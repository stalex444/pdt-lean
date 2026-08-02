# ============================================================
# PDT — Lean 4 kernel verification, ONE-CELL version.
# Paste this ENTIRE cell into a blank Google Colab cell and run it.
# (Pure Python — do NOT paste a .ipynb file; this IS the runnable code.)
# Runtime: CPU is fine (no GPU). ~a few minutes for the Mathlib cache.
#
# This clones the PUBLISHED repository (no embedded source mirror to drift),
# builds it, and self-certifies via `#print axioms` that EVERY theorem/lemma
# depends only on Lean's standard axioms {propext, Classical.choice,
# Quot.sound} — i.e. no `sorry`, no `native_decide`, no custom axioms.
# Set PDT_REF (below) to a release tag such as "v1.0" to pin an archived
# release instead of the latest main.
# ============================================================
import os, subprocess, sys, re
print("=" * 64, flush=True)
print("PDT-Lean verifier  ·  clone + build + full #print axioms audit", flush=True)
print("If you do NOT see this banner as the first output, you pasted an old copy.", flush=True)
print("=" * 64, flush=True)

REPO  = "https://github.com/stalex444/pdt-lean.git"
REF   = os.environ.get("PDT_REF", "main")           # e.g. "v1.0" to pin a release
LOCAL = os.environ.get("PDT_LOCAL")                 # audit an existing checkout in place (CI)
STD   = {"propext", "Classical.choice", "Quot.sound"}

def sh(c, check=True, capture=False, **k):
    # Stream the command; stop LOUDLY on a nonzero exit instead of marching on.
    print("$", c, flush=True)
    r = subprocess.run(c, shell=True, text=True,
                       capture_output=capture, **k)
    if capture and r.stdout:
        print(r.stdout[-4000:], flush=True)
    if check and r.returncode != 0:
        if capture and r.stderr:
            print(r.stderr[-4000:], flush=True)
        print("\n" + "=" * 60, flush=True)
        print("!!! STAGE FAILED (exit %d): %s" % (r.returncode, c), flush=True)
        print("!!! Copy the ~15 lines above and send them for diagnosis.", flush=True)
        print("=" * 60, flush=True)
        raise SystemExit(r.returncode)
    return r

HOME = os.path.expanduser("~")
if LOCAL:
    # CI path. The workflow has already installed the toolchain and run `lake build`,
    # so stages 1-3 are skipped and this checkout is audited in place. CI therefore
    # exercises the SAME enumerator and the SAME audit a reader runs in Colab — there
    # is no second copy of the logic to drift out of sync.
    DIR = os.path.abspath(LOCAL)
    print(f"PDT_LOCAL set — auditing the existing checkout at {DIR}", flush=True)
    os.chdir(DIR)
else:
    # 1) toolchain
    sh("curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh")
    sh("sh /tmp/elan-init.sh --default-toolchain v4.31.0 -y")
    os.environ["PATH"] = HOME + "/.elan/bin:" + os.environ["PATH"]
    sh("lake --version", check=False)

    # 2) clone the authoritative published repo (no embedded mirror)
    WORK = "/content" if os.path.isdir("/content") else os.getcwd()
    DIR  = os.path.join(WORK, "pdt-lean")
    sh(f"rm -rf {DIR}")
    clone = f"git clone --depth 1 {REPO} {DIR}" if REF == "main" \
            else f"git clone --depth 1 --branch {REF} {REPO} {DIR}"
    sh(clone)
    os.chdir(DIR)

    # 3) build against the pinned Mathlib (prebuilt cache first)
    sh("lake exe cache get")
    sh("lake build")

# 4) enumerate every theorem/lemma and generate the axiom-audit driver
#    Lean identifiers are Unicode (norm_ρ, A₀_sq, detMρ), and a declaration may carry
#    attributes (@[simp] lemma) or modifiers (private lemma), so the pattern has to allow
#    all three. `private` declarations are skipped: they are not addressable by name from
#    an importing file. Skipping them costs nothing, because #print axioms is transitive —
#    a public result reports the axioms of everything it depends on, private helpers included.
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<mods>(?:(?:private|protected|nonrec|noncomputable|partial|unsafe)[ \t]+)*)"
    r"(?:theorem|lemma)[ \t]+([^\s:({\[⦃⟨]+)", re.M)
#    LOOSE is an independent cross-check on DECL itself. DECL whitelists a fixed set of
#    modifiers; LOOSE accepts ANY leading words, so a modifier that is not on that list
#    surfaces as a count mismatch instead of a silently omitted declaration. Comments and
#    docstrings are stripped first, because the prose in this repo uses the words
#    "theorem" and "lemma" freely. This is the guard for omission; the coverage check in
#    stage 5 is the guard for a name that is enumerated but does not resolve.
LOOSE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:[A-Za-z_]\w*[ \t]+)*?"
    r"(?:theorem|lemma)[ \t]+\S", re.M)

def strip_comments(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))

names, imports, skipped, loose_total = [], set(), [], 0
for fn in sorted(os.listdir(DIR)):
    if fn.startswith("Pdt") and fn.endswith(".lean"):
        txt = open(os.path.join(DIR, fn), encoding="utf-8").read()
        ns  = re.search(r"namespace\s+([^\s({\[]+)", txt)
        pre = (ns.group(1) + ".") if ns else ""
        imports.add(fn[:-5])
        for m in DECL.finditer(txt):
            if "private" in m.group("mods"):
                skipped.append(pre + m.group(2))
                continue
            names.append(pre + m.group(2))
        loose_total += len(LOOSE.findall(strip_comments(txt)))

if loose_total != len(names) + len(skipped):
    print("=" * 64, flush=True)
    print(f"FAIL — enumerator disagreement: the audit pattern found "
          f"{len(names) + len(skipped)} declarations, the independent scan found "
          f"{loose_total}.", flush=True)
    print("       Some declaration form is not being enumerated. The audit would be "
          "incomplete, so it is not run.", flush=True)
    raise SystemExit(1)

driver = "".join(f"import {m}\n" for m in sorted(imports)) \
       + "".join(f"#print axioms {n}\n" for n in names)
open("CheckAll.lean", "w", encoding="utf-8").write(driver)
print(f"\nChecking {len(names)} declarations across {len(imports)} modules "
      f"({len(names) + len(skipped)} total; {len(skipped)} private, covered transitively) ...",
      flush=True)

# 5) run the audit; every axiom set must be a subset of the standard three
res = sh("lake env lean CheckAll.lean", capture=True)
os.remove("CheckAll.lean")
bad, seen = [], set()
for line in (res.stdout or "").splitlines():
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen.add(m.group(1))
        ax = {a.strip() for a in m.group(2).split(",") if a.strip()}
        if not ax <= STD:            # sorryAx / native_decide / custom land here
            bad.append((m.group(1), sorted(ax - STD)))
    m = re.search(r"'([^']+)' does not depend on any axioms", line)
    if m:
        seen.add(m.group(1))

# Coverage guard: every name we asked about must come back with a verdict. Without this,
# an enumerator defect silently shrinks the audit instead of failing it.
unresolved = [n for n in names if n not in seen]

print("=" * 64, flush=True)
if unresolved:
    print(f"FAIL — {len(unresolved)} of {len(names)} declarations returned no verdict:", flush=True)
    for n in unresolved[:20]:
        print(f"   {n}", flush=True)
    if len(unresolved) > 20:
        print(f"   ... and {len(unresolved) - 20} more", flush=True)
    print("   (enumerator/driver defect — the audit is incomplete, not passing)", flush=True)
    raise SystemExit(1)
if bad:
    print("FAIL — non-standard axioms found:", flush=True)
    for n, extra in bad:
        print(f"   {n}: {extra}", flush=True)
    raise SystemExit(1)
print(f"PASS — all {len(names)} declarations depend only on {sorted(STD)};", flush=True)
print("       no sorry, no native_decide, no custom axioms.", flush=True)
print("=" * 64, flush=True)
