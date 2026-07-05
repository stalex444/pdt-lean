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

REPO = "https://github.com/stalex444/pdt-lean.git"
REF  = os.environ.get("PDT_REF", "main")            # e.g. "v1.0" to pin a release
STD  = {"propext", "Classical.choice", "Quot.sound"}

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
names, imports = [], set()
for fn in sorted(os.listdir(DIR)):
    if fn.startswith("Pdt") and fn.endswith(".lean"):
        txt = open(os.path.join(DIR, fn), encoding="utf-8").read()
        ns  = re.search(r"namespace\s+([A-Za-z0-9_.]+)", txt)
        pre = (ns.group(1) + ".") if ns else ""
        imports.add(fn[:-5])
        for m in re.finditer(r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)", txt, re.M):
            names.append(pre + m.group(1))
driver = "".join(f"import {m}\n" for m in sorted(imports)) \
       + "".join(f"#print axioms {n}\n" for n in names)
open("CheckAll.lean", "w", encoding="utf-8").write(driver)
print(f"\nChecking {len(names)} declarations across {len(imports)} modules ...", flush=True)

# 5) run the audit; every axiom set must be a subset of the standard three
res = sh("lake env lean CheckAll.lean", capture=True)
os.remove("CheckAll.lean")
bad = []
for line in (res.stdout or "").splitlines():
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        ax = {a.strip() for a in m.group(2).split(",") if a.strip()}
        if not ax <= STD:            # sorryAx / native_decide / custom land here
            bad.append((m.group(1), sorted(ax - STD)))

print("=" * 64, flush=True)
if bad:
    print("FAIL — non-standard axioms found:", flush=True)
    for n, extra in bad:
        print(f"   {n}: {extra}", flush=True)
    raise SystemExit(1)
print(f"PASS — all {len(names)} declarations depend only on {sorted(STD)};", flush=True)
print("       no sorry, no native_decide, no custom axioms.", flush=True)
print("=" * 64, flush=True)
