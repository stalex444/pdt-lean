# PDT-Lean

**The machine-verified core of Pisot Dimensional Theory.** A Lean 4 + Mathlib formalization that verifies, in the kernel, the complex-number arithmetic underlying single-qubit quantum kinematics, and checks the number-theoretic bedrock the theory rests on through Mathlib's genuine API, not hand-substituted values.

![Lean](https://img.shields.io/badge/Lean-v4.31.0-blue) ![Mathlib](https://img.shields.io/badge/Mathlib-v4.31.0-blue) ![axioms](https://img.shields.io/badge/axioms-standard%20only-green) ![sorry-free](https://img.shields.io/badge/proofs-sorry--free-brightgreen) ![native__decide-free](https://img.shields.io/badge/native__decide--free-brightgreen) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21210683.svg)](https://doi.org/10.5281/zenodo.21210683)

> **498 declarations · 25 modules · no `sorry` outside the Palomar comparator's `Challenge.lean` stubs (which state 2 compared theorems, all proved in `Solution.lean`) · no `native_decide`.** A mix of substantive results, API wrappers, and disclosed elementary numeral identities — the per-module table below states what each module proves; all kernel-clean over the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). (211 use the `theorem` keyword; the remaining 287 are `lemma` helpers. Six of the 498 are `private` and so are not addressable by name from an importing file: the audit checks the other 492 directly, and those six transitively, since `#print axioms` reports the axioms of everything a result depends on.) The one-command verifier below builds the project and prints **PASS** with the full axiom trace — or fails loudly.

---

## What PDT is

Pisot Dimensional Theory is a **parameter-free** program: it aims to derive the constants — the fine-structure constant, the gauge couplings, the fermion-mass ratios — from the arithmetic of just two polynomials,

> **x³ − x − 1**  (root ρ, the plastic number) and **x⁴ − x − 1**  (root Q),

with **zero adjustable parameters**. The full theory develops those numerical derivations and matches them to measurement. *This repository is the part a proof kernel can certify outright.*

## What this repository proves

**The complex-number kinematics, kernel-checked.** The kernel verifies the ℂ-arithmetic underlying single-qubit kinematics: the Born form `(z·z̄).re = |z|²` (the square forced by [ℂ:ℝ] = 2), positivity, the dagger as complex conjugation, Hermitian ⟹ real (the pointer basis), unitary ⟹ norm-preserving, and that two normalized amplitudes give probabilities that are |z|², non-negative, and sum to one (`QM_from_Q`). **These are theorems about ℂ.** `QisHilbert : H ≃ₗ[ℝ] ℂ` names the physical posit — that a state space *is* this complex line, Q's complex place — but the proofs establish the ℂ-facts directly and do not transport through it; the identification with physical QM (and with Q) is interpretive, not kernel-checked.

**The arithmetic bedrock, through the real Mathlib API.** Independently of any posit, the kernel verifies — via Mathlib's genuine `Algebra.norm`, `Algebra.discr`, `Algebra.traceForm`/`Algebra.traceMatrix` (not asserted values) — the facts the theory is built on: the genuine field norms **N(Q) = −1** and **N(ρ) = 1** (via `Algebra.norm`); the discriminants **−23** and **−283** of the power bases of `AdjoinRoot(x³−x−1)` / `AdjoinRoot(x⁴−x−1)`, equivalently the polynomial discriminants (these are *field* discriminants once one adds prime ⇒ squarefree ⇒ maximal-order — a standard step carried in prose, not in the kernel); Sylvester congruence certificates over ℚ pinning the **(3,1)** Lorentzian and **(2,1)** spatial trace-form signatures (the base-change to ℝ and Sylvester's law of inertia is the standard final step, in prose); the irreducibility of both polynomials; and the classical-vs-quantum **Bell gap** — CHSH ≤ 2 classically, Tsirelson **2√2** quantum-mechanically, saturated by an explicit real-Pauli tuple. The compositum norm **N(ρQ) = −1** is *not* an `Algebra.norm` statement here — the compositum ℚ(ρ,Q) is unformalized; it is disclosed below as the numeral identity `1⁴·(−1)³ = −1`.

| File | What it proves |
|---|---|
| **PdtQm** | Single-system QM kinematics — Born rule = \|z\|², dagger = Galois conjugation, Hermitian = Galois-fixed ⟹ real (pointer basis), unitary ⟹ norm-preserving, and the capstone `QM_from_Q` (Born probabilities as \|z\|², non-negative, summing to one) — **all theorems about ℂ**. `QisHilbert : H ≃ₗ[ℝ] ℂ` is the named physical posit; the proofs do not use it. |
| **PdtNorm / PdtDiscriminant / PdtTraceForm / PdtIrreducible** | The arithmetic through the **genuine Mathlib number-theory API**, not hand-substituted identities: `Algebra.norm ℚ Q = −1`, `Algebra.norm ℚ ρ = 1`; `Algebra.discr` of the power basis = −23 / −283; the trace-form Gram matrix as `Algebra.traceForm` over `AdjoinRoot`; x³−x−1 and x⁴−x−1 proved `Irreducible` over ℚ by **reduction mod 2** (Gauss's lemma lift). (The direct answer to *"the content is just in the names."*) |
| **PdtSignature / PdtSignatureRho** | For ℚ[x]/(x⁴−x−1) the kernel checks a **Sylvester congruence certificate over ℚ**: PᵀMP = diag(4,4,−9/4,283/36) with P unimodular and det M = −283. Base-change to ℝ and the sign-count (Sylvester's law of inertia) — a standard step, in prose — give signature **(3,1)** (spacetime); likewise **(2,1)** (3-space) for the cubic. The hand-written matrices are linked to the genuine `Algebra.traceForm` / `Algebra.traceMatrix` Gram matrices in `PdtLinks` (`M_eq_M4`, `Mρ_eq_traceMatrix_fin3`). |
| **PdtLinks** | The **cross-module identification lemmas**, which dissolve the import islands. Each `Pdt*.lean` re-declares "the same" polynomial or matrix as a private duplicate, linked to its twins only by matching literals; this module imports them and proves the identities — `fq_eq_fQ`, `fc_eq_fρ`, `f4_eq_fQ`, `M_eq_M4`, `M_entry_eq_traceForm`, `Mρ_eq_traceMatrix_fin3` — so that "the same object" is a **proved statement rather than an observation about matching source text**, and the `(3,1)` / `(2,1)` certificates are certificates about the genuine `Algebra.traceForm` / `Algebra.traceMatrix` Gram matrices. Disclosed plainly: every lemma here is `rfl`-level (the duplicated bodies are syntactically identical) or an application of an existing genuine-API theorem. Also re-anchors the `Fact (Irreducible ·)` instances so `AdjoinRoot fQ` / `AdjoinRoot fρ` resolve as genuine fields. |
| **PdtSymplectic** | The complex place, two forms and one rotation: the **dagger identity** `G_Born = G_trace ∘ σ` (the Born form is the trace form precomposed with conjugation); the same `J` = mult-by-`i` is a Born **isometry** (the unitary phase) and a trace **anti-isometry** (the Lorentzian time-rotation); and the companion form `ω = Jᵀ G_Born = Im(z̄w)` is **alternating and nondegenerate** — a symplectic form — while the trace companion is symmetric. The linear-algebra core of the *Fault-Line-A* / Proposition 1 result: `g(J·,·)` is alternating iff `g` is `J`-invariant, and it is the Born metric (not the trace form) that is `J`-invariant. |
| **PdtStabilizer** | Anchored-stabilizer dimension identities at **general N** (pure linear algebra; no physics claims): X ↦ Xv from trace-zero matrices is **surjective** for v ≠ 0 (explicit solver); the sl-stabilizer of v has finrank **N²−N−1**; the gl-stabilizer has N²−N, the **corank-1** gap exhibited by an explicit trace-1 witness (the trace character); finrank sl(N) = N + (N²−N−1) (orbit ⊕ stabilizer); instances 11 (N=4), 19 (N=5), 209 (N=15). |
| **PdtTsirelson / PdtBellClassical** | The **Tsirelson bound 2√2** (Mathlib's `tsirelson_inequality`) is **saturated** by an explicit real-Pauli `IsCHSHTuple`; the classical CHSH bound is ≤ 2; the gap `2 < 2√2` is strict. |
| **PdtTsirelsonNorm / PdtTsirelsonExact** | The **exact CHSH constants**: the saturating tuple's l2 operator norm is **exactly 2√2** via the C\*-identity (and its square is provably *not* `c·1` for **any** real `c` — the textbook shortcut is false for every scalar); the **Landau identity** `T² = 4 + [A₀,A₁][B₁,B₀]` in any \*-ring; `‖T‖ ≤ 2√2` in every nontrivial unital real C\*-normed algebra; a commuting party forces `‖T‖ = 2` **exactly**; any violation `‖T‖ > 2` forces noncommutativity in **both** parties; and `2√2` is the **greatest** CHSH operator norm over `M₄(ℝ)` (`IsGreatest`, attained). |
| **PdtPisotBoundary** | The **settle/spiral dichotomy**, kernel-checked from the polynomials alone: every non-real root of x³−x−1 has modulus **< 1** (ρ is Pisot — settles) and every non-real root of x⁴−x−1 has modulus **> 1** (Q is non-Pisot — spirals), by a single Vieta reduction on the conjugate pair — no root-finding, no polynomial API; packaged as `pisot_boundary_dichotomy`. Upgrades the computed moduli 0.869 / 1.063 to a theorem. |
| **PdtClock** | The β-clock's tick word m(n) = ⌊(n+1)β⌋ − ⌊nβ⌋ is **two-valued** (for 0 < β < 1), of **density exactly β** (exact telescoping to ⌊Nβ⌋), **aperiodic** (for irrational β, carried as an explicit hypothesis), and **balanced** — any two equal-length windows differ by at most one tick. Aperiodic but not random, kernel-checked. |
| **PdtCommitment** | The two archimedean places of ℚ(ρ) and the image σ₂(ℤ[ρ]) ⊆ ℂ of the order ℤ[ρ]. Three groups: (i) the **exact contraction rate** r·\|z\|² = 1, equivalently \|z\| = r^(−1/2) (`tick_contraction`, `norm_z_eq_rpow`) — the norm relation N(ρ) = 1 read at the two places, an identity of the field rather than a numerical estimate; (ii) the **integrality floor** 1 ≤ \|σ₁(x)\|·\|σ₂(x)\|² for every nonzero x ∈ ℤ[ρ], hence \|σ₂(x)\| ≥ \|σ₁(x)\|^(−1/2) (`meyer_separation`, `meyer_separation_rpow`), proved from the norm form of a nonzero element being a nonzero rational integer; (iii) **windowed permanence** — multiplication by z permutes σ₂(ℤ[ρ]) (ρ is a unit); two lattice points whose real embeddings differ by at most H are at least H^(−1/2) apart; and a point within (1/2)·H^(−1/2) of σ₂(ℓ) remains, after any number of multiplications by z, strictly nearest to the image of ℓ among all lattice points in the window (`certification_soundness`). The window hypothesis is explicit and essential — the unwindowed image is dense. Reading these as a dynamics with recorded outcomes is an **identification**, marked as such in the file and not kernel-checked. |
| **PdtGolden / PdtArithmetic** | The same bedrock re-expressed as elementary integer identities (`decide`/`norm_num`; the genuine field invariants are the API row above): disc(x³−x−1) = −23 = dim 𝔰𝔲(3)+𝔰𝔲(4); disc(x⁴−x−1) = −283; 23, 283 prime; N(2Q−1) = −23; the norm-tower product N(ρQ) = N(ρ)⁴·N(Q)³ = 1⁴·(−1)³ = −1, an elementary numeral identity (the compositum ℚ(ρ,Q) is not formalized); dim 𝔰𝔲(4) = 15. |
| **PdtMahler / PdtMahlerBox / PdtMahlerMain / PdtMahlerTheta / PdtMahlerWindow** | The **Mahler degree window**: for d ∈ {2, 3, 4}, `x^d − x − 1` attains the **minimal Mahler measure** among monic irreducible integer polynomials of degree d with measure above one, and the minima are pinned exactly — M² = M+1 (φ), M³ = M+1 (ρ), M⁴ = M³+1 (θ₄). Graeffe-certificate architecture: Mathlib's coefficient bound cuts each degree to a finite box; all 6,339 certificates (21 / 147 / 6,171) kernel-decided with plain `decide`. Attainment is theorem-backed (the minimizers' irreducibility is on the compared surface); Siegel 1944 (smallest / second-smallest Pisot) is cited, not formalized. |
| **PdtBusch** | **Busch's theorem** (2003), finite dimension: every generalized probability measure on quantum effects — nonnegative, additive where the sum stays an effect, normalized — is trace against a **unique** density matrix (existence **and** uniqueness, `busch`). No continuity assumed anywhere: additivity plus nonnegativity force real homogeneity on the effect interval (the monotone squeeze), then spectral scale/shift extension and an entrywise density-matrix assembly. Valid already at dimension 2, where Gleason's theorem (cited, not formalized) does not apply. Effects in Mathlib vocabulary (`Matrix.PosSemidef`). |

A clickable **dependency graph** (built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)) is published on this repo's **GitHub Pages** — the headline statements green, with the lone node the kernel does not check (the identification) set apart.

## The Mahler degree window (PdtMahler*)

For d ∈ {2, 3, 4}, `x^d − x − 1` attains the minimal Mahler measure among
monic irreducible integer polynomials of degree d with measure above one
(`quadratic_mahler_min'`, `cubic_mahler_min'`, `quartic_mahler_min'`) —
attainment is theorem-backed: the minimizers' irreducibility
(`fam2/3/4_irreducible`) and measure above one are on the compared
surface. The three minima are pinned exactly (`mahler_quadratic_phi`,
`mahler_cubic_rho`, `mahler_fam_pisot`): M² = M + 1 at degree 2 (the
golden ratio), M³ = M + 1 at degree 3 (the plastic ratio), and
M⁴ = M³ + 1 at degree 4 (the root of x⁴ − x³ − 1 above one). By Siegel's
classical theorem (1944 — cited, not formalized here) the latter two are
the smallest and second-smallest Pisot numbers; the literature's symbol
for the second is θ₁ (Dufresnoy–Pisot), written θ₄ in this repository
for "the degree-4 floor". The degree-4 twist: classically x⁴ − x − 1 is
not itself a Pisot polynomial (three roots outside the unit circle;
kernel-backed here by `PDT.quartic_conj_norm_gt_one`, outside the
compared surface), yet its measure lands back on the Pisot list.

Method: a Graeffe-certificate architecture. The Mathlib coefficient bound
`norm_coeff_le_choose_mul_mahlerMeasure` cuts each problem to a finite
coefficient box at a per-degree rational threshold (81/50, 133/100,
139/100) inside a kernel-bracketed spectral gap; every box element then
carries one integer certificate — tie orbit, cyclotomic cofactor of
Xⁿ − 1, explicit factorization, or an iterated Graeffe coefficient bound
(sound by M(Graeffe q) = M(q)², proved via the root-squares product
identity). All 6,339 certificates (21 + 147 + 6,171) are kernel-decided
with plain `decide`; no `native_decide` anywhere. The exact constants
come from a root-inversion identity (reversal invariance at unit constant
term) plus a (σ, s)-reduction in the style of `PdtPisotBoundary`
localizing the conjugate pairs, with root multiplicity excluded by
kernel-certified measure brackets rather than discriminants.

## Busch's theorem (PdtBusch)

Kernel-checked Busch (2003), finite dimension: every generalized
probability measure on quantum effects is trace against a unique density
matrix (`busch_representation`: existence and uniqueness). Effects are
PSD matrices below the identity, spelled via `Matrix.PosSemidef`; no
continuity is assumed anywhere, since nonnegativity plus additivity
already force real homogeneity on the effect interval — scalars in
[0,1] (`homogeneity_automatic`, compared separately). This is Born-rule
uniqueness in the POVM reading, valid already at dimension 2, where
Gleason's theorem (which requires dimension at least 3) does not apply;
Gleason's theorem itself is not formalized here. The
infinite-dimensional sigma-additive statement is out of scope for this
entry and stated so.

Method: the frame function is bootstrapped from additivity to rational
and then real homogeneity by a monotone squeeze; extended canonically to
all PSD matrices by spectral scaling into the effect interval (conjugation
by the eigenvector unitary), then to all Hermitian matrices by shifting;
the density matrix is assembled entry by entry from the extension on a
Hermitian matrix-unit basis, and uniqueness is read off entrywise through
the same basis. Axioms: propext, Classical.choice, Quot.sound.

## The one boundary, stated plainly

The kernel certifies the **mathematics and logic** — exactly, with nothing hidden. Two things sit deliberately *outside* it, and naming them is what makes the verified part trustworthy:

- **The physics is an identification, not a theorem.** The kernel verifies the ℂ-arithmetic; that this ℂ *is* physical quantum mechanics, and *is* Q's complex place, is the interpretive posit — **not evaluated here**. The verified facts stand on their own; the identification is named and kept outside the kernel.
- **The numerical predictions are matched separately.** The theory's high-precision results (α, the mass spectrum, the glueball mass) are checked against measurement by independent computation, not in the kernel.

That is the whole discipline: one named assumption, a hard boundary around it, and a machine confirming that everything inside depends on nothing but the standard axioms of mathematics.

## Verify it yourself

**Google Colab — one cell:** open a blank Colab notebook, paste the entire contents of [`colab_oneshot.py`](colab_oneshot.py) into a single cell, and run. Pure Python — it installs the toolchain, writes the project, builds against pinned Mathlib, and self-certifies. (Do **not** paste a `.ipynb` into a cell.) The first line it prints is a version banner; the last is **PASS** with the axiom trace, or a labelled failure.

**Colab — the notebook:** in Colab choose **File → Upload notebook**, select [`PdtQm_Colab.ipynb`](PdtQm_Colab.ipynb), then Run all (CPU is fine).

**Locally:**
```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get      # respects the pinned manifest — do NOT run `lake update`
lake build              # green = kernel-verified
```

## License & citation

Code: MIT (see [`LICENSE`](LICENSE)).

**Citation (all versions):** Stephanie Alexander ([ORCID 0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)), *PDT-Lean: a kernel-verified Lean 4 formalization of the Pisot Dimensional Theory core*, Zenodo, DOI [10.5281/zenodo.21210683](https://doi.org/10.5281/zenodo.21210683) (concept DOI — always resolves to the latest release).

Feedback on the formalization and on the precision of the scope statement above is exactly what this repository invites.

## Palomar registry record

Machine-verified entries by this project, registered at the
[Palomar registry](https://palomar-registry.org) (mechanical
kernel verification plus independent editorial review; each ID links a
pinned commit):

| ID | Entry | Content |
|---|---|---|
| PALOMAR-2026-08-19-000006 | [arithmetic-of-time](https://github.com/stalex444/arithmetic-of-time) | the arrow of time as a theorem: the settled history, read backwards, is provably a different object |
| PALOMAR-2026-08-19-000007 | [pdt-lean](https://github.com/stalex444/pdt-lean) | the quantum-kinematics core: Tsirelson bound and the single-system formalism's arithmetic layer |
| PALOMAR-2026-08-31-000004 | [mahler-measure-minima](https://github.com/stalex444/mahler-measure-minima) | x^d − x − 1 attains the minimal Mahler measure (monic irreducible) at d = 2, 3, 4, minima pinned exactly |
| PALOMAR-2026-08-31-000014 | [Busch-theorem](https://github.com/stalex444/Busch-theorem) | Busch's theorem (the generalized Gleason theorem for effects), first formalization in any prover |
| PALOMAR-2026-09-01-000003 | [werner-window](https://github.com/stalex444/werner-window) | both edges of the Werner window exact: separable to p = 1/3, CHSH-violating above p = 1/√2; general bounds at arbitrary dimensions and settings |
| PALOMAR-2026-09-01-000005 | [mahler-minimizer-compositum](https://github.com/stalex444/mahler-minimizer-compositum) | the compositum of the two Mahler minimizers: exact measure ρ²Q²ψ, full conjugate census, order-12 recurrence with annihilator ideal exact |
| PALOMAR-2026-09-01-000008 | [only-two-morphic-numbers](https://github.com/stalex444/only-two-morphic-numbers) | the Aarts–Fokkink–Kruijtzer classification: the golden ratio and the plastic number are the only morphic numbers |
