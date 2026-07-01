# PDT-Lean

**The machine-verified core of Pisot Dimensional Theory.** A Lean 4 + Mathlib formalization that verifies, in the kernel, the complex-number arithmetic underlying single-qubit quantum kinematics, and checks the number-theoretic bedrock the theory rests on through Mathlib's genuine API, not hand-substituted values.

![Lean](https://img.shields.io/badge/Lean-v4.31.0-blue) ![Mathlib](https://img.shields.io/badge/Mathlib-v4.31.0-blue) ![axioms](https://img.shields.io/badge/axioms-standard%20only-green) ![sorry-free](https://img.shields.io/badge/sorry--free-brightgreen) ![native__decide-free](https://img.shields.io/badge/native__decide--free-brightgreen)

> **119 theorems · 11 modules · no `sorry`, no `native_decide`.** Every result depends only on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The one-command verifier below builds the project and prints **PASS** with the full axiom trace — or fails loudly.

---

## What PDT is

Pisot Dimensional Theory is a **parameter-free** program: it aims to derive the constants — the fine-structure constant, the gauge couplings, the fermion-mass ratios — from the arithmetic of just two polynomials,

> **x³ − x − 1**  (root ρ, the plastic number) and **x⁴ − x − 1**  (root Q),

with **zero adjustable parameters**. The full theory develops those numerical derivations and matches them to measurement. *This repository is the part a proof kernel can certify outright.*

## What this repository proves

**The complex-number kinematics, kernel-checked.** The kernel verifies the ℂ-arithmetic underlying single-qubit kinematics: the Born form `(z·z̄).re = |z|²` (the square forced by [ℂ:ℝ] = 2), positivity, the dagger as complex conjugation, Hermitian ⟹ real (the pointer basis), unitary ⟹ norm-preserving, and that two normalized amplitudes give probabilities that are |z|², non-negative, and sum to one (`QM_from_Q`). **These are theorems about ℂ.** `QisHilbert : H ≃ₗ[ℝ] ℂ` names the physical posit — that a state space *is* this complex line, Q's complex place — but the proofs establish the ℂ-facts directly and do not transport through it; the identification with physical QM (and with Q) is interpretive, not kernel-checked.

**The arithmetic bedrock, through the real Mathlib API.** Independently of any posit, the kernel verifies — via Mathlib's genuine `Algebra.norm`, `Algebra.discr`, `Algebra.traceForm` (not asserted values) — the facts the theory is built on: the **(3,1)** Lorentzian and **(2,1)** spatial trace-form signatures, the field discriminants **−23** and **−283**, the unit norm **N(ρQ) = −1**, the irreducibility of both polynomials, and the classical-vs-quantum **Bell gap** — CHSH ≤ 2 classically, Tsirelson **2√2** quantum-mechanically, saturated by an explicit real-Pauli tuple.

| File | What it proves |
|---|---|
| **PdtQm** | Single-system QM kinematics — Born rule = \|z\|², dagger = Galois conjugation, Hermitian = Galois-fixed ⟹ real (pointer basis), unitary ⟹ norm-preserving, and the capstone `QM_from_Q` (Born probabilities as \|z\|², non-negative, summing to one) — **all theorems about ℂ**. `QisHilbert : H ≃ₗ[ℝ] ℂ` is the named physical posit; the proofs do not use it. |
| **PdtNorm / PdtDiscriminant / PdtTraceForm / PdtIrreducible** | The arithmetic through the **genuine Mathlib number-theory API**, not hand-substituted identities: `Algebra.norm ℚ Q = −1`, `Algebra.norm ℚ ρ = 1`; `Algebra.discr` of the power basis = −23 / −283; the trace-form Gram matrix as `Algebra.traceForm` over `AdjoinRoot`; x³−x−1 and x⁴−x−1 proved `Irreducible` via `minpoly`. (The direct answer to *"the content is just in the names."*) |
| **PdtSignature / PdtSignatureRho** | The trace form of ℚ[x]/(x⁴−x−1) has signature **(3,1)** (spacetime), and ℚ[x]/(x³−x−1) has **(2,1)** (3-space) — each by an explicit ℚ-congruence to diagonal form plus Sylvester's law. |
| **PdtTsirelson / PdtBellClassical** | The **Tsirelson bound 2√2** (Mathlib's `tsirelson_inequality`) is **saturated** by an explicit real-Pauli `IsCHSHTuple`; the classical CHSH bound is ≤ 2; the gap `2 < 2√2` is strict. |
| **PdtGolden / PdtArithmetic** | The same bedrock re-expressed as elementary integer identities (`decide`/`norm_num`; the genuine field invariants are the API row above): disc(x³−x−1) = −23 = dim 𝔰𝔲(3)+𝔰𝔲(4); disc(x⁴−x−1) = −283; 23, 283 prime; N(2Q−1) = −23; N(ρQ) = −1; dim 𝔰𝔲(4) = 15. |

A clickable **dependency graph** (built with [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)) is published on this repo's **GitHub Pages** — every theorem green, with the lone node the kernel does not check (the identification) set apart.

## The one boundary, stated plainly

The kernel certifies the **mathematics and logic** — exactly, with nothing hidden. Two things sit deliberately *outside* it, and naming them is what makes the verified part trustworthy:

- **The physics is an identification, not a theorem.** The kernel verifies the ℂ-arithmetic; that this ℂ *is* physical quantum mechanics, and *is* Q's complex place, is the interpretive posit — **not evaluated here**. The verified facts stand on their own; the identification is named and kept outside the kernel.
- **The numerical predictions are matched separately.** The theory's high-precision results (α, the mass spectrum, the glueball mass) are checked against measurement by independent computation, not in the kernel.

That is the whole discipline: one named assumption, a hard boundary around it, and a machine confirming that everything inside depends on nothing but the standard axioms of mathematics.

## Verify it yourself

**Google Colab — one cell (most robust):** open a blank Colab notebook, paste the entire contents of [`colab_oneshot.py`](colab_oneshot.py) into a single cell, and run. Pure Python — it installs the toolchain, writes the project, builds against pinned Mathlib, and self-certifies. (Do **not** paste a `.ipynb` into a cell.) The first line it prints is a version banner; the last is **PASS** with the axiom trace, or a labelled failure.

**Colab — the notebook:** in Colab choose **File → Upload notebook**, select [`PdtQm_Colab.ipynb`](PdtQm_Colab.ipynb), then Run all (CPU is fine).

**Locally:**
```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get      # respects the pinned manifest — do NOT run `lake update`
lake build              # green = kernel-verified
```

## License & citation

Code: MIT (see [`LICENSE`](LICENSE)). Citable via the Zenodo DOI on archival (see [`.zenodo.json`](.zenodo.json)). Feedback on the formalization and on the precision of the scope statement above is exactly what this repository invites.
