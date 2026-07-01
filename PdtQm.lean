/-
PDT — the complex-number arithmetic behind single-qubit quantum kinematics.

Every theorem below is a fact about ℂ, kernel-checked by `lake build`: the Born form
`|z|²`, positivity, the dagger = complex conjugation = `starRingEnd ℂ`, Hermitian ⟹ real,
and unitary ⟹ norm-preserving.

THE NAMED POSIT (T4, kept explicit): `QisHilbert H` says a physical state space is
ℝ-linearly the complex place of Q's field (≃ₗ[ℝ] ℂ). The theorems below are about ℂ
directly and do NOT use this equivalence — the posit is stated, not yet load-bearing —
and the identification with physical QM and with Q's complex place is interpretive, not
kernel-checked. The oracle is the Lean kernel: a green build is the verification.
-/
import Mathlib

namespace PDT
open Complex

/-- THE NAMED POSIT (T4) — the one hypothesis everything hangs off, kept explicit.
    A physical one-qubit state space `H` is ℝ-linearly equivalent to Q's complex place ℂ. -/
abbrev QisHilbert (H : Type*) [AddCommGroup H] [Module ℝ H] : Type _ := H ≃ₗ[ℝ] ℂ

/-- Born form = the conjugate-twisted trace form = |z|². The SQUARE is forced by [ℂ:ℝ]=2. -/
theorem born_form (z : ℂ) : (z * (starRingEnd ℂ) z).re = normSq z := by
  rw [Complex.mul_conj]; simp

/-- Born positivity: |z|² ≥ 0 always, and > 0 for a nonzero amplitude (a genuine probability). -/
theorem born_nonneg (z : ℂ) : 0 ≤ normSq z := normSq_nonneg z
theorem born_pos {z : ℂ} (hz : z ≠ 0) : 0 < normSq z := normSq_pos.mpr hz

/-- The UNTWISTED trace form Tr(z²)+Tr(z̄²) = 2(a²−b²): the INDEFINITE (3,1)-signature
    form, provably DISTINCT from the positive-definite Born form above. -/
theorem signature_form (z : ℂ) :
    (z * z + (starRingEnd ℂ) z * (starRingEnd ℂ) z).re = 2 * (z.re ^ 2 - z.im ^ 2) := by
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- dagger = Galois conjugation is an involution (F² = +1). -/
theorem dagger_invol : Function.Involutive (starRingEnd ℂ) := Complex.conj_conj

/-- dagger is multiplicative (a ring hom): (a·z)† = a†·z†. -/
theorem dagger_mul (a z : ℂ) :
    (starRingEnd ℂ) (a * z) = (starRingEnd ℂ) a * (starRingEnd ℂ) z := map_mul _ a z

/-- Hermitian = Galois-FIXED ⇒ real. Observables (the Galois-fixed elements) have real
    values — this is the pointer basis. -/
theorem hermitian_real {z : ℂ} (h : (starRingEnd ℂ) z = z) : z.im = 0 := by
  have h2 : -z.im = z.im := by rw [← Complex.conj_im]; exact congrArg Complex.im h
  linarith

/-- Unitary scalar (z·z† = 1) ⇒ |z|² = 1: evolution preserves the Born norm. -/
theorem unitary_normSq_one {z : ℂ} (h : z * (starRingEnd ℂ) z = 1) : normSq z = 1 := by
  have h2 := congrArg Complex.re h
  rw [Complex.mul_conj] at h2
  simpa using h2

/-- THE CAPSTONE: for normalized two-outcome amplitudes `a b : ℂ`, the Born probabilities
    are `|z|²` (the conjugate-twisted trace form), nonnegative, and sum to one — a genuine
    probability rule assembling `born_form`/`normSq_nonneg`, with NO independent Born
    postulate. A theorem about ℂ; `QisHilbert` is not used. -/
theorem QM_from_Q {a b : ℂ} (hnorm : normSq a + normSq b = 1) :
    (a * (starRingEnd ℂ) a).re = normSq a ∧
    (b * (starRingEnd ℂ) b).re = normSq b ∧
    0 ≤ normSq a ∧ 0 ≤ normSq b ∧
    normSq a + normSq b = 1 :=
  ⟨born_form a, born_form b, normSq_nonneg a, normSq_nonneg b, hnorm⟩

/-- `born_nonneg` for `P ψ`, where `P : QisHilbert H`. NOTE: this uses only that `P ψ : ℂ`
    (via `normSq_nonneg`); the ℝ-linear-equivalence STRUCTURE of `P` is never used, so this
    does NOT make the posit load-bearing — the theorems above are about ℂ directly. Making
    the posit genuinely do work is future formalization, not yet done. -/
theorem born_nonneg_physical {H : Type*} [AddCommGroup H] [Module ℝ H]
    (P : QisHilbert H) (ψ : H) : 0 ≤ normSq (P ψ) := normSq_nonneg _

end PDT
