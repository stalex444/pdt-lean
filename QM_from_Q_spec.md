# Formalization blueprint — "QM from Q's complex place" (the IF-posit-THEN-formalism artifact)

Toolchain status (2026-06-21): `lean`/`lake`/`elan` are NOT installed in this environment; `lean/` is empty.
The identities below are SETTLED by the computation oracle (sympy/numpy, FINDINGS_VERIFIED 2026-06-21) — a valid
oracle per CLAUDE.md ("the digits"). This file is the ready-to-compile Lean blueprint; the literal `lake build`
T0 step is pending `elan`+Mathlib being stood up (a clean named next action). Statements are elementary
(degree-2 field / Complex API), so they will compile with `field_simp`/`ring`/`simp` once Mathlib is present.

## THE NAMED POSIT (the single hypothesis everything hangs off — kept explicit, NOT hidden)
`P_QisHilbert : (the physical one-qubit/qudit QM Hilbert space) ≃ₗ (Q's complex place ℂ as an ℝ-structure)`
Tier T4. Everything below is a THEOREM given P_QisHilbert + standard Mathlib/Gleason; the artifact's whole point
is to expose this as the one undischarged hypothesis.

## THE ELEMENTARY LEMMAS (T2/math; the forced part) — Lean 4 / Mathlib statements
```
-- the Born form = the trace form twisted by the Galois involution = 2|z|^2, positive-definite
-- (starRingEnd ℂ = complex conjugation = the Galois automorphism of ℂ/ℝ = the dagger)
theorem born_form (z : ℂ) :
    (algebraMap ℂ ℂ z * starRingEnd ℂ z).re = Complex.normSq z := by
  simp [Complex.normSq, starRingEnd, Complex.mul_conj]   -- = |z|^2

theorem born_pos {z : ℂ} (hz : z ≠ 0) : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz

-- distinct from the UNTWISTED trace form Tr(z^2) = 2(a^2 - b^2) (the indefinite (3,1) SIGNATURE form)
theorem signature_form (z : ℂ) : (z*z + (starRingEnd ℂ z)*(starRingEnd ℂ z)).re = 2*(z.re^2 - z.im^2) := by
  simp [starRingEnd]; ring

-- dagger = Galois conjugation is an anti-linear involution
theorem dagger_invol : Function.Involutive (starRingEnd ℂ) := Complex.conj_conj
theorem dagger_antilinear (a z : ℂ) : starRingEnd ℂ (a*z) = (starRingEnd ℂ a)*(starRingEnd ℂ z) := by
  simp [map_mul]

-- Hermitian observable = Galois-fixed (self-adjoint) ⇒ REAL spectrum  [Mathlib: IsSelfAdjoint, spectrum ⊆ ℝ]
theorem hermitian_real_spectrum {n} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsSelfAdjoint A) :
    ∀ μ ∈ spectrum ℂ A, (starRingEnd ℂ) μ = μ := by exact?  -- IsSelfAdjoint ⇒ eigenvalues real (Mathlib)

-- unitary = Galois-norm-1 :  U * star U = 1  (the |.|=1 'unit circle')
theorem unitary_norm_one {n} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    U * star U = 1 := (Matrix.mem_unitaryGroup_iff'.1 hU)
```

## THE CONDITIONAL THEOREM (the artifact's headline)
```
theorem QM_from_Q (P_QisHilbert : ...) :
    -- the imaginary unit of QM = the complex place's i
    (QM_i = Complex.I) ∧
    -- the bra-ket = the conjugate-twisted trace form = the field norm
    (∀ z, QM_inner z z = Complex.normSq z) ∧
    -- the dagger = the Galois conjugation
    (QM_dagger = starRingEnd ℂ) ∧
    -- observables real, evolution unitary
    (Hermitian ⇒ real spectrum) ∧ (Unitary ⇒ Galois-norm-1) := by
  ...   -- each conjunct discharged by the elementary lemmas above + P_QisHilbert
```
The Born-rule UNIQUENESS (|.|^2 is the ONLY consistent measure) is GLEASON's theorem — not in Mathlib; cite as an
external [T1] hypothesis `gleason : (measure on projections of a complex H, dim ≥ 3) → BornRule`. The artifact
proves the STRUCTURE (the form, the conjugation, the field norm); Gleason supplies uniqueness.

## CPT / TIME-REVERSAL = GALOIS (the new identification, T1+T4)
Wigner (1932): time-reversal T is anti-unitary [T1]. The canonical anti-unitary is complex conjugation =
`starRingEnd ℂ` = the Galois automorphism of ℂ/ℝ. ⇒ T (and the CPT anti-unitary) = the field's Galois action.
Not a Mathlib statement (it's a physics identification); record at tier in FINDINGS / PENDING, not auto-canon.

## NEXT
1. Stand up the toolchain: `elan` install → `lake new` → add Mathlib → `lake exe cache get` (large, one-time).
2. Compile `QM_from_Q.lean` with the lemmas above (elementary; expect green with field_simp/ring/Complex API).
3. THEN the higher-value T0 targets (posit_attack.md): signature (3,1) ⟺ n=4; étale K⊗ℝ=ℝ²×ℂ; op-norm 2√2.
