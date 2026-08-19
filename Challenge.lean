import Mathlib

/-!
# Challenge: tightness of the Tsirelson bound — the classical–quantum CHSH gap

This module is the small, trusted surface to audit. Results with `sorry`
placeholders; proved versions are in `Solution.lean`.

**The story in three beats.** (1) For any CHSH tuple in an ordered star-ring,
the CHSH operator is bounded by `2√2` (Tsirelson's bound, in its familiar
form). (2) That bound is *attained*: an explicit real-Pauli quadruple in
`M₄(ℝ)` — integer matrices up to one scalar `(√2)⁻¹` — is a genuine CHSH
tuple whose CHSH operator has eigenvalue exactly `2√2` on an explicit nonzero
vector. (3) In a *commutative* ordered star-ring the same expression is
bounded by `2`, and `2 < 2√2` strictly: the gap between the classical and
quantum bounds is real, and noncommutativity is exactly what crosses it.

**Two operator-norm results.** In the l2 operator norm on `M₄(ℝ)`
(Mathlib's scoped `Matrix.Norms.L2Operator` instances), the CHSH operator of
the tuple has norm *exactly* `2√2` (`chsh_opNorm`) — the former prose
inference from the eigen-equation, now a compared statement. Yet its square
is *not* the scalar `8·1` (`chsh_sq_ne`): the operator is not `√8` times an
involution, so the naive scalar-square route `P² = 8·1 ⇒ ‖P‖ = √8` is closed
for this representation, and the norm equality must be reached another way.
-/

namespace TsirelsonTightness

open Matrix

/-- **Tsirelson's bound, `2√2` form.** Any CHSH tuple in an ordered star-ring
satisfies `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ (2√2) • 1`. -/
theorem chsh_upper
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ (2 * Real.sqrt 2) • (1 : R) := by
  sorry

/-- The scalar `(√2)⁻¹`. -/
noncomputable def s : ℝ := (Real.sqrt 2)⁻¹

/-- `A₀ = X ⊗ I` (real Pauli `X` on the first factor). -/
def A₀ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

/-- `A₁ = Z ⊗ I` (real Pauli `Z` on the first factor). -/
def A₁ : Matrix (Fin 4) (Fin 4) ℝ := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- Integer part of `B₀`: `I ⊗ (X + Z)`. -/
def B₀i : Matrix (Fin 4) (Fin 4) ℝ := !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]

/-- Integer part of `B₁`: `I ⊗ (X − Z)`. -/
def B₁i : Matrix (Fin 4) (Fin 4) ℝ := !![-1,1,0,0; 1,1,0,0; 0,0,-1,1; 0,0,1,1]

/-- `B₀ = (√2)⁻¹ • (I ⊗ (X + Z))`. -/
noncomputable def B₀ : Matrix (Fin 4) (Fin 4) ℝ := s • B₀i

/-- `B₁ = (√2)⁻¹ • (I ⊗ (X − Z))`. -/
noncomputable def B₁ : Matrix (Fin 4) (Fin 4) ℝ := s • B₁i

/-- **The real-Pauli quadruple is a genuine CHSH tuple**: each operator is a
self-adjoint involution, and the `A`s commute with the `B`s. -/
theorem tuple_isCHSH : IsCHSHTuple A₀ A₁ B₀ B₁ := by
  sorry

/-- The eigenvector witnessing saturation: `v = (1, 0, 0, 1)`. -/
def vsat : Fin 4 → ℝ := ![1, 0, 0, 1]

/-- The witness vector is nonzero. -/
theorem vsat_ne_zero : vsat ≠ 0 := by
  sorry

/-- **Saturation.** The CHSH operator of the real-Pauli tuple attains the
eigenvalue `2√2` on `vsat`:
`(A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁) · v = (2√2) • v`. -/
theorem chsh_saturates :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁).mulVec vsat
      = (2 * Real.sqrt 2) • vsat := by
  sorry

/-- **Classical CHSH bound.** In a *commutative* ordered star-ring, any CHSH
tuple satisfies `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2`. -/
theorem classical_le_two
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 := by
  sorry

/-- **The gap is strict:** `2 < 2√2`. Commuting observables stop at `2`;
the noncommutative tuple above reaches `2√2`. -/
theorem bell_gap : (2 : ℝ) < 2 * Real.sqrt 2 := by
  sorry

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- **Exact operator norm.** The CHSH operator of the real-Pauli tuple has
l2 operator norm exactly `2√2`, the Tsirelson value. -/
theorem chsh_opNorm :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 * Real.sqrt 2 := by
  sorry

/-- **Falsification:** the square of the CHSH operator is *not* the scalar
`8·1` — the naive scalar-square route to the Tsirelson norm fails for this
representation. -/
theorem chsh_sq_ne :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      ≠ (8 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  sorry

end OperatorNorm

end TsirelsonTightness
