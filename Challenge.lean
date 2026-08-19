import Mathlib

/-!
# Challenge: the exact CHSH constants — necessity, attainment, and the supremum over M₄(ℝ)

This module is the small, trusted surface to audit. Results with `sorry`
placeholders; proved versions are in `Solution.lean`.

**The suite.** For a CHSH tuple (Mathlib's `IsCHSHTuple`: self-adjoint
involutions `A₀, A₁, B₀, B₁` with the `A`s commuting with the `B`s), write
`T = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁`.

1. **The Landau identity** (`chsh_mul_self`): in any \*-ring,
   `T² = 4 + [A₀,A₁]·[B₁,B₀]` — the exact, representation-independent
   correction to the naive `T² = 8·1`.
2. **Tsirelson's bound in norm form** (`chsh_norm_le`): in every nontrivial
   unital real C\*-normed algebra, `‖T‖ ≤ 2√2`.
3. **The classical constant, exactly** (`chsh_norm_of_comm`): if either
   party's pair commutes, `‖T‖ = 2` exactly — not merely `≤ 2`.
4. **Necessity of noncommutativity** (`noncomm_of_chsh_norm_gt_two`): any
   violation `‖T‖ > 2` forces `A₀A₁ ≠ A₁A₀` *and* `B₀B₁ ≠ B₁B₀`.
5. **The exact constant of `M₄(ℝ)`** (`chsh_opNorm_isGreatest`): in the l2
   operator norm, `2√2` is the *greatest* element of the set of CHSH operator
   norms over 4×4 real matrices — an upper bound for every tuple, attained.

Points 4 and 5 are the necessity/possibility pair: noncommutativity within
both parties is *necessary* for any violation of the classical bound, and the
explicit real-Pauli tuple below shows the maximal violation `2√2` is
*possible* (attained).

**The original three beats** remain compared. (1) `chsh_upper`: for any CHSH
tuple in an ordered star-ring, `T ≤ (2√2) • 1`. (2) Attainment: an explicit
real-Pauli quadruple in `M₄(ℝ)` — integer matrices up to one scalar `(√2)⁻¹`
— is a genuine CHSH tuple (`tuple_isCHSH`) whose CHSH operator has eigenvalue
exactly `2√2` on an explicit nonzero vector (`chsh_saturates`,
`vsat_ne_zero`), and l2 operator norm exactly `2√2` (`chsh_opNorm`).
(3) `classical_le_two`: in a *commutative* ordered star-ring the same
expression is bounded by `2`, and `2 < 2√2` strictly (`bell_gap`). Along the
way, a falsification (`chsh_sq_ne`): the saturating tuple's `T²` is *not* the
scalar `8·1` (its square is not a scalar multiple of the identity), so the
naive scalar-square route `T² = 8·1 ⇒ ‖T‖ = √8` is closed for this
representation; the norm results here go through the C\*-identity (and, for
the generic bound, the Landau identity) instead.
-/

namespace TsirelsonTightness

open Matrix

/-! ## Generic results: any CHSH tuple, any carrier -/

/-- **Tsirelson's bound, `2√2` form.** Any CHSH tuple in an ordered star-ring
satisfies `A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ (2√2) • 1`. -/
theorem chsh_upper
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ (2 * Real.sqrt 2) • (1 : R) := by
  sorry

/-- **The Landau identity.** For any CHSH tuple in any \*-ring,
`T² = 4 + [A₀,A₁]·[B₁,B₀]`: the deviation of `T²` from the scalar `4` is
exactly the product of the two intra-party commutators (Landau 1987). -/
theorem chsh_mul_self
    {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
  sorry

/-- **Tsirelson's inequality in norm form, for every CHSH tuple.** In any
unital real C\*-normed algebra, `‖A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁‖ ≤ 2√2`. -/
theorem chsh_norm_le
    {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [Nontrivial R]
    [NormedAlgebra ℝ R] {A₀ A₁ B₀ B₁ : R}
    (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  sorry

/-- **The classical CHSH constant, exactly.** If either party's observables
commute, the CHSH operator has norm exactly `2` — the commutator product in
the Landau identity vanishes, so `T² = 4`. -/
theorem chsh_norm_of_comm
    {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [Nontrivial R]
    [NormedAlgebra ℝ R] {A₀ A₁ B₀ B₁ : R}
    (h : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : A₀ * A₁ = A₁ * A₀ ∨ B₀ * B₁ = B₁ * B₀) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 := by
  sorry

/-- **Necessity of noncommutativity.** Any CHSH tuple whose operator norm
exceeds the classical bound `2` must be noncommuting in **both** parties. -/
theorem noncomm_of_chsh_norm_gt_two
    {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [Nontrivial R]
    [NormedAlgebra ℝ R] {A₀ A₁ B₀ B₁ : R}
    (h : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hgt : 2 < ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖) :
    A₀ * A₁ ≠ A₁ * A₀ ∧ B₀ * B₁ ≠ B₁ * B₀ := by
  sorry

/-! ## The explicit saturating tuple in `M₄(ℝ)` -/

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

/-! ## Operator-norm results over `M₄(ℝ)` (l2 operator norm) -/

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- **Exact operator norm.** The CHSH operator of the real-Pauli tuple has
l2 operator norm exactly `2√2`, the Tsirelson value. -/
theorem chsh_opNorm :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 * Real.sqrt 2 := by
  sorry

/-- **Falsification:** the square of the CHSH operator is *not* the scalar
`8·1` — the naive scalar-square route to the Tsirelson norm fails for this
representation (compare the Landau identity `chsh_mul_self`: the commutator
product is not scalar here). -/
theorem chsh_sq_ne :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      ≠ (8 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  sorry

/-- **The exact CHSH constant of `M₄(ℝ)` is `2√2`:** it is the *greatest*
element of the set of CHSH operator norms over 4×4 real matrices — an upper
bound for every CHSH tuple, attained by the real-Pauli tuple above. Not a
bound plus an example: the supremum, achieved. -/
theorem chsh_opNorm_isGreatest :
    IsGreatest {x : ℝ | ∃ A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℝ,
        IsCHSHTuple A₀ A₁ B₀ B₁ ∧ x = ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖}
      (2 * Real.sqrt 2) := by
  sorry

end OperatorNorm

end TsirelsonTightness
