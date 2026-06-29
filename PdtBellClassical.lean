import Mathlib

namespace PDT
open scoped Real

/-!
# The classical (commutative) CHSH bound ≤ 2 — the Bell gap

Companion to `PdtTsirelson` (quantum bound 2√2, saturated by the real-Pauli tuple).
Commuting observables cannot exceed 2; the noncommutative real-Pauli tuple reaches 2√2.
-/

/-- **Classical CHSH bound ≤ 2.** In a COMMUTATIVE ordered \*-ring, any CHSH tuple satisfies
`A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ ≤ 2` (Mathlib's `CHSH_inequality_of_comm`). The commutativity
hypothesis is exactly what fails in the quantum case. -/
theorem chsh_comm_le_two
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  CHSH_inequality_of_comm A₀ A₁ B₀ B₁ T

/-- **The Bell gap is strict:** the classical bound `2` is strictly below the quantum
Tsirelson value `2√2 ≈ 2.828`. Commuting observables stop at 2; noncommutativity reaches 2√2. -/
theorem bell_gap : (2 : ℝ) < 2 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

end PDT
