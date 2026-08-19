import PdtTsirelsonNorm
import PdtBellClassical

namespace PDT

open Matrix

/-!
# The exact CHSH constant over `M₄(ℝ)`: an optimality theorem

`PdtTsirelson.lean` gives the Tsirelson bound for one order-theoretic setting and
one explicit saturating tuple; `PdtTsirelsonNorm.lean` computes `‖P‖ = 2√2` for
that one tuple. This file proves the **exact-constant suite** — necessity and
attainment; Landau's converse (that every noncommuting pair admits a violating
state) is *not* formalized here:

* `chsh_norm_le` / `chsh_opNorm_le` — for **every** CHSH tuple (Mathlib's
  `IsCHSHTuple`: self-adjoint involutions, A's commuting with B's) in a unital
  C*-normed ring (in particular in `M₄(ℝ)` under the l2 operator norm), the CHSH
  operator `T = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` satisfies `‖T‖ ≤ 2√2`.

* `chsh_opNorm_isGreatest` — `2√2` **is** the exact CHSH constant of `M₄(ℝ)`:
  it is the greatest element of the set of CHSH operator norms, attained by the
  real-Pauli tuple of `PdtTsirelson.lean`.

* `chsh_norm_of_comm` / `chsh_opNorm_eq_two_of_comm` — if either party's pair
  commutes (`A₀A₁ = A₁A₀` or `B₀B₁ = B₁B₀`), then `‖T‖ = 2` **exactly**: the
  classical CHSH constant, exactly.

* `noncomm_of_chsh_norm_gt_two` — necessity, formally: any violation `‖T‖ > 2`
  forces noncommutativity in **both** parties. Instantiated on the concrete
  real-Pauli tuple (`A_noncomm`, `B_noncomm`), with an independent
  entrywise check (`A_noncomm_explicit`).

The proof is the Landau/Tsirelson C*-argument, made kernel-checked:
`T` is self-adjoint and `T² = 4 + [A₀,A₁]·[B₁,B₀]` (an identity in *any* ring,
given the tuple relations — `chsh_mul_self`), each commutator has norm ≤ 2
(the generators are self-adjoint involutions, hence of norm 1 by the
C*-identity), so `‖T‖² = ‖T²‖ ≤ 4 + 4 = 8`. No Loewner-order transfer is
needed: the C*-identity alone carries the argument.
-/

/-! ## Ring-level identities (no norm, no order) -/

section RingIdentities

variable {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}

/-- The CHSH operator of any CHSH tuple is self-adjoint (abstract form of
`PDT.Pchsh_sa`): `star` flips each product, and cross-party commutation flips
it back. -/
theorem chsh_sa (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ := by
  rw [star_sub, star_add, star_add, star_mul, star_mul, star_mul, star_mul,
    h.A₀_sa, h.A₁_sa, h.B₀_sa, h.B₁_sa,
    ← h.A₀B₀_commutes, ← h.A₀B₁_commutes, ← h.A₁B₀_commutes, ← h.A₁B₁_commutes]

/-- **The CHSH square identity.** For any CHSH tuple in any \*-ring,
`T² = 4 + [A₀,A₁]·[B₁,B₀]`. This is the exact, representation-independent
correction to the naive `T² = 8·1` (which `PdtTsirelsonNorm.Pchsh_sq_ne`
refutes for the real-Pauli tuple): the deviation of `T²` from the scalar `4`
is precisely the product of the two intra-party commutators. -/
theorem chsh_mul_self (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
  have sA₀ : A₀ * A₀ = 1 := by rw [← sq]; exact h.A₀_inv
  have sA₁ : A₁ * A₁ = 1 := by rw [← sq]; exact h.A₁_inv
  have sB₀ : B₀ * B₀ = 1 := by rw [← sq]; exact h.B₀_inv
  have sB₁ : B₁ * B₁ = 1 := by rw [← sq]; exact h.B₁_inv
  -- sorted-product helper: pull the second factor's A past the first factor's B.
  have key : ∀ a b c d : R, c * b = b * c → a * b * (c * d) = a * c * (b * d) := by
    intro a b c d hcb
    calc a * b * (c * d) = a * (b * c) * d := by noncomm_ring
      _ = a * (c * b) * d := by rw [← hcb]
      _ = a * c * (b * d) := by noncomm_ring
  calc
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
        = A₀ * B₀ * (A₀ * B₀) + A₀ * B₀ * (A₀ * B₁) + A₀ * B₀ * (A₁ * B₀)
            - A₀ * B₀ * (A₁ * B₁)
          + (A₀ * B₁ * (A₀ * B₀) + A₀ * B₁ * (A₀ * B₁) + A₀ * B₁ * (A₁ * B₀)
            - A₀ * B₁ * (A₁ * B₁))
          + (A₁ * B₀ * (A₀ * B₀) + A₁ * B₀ * (A₀ * B₁) + A₁ * B₀ * (A₁ * B₀)
            - A₁ * B₀ * (A₁ * B₁))
          - (A₁ * B₁ * (A₀ * B₀) + A₁ * B₁ * (A₀ * B₁) + A₁ * B₁ * (A₁ * B₀)
            - A₁ * B₁ * (A₁ * B₁)) := by noncomm_ring
    _ = A₀ * A₀ * (B₀ * B₀) + A₀ * A₀ * (B₀ * B₁) + A₀ * A₁ * (B₀ * B₀)
            - A₀ * A₁ * (B₀ * B₁)
          + (A₀ * A₀ * (B₁ * B₀) + A₀ * A₀ * (B₁ * B₁) + A₀ * A₁ * (B₁ * B₀)
            - A₀ * A₁ * (B₁ * B₁))
          + (A₁ * A₀ * (B₀ * B₀) + A₁ * A₀ * (B₀ * B₁) + A₁ * A₁ * (B₀ * B₀)
            - A₁ * A₁ * (B₀ * B₁))
          - (A₁ * A₀ * (B₁ * B₀) + A₁ * A₀ * (B₁ * B₁) + A₁ * A₁ * (B₁ * B₀)
            - A₁ * A₁ * (B₁ * B₁)) := by
        rw [key A₀ B₀ A₀ B₀ h.A₀B₀_commutes, key A₀ B₀ A₀ B₁ h.A₀B₀_commutes,
          key A₀ B₀ A₁ B₀ h.A₁B₀_commutes, key A₀ B₀ A₁ B₁ h.A₁B₀_commutes,
          key A₀ B₁ A₀ B₀ h.A₀B₁_commutes, key A₀ B₁ A₀ B₁ h.A₀B₁_commutes,
          key A₀ B₁ A₁ B₀ h.A₁B₁_commutes, key A₀ B₁ A₁ B₁ h.A₁B₁_commutes,
          key A₁ B₀ A₀ B₀ h.A₀B₀_commutes, key A₁ B₀ A₀ B₁ h.A₀B₀_commutes,
          key A₁ B₀ A₁ B₀ h.A₁B₀_commutes, key A₁ B₀ A₁ B₁ h.A₁B₀_commutes,
          key A₁ B₁ A₀ B₀ h.A₀B₁_commutes, key A₁ B₁ A₀ B₁ h.A₀B₁_commutes,
          key A₁ B₁ A₁ B₀ h.A₁B₁_commutes, key A₁ B₁ A₁ B₁ h.A₁B₁_commutes]
    _ = 4 + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁) := by
        rw [sA₀, sA₁, sB₀, sB₁, show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
        noncomm_ring

end RingIdentities

/-! ## Norm-level results in a unital C*-normed ring -/

section CStarNorm

variable {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [Nontrivial R]

/-- A self-adjoint involution in a unital C*-normed ring has norm exactly 1. -/
theorem norm_eq_one_of_selfAdjoint_involution {a : R}
    (hsa : star a = a) (hinv : a ^ 2 = 1) : ‖a‖ = 1 := by
  have hsq : ‖a‖ * ‖a‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self (x := a), hsa, ← sq, hinv, CStarRing.norm_one]
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exact h1
  · linarith [norm_nonneg a]

variable [NormedAlgebra ℝ R]

/-- `‖(4 : R)‖ = 4` in a unital real C*-normed algebra. -/
theorem norm_four : ‖(4 : R)‖ = 4 := by
  have h : (4 : R) = (4 : ℝ) • (1 : R) := by
    rw [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  rw [h, norm_smul, CStarRing.norm_one, Real.norm_ofNat, mul_one]

variable {A₀ A₁ B₀ B₁ : R}

/-- **Tsirelson's inequality in norm form, for every CHSH tuple.** In any
unital real C*-normed algebra, a CHSH tuple's operator satisfies
`‖T‖ ≤ 2√2`. Proof: `T` is self-adjoint with `T² = 4 + [A₀,A₁][B₁,B₀]`
(`chsh_mul_self`); the generators have norm 1 (`norm_eq_one_of_selfAdjoint_involution`),
so each commutator has norm ≤ 2 and `‖T‖² = ‖T²‖ ≤ 4 + 2·2 = 8`. -/
theorem chsh_norm_le (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  have nA₀ : ‖A₀‖ = 1 := norm_eq_one_of_selfAdjoint_involution h.A₀_sa h.A₀_inv
  have nA₁ : ‖A₁‖ = 1 := norm_eq_one_of_selfAdjoint_involution h.A₁_sa h.A₁_inv
  have nB₀ : ‖B₀‖ = 1 := norm_eq_one_of_selfAdjoint_involution h.B₀_sa h.B₀_inv
  have nB₁ : ‖B₁‖ = 1 := norm_eq_one_of_selfAdjoint_involution h.B₁_sa h.B₁_inv
  have hcommA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 := by
    calc ‖A₀ * A₁ - A₁ * A₀‖ ≤ ‖A₀ * A₁‖ + ‖A₁ * A₀‖ := norm_sub_le _ _
      _ ≤ ‖A₀‖ * ‖A₁‖ + ‖A₁‖ * ‖A₀‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 := by rw [nA₀, nA₁]; norm_num
  have hcommB : ‖B₁ * B₀ - B₀ * B₁‖ ≤ 2 := by
    calc ‖B₁ * B₀ - B₀ * B₁‖ ≤ ‖B₁ * B₀‖ + ‖B₀ * B₁‖ := norm_sub_le _ _
      _ ≤ ‖B₁‖ * ‖B₀‖ + ‖B₀‖ * ‖B₁‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 := by rw [nB₀, nB₁]; norm_num
  have hTsq : ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖
      * ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 8 := by
    calc ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖
          * ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖
        = ‖star (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
            * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)‖ :=
          CStarRing.norm_star_mul_self.symm
      _ = ‖(4 : R) + (A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖ := by
          rw [chsh_sa h, chsh_mul_self h]
      _ ≤ ‖(4 : R)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₁ * B₀ - B₀ * B₁)‖ := norm_add_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₁ * B₀ - B₀ * B₁‖ := by
          rw [norm_four]; exact add_le_add le_rfl (norm_mul_le _ _)
      _ ≤ 4 + 2 * 2 :=
          add_le_add le_rfl (mul_le_mul hcommA hcommB (norm_nonneg _) (by norm_num))
      _ = 8 := by norm_num
  nlinarith [norm_nonneg (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁),
    Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- **The classical CHSH constant, exactly.** If either party's observables
commute, the CHSH operator has norm exactly `2`: the commutator product in
`chsh_mul_self` vanishes, so `T² = 4` and the C*-identity gives `‖T‖² = 4`. -/
theorem chsh_norm_of_comm (h : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : A₀ * A₁ = A₁ * A₀ ∨ B₀ * B₁ = B₁ * B₀) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 := by
  have hTT : (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) = 4 := by
    rcases hcomm with hA | hB
    · rw [chsh_mul_self h, hA, sub_self, zero_mul, add_zero]
    · rw [chsh_mul_self h, hB, sub_self, mul_zero, add_zero]
  have hsq : ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖
      * ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 4 := by
    rw [← CStarRing.norm_star_mul_self, chsh_sa h, hTT, norm_four]
  exact (mul_self_inj (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mp
    (hsq.trans (by norm_num))

/-- **Necessity of noncommutativity, formally.** Any CHSH tuple whose operator
norm exceeds the classical bound `2` must be noncommuting in **both** parties:
`A₀A₁ ≠ A₁A₀` and `B₀B₁ ≠ B₁B₀`. (Contrapositive of `chsh_norm_of_comm`:
commutation on either side pins the norm at exactly 2.) -/
theorem noncomm_of_chsh_norm_gt_two (h : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hgt : 2 < ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖) :
    A₀ * A₁ ≠ A₁ * A₀ ∧ B₀ * B₁ ≠ B₁ * B₀ := by
  constructor
  · intro hA
    rw [chsh_norm_of_comm h (Or.inl hA)] at hgt
    exact lt_irrefl 2 hgt
  · intro hB
    rw [chsh_norm_of_comm h (Or.inr hB)] at hgt
    exact lt_irrefl 2 hgt

end CStarNorm

/-! ## The exact CHSH constant of `M₄(ℝ)` -/

section MatrixCase

open scoped Matrix.Norms.L2Operator

/-- **The generic upper bound over `M₄(ℝ)`:** every CHSH tuple of 4×4 real
matrices has CHSH operator norm at most `2√2` (l2 operator norm). -/
theorem chsh_opNorm_le (A₀ A₁ B₀ B₁ : Mat) (h : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_norm_le h

/-- **The exact CHSH constant of `M₄(ℝ)` is `2√2`:** it is the *greatest*
CHSH operator norm — an upper bound for every CHSH tuple (`chsh_opNorm_le`),
attained by the real-Pauli tuple of `PdtTsirelson.lean` (`Pchsh_opNorm`).
This is the optimality theorem: not a bound plus an example, but the
supremum, achieved. -/
theorem chsh_opNorm_isGreatest :
    IsGreatest {x : ℝ | ∃ A₀ A₁ B₀ B₁ : Mat, IsCHSHTuple A₀ A₁ B₀ B₁ ∧
      x = ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖} (2 * Real.sqrt 2) := by
  constructor
  · exact ⟨A₀, A₁, B₀, B₁, isCHSH, Pchsh_opNorm.symm⟩
  · rintro x ⟨a₀, a₁, b₀, b₁, h, rfl⟩
    exact chsh_opNorm_le a₀ a₁ b₀ b₁ h

/-- **The classical constant over `M₄(ℝ)`, exactly:** a CHSH tuple with either
party commuting has CHSH operator norm exactly `2`. -/
theorem chsh_opNorm_eq_two_of_comm (A₀ A₁ B₀ B₁ : Mat) (h : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : A₀ * A₁ = A₁ * A₀ ∨ B₀ * B₁ = B₁ * B₀) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 :=
  chsh_norm_of_comm h hcomm

/-- The real-Pauli CHSH operator violates the classical bound: `2 < ‖P‖ = 2√2`. -/
theorem Pchsh_opNorm_gt_two : 2 < ‖Pchsh‖ := by
  rw [Pchsh_opNorm]; exact bell_gap

/-- **Necessity, instantiated:** the real-Pauli tuple's Alice observables do
not commute — forced by its CHSH violation via `noncomm_of_chsh_norm_gt_two`,
not checked entrywise. -/
theorem A_noncomm : A₀ * A₁ ≠ A₁ * A₀ :=
  (noncomm_of_chsh_norm_gt_two isCHSH Pchsh_opNorm_gt_two).1

/-- **Necessity, instantiated:** Bob's observables do not commute either. -/
theorem B_noncomm : B₀ * B₁ ≠ B₁ * B₀ :=
  (noncomm_of_chsh_norm_gt_two isCHSH Pchsh_opNorm_gt_two).2

end MatrixCase

/-- Independent entrywise check of `A_noncomm`: the `(0,2)` entries of
`A₀A₁` and `A₁A₀` are `−1` and `1`. -/
theorem A_noncomm_explicit : A₀ * A₁ ≠ A₁ * A₀ := by
  intro hcontra
  have h02 := congrArg (fun M : Mat => M 0 2) hcontra
  norm_num [A₀, A₁, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at h02

end PDT

-- Axiom audit (repo idiom): every theorem must depend on at most
-- {propext, Classical.choice, Quot.sound}.
#print axioms PDT.chsh_sa
#print axioms PDT.chsh_mul_self
#print axioms PDT.norm_eq_one_of_selfAdjoint_involution
#print axioms PDT.norm_four
#print axioms PDT.chsh_norm_le
#print axioms PDT.chsh_norm_of_comm
#print axioms PDT.noncomm_of_chsh_norm_gt_two
#print axioms PDT.chsh_opNorm_le
#print axioms PDT.chsh_opNorm_isGreatest
#print axioms PDT.chsh_opNorm_eq_two_of_comm
#print axioms PDT.Pchsh_opNorm_gt_two
#print axioms PDT.A_noncomm
#print axioms PDT.B_noncomm
#print axioms PDT.A_noncomm_explicit
