import Mathlib

namespace PDT

open scoped Real
open Matrix

/-!
# The Tsirelson bound 2√2 (FINDINGS:82)

We tie the PDT entanglement-bound claim to Mathlib's kernel-verified
`tsirelson_inequality` (in `Mathlib.Algebra.Star.CHSH`), and we construct
the explicit **real-Pauli** CHSH tuple that **saturates** the bound.

Mathlib states the upper bound as
  `A₀*B₀ + A₀*B₁ + A₁*B₀ − A₁*B₁ ≤ √2 ^ 3 • (1 : R)`,
and `√2 ^ 3 = 2 * √2`, the Tsirelson constant.
-/

/-! ## Part 0 : the scalar identity `√2 ^ 3 = 2 √2`. -/

/-- The scalar identity behind the bound: `√2 ^ 3 = 2 * √2`. -/
theorem sqrt_two_cubed_eq : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
    _ = 2 * Real.sqrt 2 := by rw [h]

/-- Numerically, the Tsirelson constant is `2√2 ≈ 2.828…`, in particular `< 3`. -/
theorem tsirelson_const_lt_three : (Real.sqrt 2) ^ 3 < 3 := by
  rw [sqrt_two_cubed_eq]
  have h : Real.sqrt 2 < 3 / 2 := by
    rw [show (3:ℝ)/2 = Real.sqrt ((3/2)^2) by rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-! ## Part (a) : the bound, instantiated from Mathlib's verified theorem. -/

/-- **Tsirelson bound, PDT form (a):** for any CHSH tuple in a noncommutative
ordered real \*-algebra, the CHSH operator is bounded by `2 √2 • 1`.
This is a direct instantiation of Mathlib's `tsirelson_inequality`, with the
constant rewritten into the familiar `2√2` form. -/
theorem chsh_le_two_sqrt_two
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ (2 * Real.sqrt 2) • (1 : R) := by
  have h := tsirelson_inequality A₀ A₁ B₀ B₁ T
  rwa [sqrt_two_cubed_eq] at h

/-! ## Part (b) : the explicit real-Pauli tuple in `M₄(ℝ)` that saturates 2√2.

Working in `Matrix (Fin 4) (Fin 4) ℝ ≅ M₂(ℝ) ⊗ M₂(ℝ)` with computational basis
`|00⟩,|01⟩,|10⟩,|11⟩`. Real Paulis `X = !![0,1;1,0]`, `Z = !![1,0;0,-1]`.

  A₀ = X ⊗ I,   A₁ = Z ⊗ I,
  B₀ = I ⊗ (X+Z)/√2,   B₁ = I ⊗ (X−Z)/√2.

We factor the `√2` out:  `B₀ = (√2)⁻¹ • B₀i`, `B₁ = (√2)⁻¹ • B₁i`,
with `B₀i = I⊗(X+Z)`, `B₁i = I⊗(X−Z)` having integer entries and squaring to `2•1`.
-/

/-- `s = 1/√2`. -/
noncomputable def s : ℝ := (Real.sqrt 2)⁻¹

theorem s_sq : s * s = (1 : ℝ) / 2 := by
  unfold s
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

/-- `A₀ = X ⊗ I`. -/
def A₀ : Mat := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
/-- `A₁ = Z ⊗ I`. -/
def A₁ : Mat := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
/-- integer part of `B₀`:  `I ⊗ (X+Z)`. -/
def B₀i : Mat := !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]
/-- integer part of `B₁`:  `I ⊗ (X−Z)`. -/
def B₁i : Mat := !![-1,1,0,0; 1,1,0,0; 0,0,-1,1; 0,0,1,1]
/-- `B₀ = (1/√2) • (I⊗(X+Z))`. -/
noncomputable def B₀ : Mat := s • B₀i
/-- `B₁ = (1/√2) • (I⊗(X−Z))`. -/
noncomputable def B₁ : Mat := s • B₁i

/-- Helper: every integer building block squares correctly. -/
theorem A₀_sq : A₀ * A₀ = (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, Matrix.mul_apply, Fin.sum_univ_four]

theorem A₁_sq : A₁ * A₁ = (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, Matrix.mul_apply, Fin.sum_univ_four]

theorem B₀i_sq : B₀i * B₀i = (2 : ℝ) • (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B₀i, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem B₁i_sq : B₁i * B₁i = (2 : ℝ) • (1 : Mat) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B₁i, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The four building blocks are symmetric, so (being real) self-adjoint. -/
theorem A₀_sa : star A₀ = A₀ := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [A₀]
theorem A₁_sa : star A₁ = A₁ := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [A₁]
theorem B₀i_sa : star B₀i = B₀i := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [B₀i]
theorem B₁i_sa : star B₁i = B₁i := by
  rw [star_eq_conjTranspose]; ext i j; fin_cases i <;> fin_cases j <;> simp [B₁i]

/-- Cross-party commutation (A on party 1, B on party 2). -/
theorem A₀B₀i_comm : A₀ * B₀i = B₀i * A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, B₀i, Matrix.mul_apply, Fin.sum_univ_four]
theorem A₀B₁i_comm : A₀ * B₁i = B₁i * A₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₀, B₁i, Matrix.mul_apply, Fin.sum_univ_four]
theorem A₁B₀i_comm : A₁ * B₀i = B₀i * A₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, B₀i, Matrix.mul_apply, Fin.sum_univ_four]
theorem A₁B₁i_comm : A₁ * B₁i = B₁i * A₁ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A₁, B₁i, Matrix.mul_apply, Fin.sum_univ_four]

/-- **The real-Pauli quadruple is a genuine CHSH tuple.** -/
theorem isCHSH : IsCHSHTuple A₀ A₁ B₀ B₁ where
  A₀_inv := by rw [sq]; exact A₀_sq
  A₁_inv := by rw [sq]; exact A₁_sq
  B₀_inv := by
    rw [sq, B₀, smul_mul_smul_comm, B₀i_sq, smul_smul, s_sq]
    norm_num
  B₁_inv := by
    rw [sq, B₁, smul_mul_smul_comm, B₁i_sq, smul_smul, s_sq]
    norm_num
  A₀_sa := A₀_sa
  A₁_sa := A₁_sa
  B₀_sa := by rw [B₀, star_smul, B₀i_sa, star_trivial]
  B₁_sa := by rw [B₁, star_smul, B₁i_sa, star_trivial]
  A₀B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₀B₀i_comm]
  A₀B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₀B₁i_comm]
  A₁B₀_commutes := by rw [B₀, mul_smul_comm, smul_mul_assoc, A₁B₀i_comm]
  A₁B₁_commutes := by rw [B₁, mul_smul_comm, smul_mul_assoc, A₁B₁i_comm]

/-! ### Saturation: the CHSH operator achieves the eigenvalue `2√2`.

The CHSH operator `P = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ = (1/√2) • M`, where `M` is the
integer matrix `A₀B₀i + A₀B₁i + A₁B₀i − A₁B₁i`. `M` has the integer eigenvalue `4`
on the vector `v = (1,0,0,1)`, so `P` has eigenvalue `4/√2 = 2√2` on `v` — the
operator attains the Tsirelson value. -/

/-- The integer CHSH matrix `M = A₀B₀i + A₀B₁i + A₁B₀i − A₁B₁i`. -/
def Mchsh : Mat := A₀ * B₀i + A₀ * B₁i + A₁ * B₀i - A₁ * B₁i

/-- The eigenvector witnessing saturation. -/
def vsat : Fin 4 → ℝ := ![1,0,0,1]

/-- `M` evaluates to the explicit integer matrix `[[2,0,0,2],[0,-2,2,0],[0,2,-2,0],[2,0,0,2]]`. -/
theorem Mchsh_eq :
    Mchsh = !![2,0,0,2; 0,-2,2,0; 0,2,-2,0; 2,0,0,2] := by
  ext i j
  simp only [Mchsh, A₀, A₁, B₀i, B₁i, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- **`M` has integer eigenvalue 4 on `v=(1,0,0,1)`.** -/
theorem Mchsh_mulVec : Mchsh.mulVec vsat = (4 : ℝ) • vsat := by
  rw [Mchsh_eq]
  ext i; fin_cases i <;>
    simp [vsat, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- **Saturation of the Tsirelson bound (form b).**
The explicit real-Pauli CHSH operator `P = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁`
attains the eigenvalue `2√2` on the unit-direction `v = (1,0,0,1)`:
`P.mulVec v = (2√2) • v`. Since `‖v‖ ≠ 0`, the operator norm of `P` is ≥ `2√2`;
together with `chsh_le_two_sqrt_two` (≤ `2√2`), the bound is exactly attained. -/
theorem chsh_saturates :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁).mulVec vsat
      = (2 * Real.sqrt 2) • vsat := by
  -- Rewrite the operator as `s • Mchsh`.
  have hop : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ = s • Mchsh := by
    unfold Mchsh B₀ B₁
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm]
    rw [smul_sub, smul_add, smul_add]
  rw [hop]
  -- `(s • M).mulVec v = s • (M.mulVec v) = s • (4 • v) = (4s) • v`.
  rw [Matrix.smul_mulVec, Mchsh_mulVec, smul_smul]
  -- `4 * s = 2 √2`.
  have hcoef : (4 : ℝ) * s = 2 * Real.sqrt 2 := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    unfold s
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [show s * (4:ℝ) = (4:ℝ) * s by ring, hcoef]

/-- The witness direction is nonzero, so saturation is genuine (the operator
norm is bounded below by `2√2`). -/
theorem vsat_ne_zero : vsat ≠ 0 := by
  intro h
  have : vsat 0 = (0 : Fin 4 → ℝ) 0 := by rw [h]
  simp [vsat] at this

end PDT
