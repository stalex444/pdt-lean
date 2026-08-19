import PdtTsirelson

namespace PDT

open Matrix

/-!
# The CHSH operator norm: `‖P‖ = 2√2` exactly

`PdtTsirelson.lean` proves the Tsirelson **bound** (`chsh_le_two_sqrt_two`, from
Mathlib's `tsirelson_inequality`) and the **saturation** on the eigenvector
`v = (1,0,0,1)` (`chsh_saturates`). Its docstring then *infers in prose* that
the operator norm of the CHSH operator is therefore ≥ `2√2` and, with the
bound, exactly `2√2`. This file converts that prose inference into a kernel
theorem, and strengthens it to **equality**:

  `‖P‖ = 2√2`  (`Pchsh_opNorm`)

where `‖·‖` is the l2 **operator** norm on `Matrix (Fin 4) (Fin 4) ℝ`
(Mathlib's scoped `Matrix.Norms.L2Operator` instances, under which `M₄(ℝ)` is
a C*-algebra).

**A falsification, kernel-certified along the way** (`Mchsh_sq_ne_sixteen_one`):
the tempting identity `M² = 16·1` (equivalently `P² = 8·1`) is FALSE for this
real-Pauli representation. `P = √2·(X⊗X + Z⊗Z)` has spectrum `{2√2, 0, 0, −2√2}`
— it has a 2-dimensional kernel — so `M = √2·P` has spectrum `{4, 0, 0, −4}` and
`M²` has eigenvalues `{16, 16, 0, 0}`, not `16` on all of `ℝ⁴`. The naive CHSH
algebra `P² = 4·1 + [A₀,A₁]·[B₁,B₀] = 8·1` fails here because the commutator
term is not scalar. The norm equality survives via the correct route:

* `P = s • M` with `s = 1/√2` (`Pchsh_eq_smul`);
* `M² = K` with `K` the explicit integer matrix (`Mchsh_sq_eq`), and `K` is
  (16×) an idempotent: `K² = 16·K` (`Kchsh_sq`), `K` self-adjoint, `K ≠ 0`;
* the C*-identity `‖Xᴴ·X‖ = ‖X‖²` applied to `K` gives `‖K‖² = ‖16·K‖ = 16·‖K‖`,
  so `‖K‖ = 16` (`Kchsh_opNorm`);
* applied to the self-adjoint `P` it gives
  `‖P‖² = ‖P²‖ = ‖(1/2)•K‖ = 8`, hence `‖P‖ = √8 = 2√2`.
-/

/-- The (scaled, physical) CHSH operator `P = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁`,
with `B₀ = s • B₀i`, `B₁ = s • B₁i`, `s = 1/√2`. -/
noncomputable def Pchsh : Mat := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- `P = s • M`: the physical CHSH operator is the integer CHSH matrix scaled
by `1/√2`. -/
theorem Pchsh_eq_smul : Pchsh = s • Mchsh := by
  unfold Pchsh Mchsh B₀ B₁
  rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm]
  rw [smul_sub, smul_add, smul_add]

/-- `K = M²` as an explicit integer matrix. Its eigenvalues are `{16,16,0,0}`;
`K/16` is the orthogonal projection onto the span of the two `M`-eigenvectors
with eigenvalue `±4`. -/
def Kchsh : Mat := !![8,0,0,8; 0,8,-8,0; 0,-8,8,0; 8,0,0,8]

/-- The square of the integer CHSH matrix, entrywise. -/
theorem Mchsh_sq_eq : Mchsh * Mchsh = Kchsh := by
  rw [Mchsh_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kchsh, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- **Falsification (kernel-certified):** `M² ≠ 16·1`. The `(0,0)` entry of
`M²` is `8`, not `16` — `M` has a 2-dimensional kernel, so no identity of the
form `M² = c·1` with `c ≠ 0` can hold. Equivalently `P² ≠ 8·1`: the naive
CHSH-algebra shortcut to the Tsirelson norm is not available for this
representation. -/
theorem Mchsh_sq_ne_sixteen_one : Mchsh * Mchsh ≠ (16 : ℝ) • (1 : Mat) := by
  rw [Mchsh_sq_eq]
  intro h
  have h00 := congrArg (fun X : Mat => X 0 0) h
  norm_num [Kchsh, Matrix.smul_apply, Matrix.one_apply] at h00

/-- `K² = 16·K` — `K/16` is idempotent. -/
theorem Kchsh_sq : Kchsh * Kchsh = (16 : ℝ) • Kchsh := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kchsh, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- `K` is symmetric, hence (real) self-adjoint. -/
theorem Kchsh_sa : star Kchsh = Kchsh := by
  rw [star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Kchsh]

theorem Kchsh_ne_zero : Kchsh ≠ 0 := by
  intro h
  have h00 := congrArg (fun X : Mat => X 0 0) h
  norm_num [Kchsh, Matrix.zero_apply] at h00

/-- **`P² = (1/2)·K`.** The scaled CHSH operator squares to half the
integer idempotent-like matrix `K` (NOT to `8·1`; see
`Mchsh_sq_ne_sixteen_one`). -/
theorem Pchsh_sq : Pchsh * Pchsh = (1 / 2 : ℝ) • Kchsh := by
  rw [Pchsh_eq_smul, smul_mul_smul_comm, Mchsh_sq_eq, s_sq]

/-- **Falsification, scaled form (kernel-certified):** `P² ≠ 8·1`. The `(0,0)`
entry of `P²` is `4`, not `8` — the scalar-square shortcut `P² = 8·1 ⇒ ‖P‖ = √8`
is not available for this representation. Scaled companion of
`Mchsh_sq_ne_sixteen_one`. -/
theorem Pchsh_sq_ne : Pchsh * Pchsh ≠ (8 : ℝ) • (1 : Mat) := by
  rw [Pchsh_sq]
  intro h
  have h00 := congrArg (fun X : Mat => X 0 0) h
  norm_num [Kchsh, Matrix.smul_apply, Matrix.one_apply] at h00

/-- The integer CHSH matrix is self-adjoint (star of each product swaps the
factors; cross-party commutation swaps them back). -/
theorem Mchsh_sa : star Mchsh = Mchsh := by
  unfold Mchsh
  rw [star_sub, star_add, star_add, star_mul, star_mul, star_mul, star_mul,
    A₀_sa, A₁_sa, B₀i_sa, B₁i_sa,
    ← A₀B₀i_comm, ← A₀B₁i_comm, ← A₁B₀i_comm, ← A₁B₁i_comm]

/-- The scaled CHSH operator is self-adjoint. -/
theorem Pchsh_sa : star Pchsh = Pchsh := by
  rw [Pchsh_eq_smul, star_smul, Mchsh_sa, star_trivial]

/-- Restatement of `chsh_saturates` in terms of `Pchsh`: the CHSH operator
attains the eigenvalue `2√2` on `v = (1,0,0,1)`. -/
theorem Pchsh_mulVec : Pchsh.mulVec vsat = (2 * Real.sqrt 2) • vsat :=
  chsh_saturates

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- `‖K‖ = 16` in the l2 operator norm, by the C*-identity:
`‖K‖² = ‖Kᴴ·K‖ = ‖K²‖ = ‖16·K‖ = 16·‖K‖` and `‖K‖ ≠ 0`. -/
theorem Kchsh_opNorm : ‖Kchsh‖ = 16 := by
  have hnz : ‖Kchsh‖ ≠ 0 := norm_ne_zero_iff.mpr Kchsh_ne_zero
  have hC : ‖Kchsh‖ * ‖Kchsh‖ = 16 * ‖Kchsh‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self Kchsh, ← star_eq_conjTranspose,
      Kchsh_sa, Kchsh_sq, norm_smul, Real.norm_ofNat]
  exact mul_right_cancel₀ hnz hC

/-- **The CHSH operator norm is exactly the Tsirelson value:** `‖P‖ = 2√2`,
in the l2 operator norm on `M₄(ℝ)`. Proof: the C*-identity plus `P`
self-adjoint give `‖P‖² = ‖P²‖ = ‖(1/2)•K‖ = (1/2)·16 = 8`; nonnegativity
pins `‖P‖ = √8 = 2√2`. This replaces the prose inference in
`PdtTsirelson.lean` ("the operator norm of `P` is ≥ `2√2`") with a kernel
equality. -/
theorem Pchsh_opNorm : ‖Pchsh‖ = 2 * Real.sqrt 2 := by
  have hsq : ‖Pchsh‖ * ‖Pchsh‖ = 8 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self Pchsh, ← star_eq_conjTranspose,
      Pchsh_sa, Pchsh_sq, norm_smul, Kchsh_opNorm,
      Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hval : (2 * Real.sqrt 2) * (2 * Real.sqrt 2) = 8 := by nlinarith [h2]
  exact (mul_self_inj (norm_nonneg _) (by positivity)).mp (hsq.trans hval.symm)

end OperatorNorm

end PDT

-- Axiom audit (repo idiom): every theorem must depend on at most
-- {propext, Classical.choice, Quot.sound}.
#print axioms PDT.Pchsh_eq_smul
#print axioms PDT.Mchsh_sq_eq
#print axioms PDT.Mchsh_sq_ne_sixteen_one
#print axioms PDT.Kchsh_sq
#print axioms PDT.Kchsh_sa
#print axioms PDT.Kchsh_ne_zero
#print axioms PDT.Pchsh_sq
#print axioms PDT.Pchsh_sq_ne
#print axioms PDT.Mchsh_sa
#print axioms PDT.Pchsh_sa
#print axioms PDT.Pchsh_mulVec
#print axioms PDT.Kchsh_opNorm
#print axioms PDT.Pchsh_opNorm
