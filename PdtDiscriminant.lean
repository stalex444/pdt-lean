import Mathlib
set_option linter.unusedSimpArgs false

namespace PDT

open Polynomial AdjoinRoot Algebra Matrix

noncomputable section

/-- The cubic `X^3 - X - 1`. -/
def fc : ℚ[X] := X ^ 3 - X - 1

lemma fc_monic : (fc).Monic := by
  unfold fc; monicity!

lemma fc_deg : (fc).natDegree = 3 := by
  unfold fc; compute_degree!

lemma fc_degree : (fc).degree = 3 := by
  unfold fc; compute_degree!

/-- K = ℚ[x]/(x³-x-1) as a ℚ-algebra, free of rank 3. -/
abbrev Kc := AdjoinRoot fc

/-- power basis -/
def pbc : PowerBasis ℚ Kc := powerBasis' fc_monic

lemma pbc_dim : pbc.dim = 3 := by
  rw [pbc, powerBasis'_dim, fc_deg]

-- The defining relation in K: root^3 = root + 1
lemma rootc_cubed : (root fc) ^ 3 = root fc + 1 := by
  have h : (aeval (root fc)) fc = 0 := by rw [aeval_eq, mk_self]
  have h2 : (root fc) ^ 3 - (root fc) - 1 = 0 := by
    have : (aeval (root fc)) fc = (root fc) ^ 3 - (root fc) - 1 := by
      unfold fc; simp [map_sub, map_pow]
    rw [← this]; exact h
  linear_combination h2

/-- repr of a power of root in the power basis = coeff of (X^m %ₘ fc). -/
lemma repr_root_pow (m : ℕ) (i : Fin fc.natDegree) :
    (powerBasis' fc_monic).basis.repr (root fc ^ m) i = (X ^ m %ₘ fc).coeff (i : ℕ) := by
  have hr : (root fc ^ m) = mk fc (X ^ m) := by
    rw [map_pow, ← aeval_eq]; simp [aeval_X]
  rw [hr]
  show (powerBasisAux' fc_monic).repr (mk fc (X ^ m)) i = _
  rw [powerBasisAux'_repr_apply_to_fun, modByMonicHom_mk]

-- Reduced representatives of X^m mod fc (deg < 3), via div_modByMonic_unique.
lemma mod3 : (X : ℚ[X]) ^ 3 %ₘ fc = X + 1 :=
  (div_modByMonic_unique (f := X ^ 3) 1 (X + 1) fc_monic
    ⟨by unfold fc; ring, by rw [fc_degree]; compute_degree!⟩).2

lemma mod4 : (X : ℚ[X]) ^ 4 %ₘ fc = X ^ 2 + X :=
  (div_modByMonic_unique (f := X ^ 4) X (X ^ 2 + X) fc_monic
    ⟨by unfold fc; ring, by rw [fc_degree]; compute_degree!⟩).2

lemma mod5 : (X : ℚ[X]) ^ 5 %ₘ fc = X ^ 2 + X + 1 :=
  (div_modByMonic_unique (f := X ^ 5) (X ^ 2 + 1) (X ^ 2 + X + 1) fc_monic
    ⟨by unfold fc; ring, by rw [fc_degree]; compute_degree!⟩).2

lemma mod6 : (X : ℚ[X]) ^ 6 %ₘ fc = X ^ 2 + 2 * X + 1 :=
  (div_modByMonic_unique (f := X ^ 6) (X ^ 3 + X + 1) (X ^ 2 + 2 * X + 1) fc_monic
    ⟨by unfold fc; ring, by rw [fc_degree]; compute_degree!⟩).2

/-- trace of root^k = sum over basis of (X^{k+i} %ₘ fc).coeff i. -/
lemma trace_root_pow (k : ℕ) :
    Algebra.trace ℚ Kc (root fc ^ k) =
      ∑ i : Fin (powerBasis' fc_monic).dim, (X ^ (k + (i : ℕ)) %ₘ fc).coeff (i : ℕ) := by
  rw [Algebra.trace_eq_matrix_trace (powerBasis' fc_monic).basis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, leftMulMatrix_eq_repr_mul]
  have hb : (powerBasis' fc_monic).basis i = root fc ^ (i : ℕ) := by
    rw [(powerBasis' fc_monic).basis_eq_pow, powerBasis'_gen]
  rw [hb, ← pow_add, repr_root_pow]

-- Reduced forms for low powers (degree < 3): X^m %ₘ fc = X^m.
lemma mod0 : (X : ℚ[X]) ^ 0 %ₘ fc = 1 := by
  rw [pow_zero]; exact (modByMonic_eq_self_iff fc_monic).mpr (by rw [fc_degree]; compute_degree!)
lemma mod1 : (X : ℚ[X]) ^ 1 %ₘ fc = X := by
  rw [pow_one]; exact (modByMonic_eq_self_iff fc_monic).mpr (by rw [fc_degree]; compute_degree!)
lemma mod2 : (X : ℚ[X]) ^ 2 %ₘ fc = X ^ 2 := by
  exact (modByMonic_eq_self_iff fc_monic).mpr (by rw [fc_degree]; compute_degree!)

/-- The power-sum / trace dictionary (Newton sums) p_k = trace(root^k). -/
lemma pdim : (powerBasis' fc_monic).dim = 3 := by rw [powerBasis'_dim, fc_deg]

/-- Evaluate trace(root^k) as a Fin-3 sum of coeffs. -/
lemma trace_eval (k : ℕ) :
    Algebra.trace ℚ Kc (root fc ^ k) =
      (X ^ (k + 0) %ₘ fc).coeff 0 + (X ^ (k + 1) %ₘ fc).coeff 1
        + (X ^ (k + 2) %ₘ fc).coeff 2 := by
  rw [trace_root_pow]
  rw [Fintype.sum_equiv (finCongr pdim)
      (fun i => (X ^ (k + (i : ℕ)) %ₘ fc).coeff (i : ℕ))
      (fun j => (X ^ (k + (j : ℕ)) %ₘ fc).coeff (j : ℕ))
      (fun i => by simp)]
  rw [Fin.sum_univ_three]
  rfl

-- The seven power sums (Newton traces) for the cubic.
lemma p0 : Algebra.trace ℚ Kc (root fc ^ 0) = 3 := by
  rw [trace_eval, mod0, mod1, mod2]; simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num
lemma p1 : Algebra.trace ℚ Kc (root fc ^ 1) = 0 := by
  rw [trace_eval, mod1, mod2, mod3]; simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num
lemma p2 : Algebra.trace ℚ Kc (root fc ^ 2) = 2 := by
  rw [trace_eval, mod2, mod3, mod4]; simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num
lemma p3 : Algebra.trace ℚ Kc (root fc ^ 3) = 3 := by
  rw [trace_eval, mod3, mod4, mod5]; simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num
lemma p4 : Algebra.trace ℚ Kc (root fc ^ 4) = 2 := by
  rw [trace_eval, mod4, mod5, mod6]; simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num

/-- The trace-form Gram matrix entry: traceMatrix(i,j) = trace(root^(i+j)). -/
lemma traceMatrix_entry (i j : Fin (powerBasis' fc_monic).dim) :
    Algebra.traceMatrix ℚ (powerBasis' fc_monic).basis i j =
      Algebra.trace ℚ Kc (root fc ^ ((i : ℕ) + (j : ℕ))) := by
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hi : (powerBasis' fc_monic).basis i = root fc ^ (i : ℕ) := by
    rw [(powerBasis' fc_monic).basis_eq_pow, powerBasis'_gen]
  have hj : (powerBasis' fc_monic).basis j = root fc ^ (j : ℕ) := by
    rw [(powerBasis' fc_monic).basis_eq_pow, powerBasis'_gen]
  rw [hi, hj, ← pow_add]

/-- The reindexed (Fin 3) trace-form Gram matrix is the explicit power-sum matrix. -/
lemma traceMatrix_fin3 :
    Algebra.traceMatrix ℚ ((powerBasis' fc_monic).basis ∘ (finCongr pdim).symm) =
      !![(3 : ℚ), 0, 2; 0, 2, 3; 2, 3, 2] := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hcomp : ∀ k : Fin 3, ((powerBasis' fc_monic).basis ∘ (finCongr pdim).symm) k
      = root fc ^ ((finCongr pdim).symm k : ℕ) := by
    intro k
    simp only [Function.comp_apply]
    rw [(powerBasis' fc_monic).basis_eq_pow, powerBasis'_gen]
  rw [hcomp, hcomp, ← pow_add]
  have he : ∀ k : Fin 3, ((finCongr pdim).symm k : ℕ) = (k : ℕ) := fun k => rfl
  rw [he, he]
  fin_cases i <;> fin_cases j <;>
    (simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Nat.reduceAdd]
     first
       | rw [p0] | rw [p1] | rw [p2] | rw [p3] | rw [p4]
     simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
       Matrix.tail_cons])

/-- **GENUINE discriminant of x³ − x − 1.**
The discriminant of the power basis `{1, ρ, ρ²}` of `ℚ[x]/(x³−x−1)` is `-23`. -/
theorem discr_cubic : Algebra.discr ℚ (powerBasis' fc_monic).basis = -23 := by
  rw [← Algebra.discr_reindex ℚ (powerBasis' fc_monic).basis (finCongr pdim),
    Algebra.discr_def, traceMatrix_fin3, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.cons_val']

/-! ## Quartic x⁴ − x − 1, discriminant −283 -/

/-- The quartic `X^4 - X - 1`. -/
def fq : ℚ[X] := X ^ 4 - X - 1

lemma fq_monic : (fq).Monic := by unfold fq; monicity!
lemma fq_deg : (fq).natDegree = 4 := by unfold fq; compute_degree!
lemma fq_degree : (fq).degree = 4 := by unfold fq; compute_degree!

abbrev Kq := AdjoinRoot fq

lemma qdim : (powerBasis' fq_monic).dim = 4 := by rw [powerBasis'_dim, fq_deg]

/-- repr of a power of root in the quartic power basis. -/
lemma repr_root_pow_q (m : ℕ) (i : Fin fq.natDegree) :
    (powerBasis' fq_monic).basis.repr (root fq ^ m) i = (X ^ m %ₘ fq).coeff (i : ℕ) := by
  have hr : (root fq ^ m) = mk fq (X ^ m) := by
    rw [map_pow, ← aeval_eq]; simp [aeval_X]
  rw [hr]
  show (powerBasisAux' fq_monic).repr (mk fq (X ^ m)) i = _
  rw [powerBasisAux'_repr_apply_to_fun, modByMonicHom_mk]

lemma trace_root_pow_q (k : ℕ) :
    Algebra.trace ℚ Kq (root fq ^ k) =
      ∑ i : Fin (powerBasis' fq_monic).dim, (X ^ (k + (i : ℕ)) %ₘ fq).coeff (i : ℕ) := by
  rw [Algebra.trace_eq_matrix_trace (powerBasis' fq_monic).basis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, leftMulMatrix_eq_repr_mul]
  have hb : (powerBasis' fq_monic).basis i = root fq ^ (i : ℕ) := by
    rw [(powerBasis' fq_monic).basis_eq_pow, powerBasis'_gen]
  rw [hb, ← pow_add, repr_root_pow_q]

lemma trace_eval_q (k : ℕ) :
    Algebra.trace ℚ Kq (root fq ^ k) =
      (X ^ (k + 0) %ₘ fq).coeff 0 + (X ^ (k + 1) %ₘ fq).coeff 1
        + (X ^ (k + 2) %ₘ fq).coeff 2 + (X ^ (k + 3) %ₘ fq).coeff 3 := by
  rw [trace_root_pow_q]
  rw [Fintype.sum_equiv (finCongr qdim)
      (fun i => (X ^ (k + (i : ℕ)) %ₘ fq).coeff (i : ℕ))
      (fun j => (X ^ (k + (j : ℕ)) %ₘ fq).coeff (j : ℕ))
      (fun i => by simp)]
  rw [Fin.sum_univ_four]
  rfl

-- Reduced reps mod fq.
lemma qmod0 : (X : ℚ[X]) ^ 0 %ₘ fq = 1 := by
  rw [pow_zero]; exact (modByMonic_eq_self_iff fq_monic).mpr (by rw [fq_degree]; compute_degree!)
lemma qmod1 : (X : ℚ[X]) ^ 1 %ₘ fq = X := by
  rw [pow_one]; exact (modByMonic_eq_self_iff fq_monic).mpr (by rw [fq_degree]; compute_degree!)
lemma qmod2 : (X : ℚ[X]) ^ 2 %ₘ fq = X ^ 2 :=
  (modByMonic_eq_self_iff fq_monic).mpr (by rw [fq_degree]; compute_degree!)
lemma qmod3 : (X : ℚ[X]) ^ 3 %ₘ fq = X ^ 3 :=
  (modByMonic_eq_self_iff fq_monic).mpr (by rw [fq_degree]; compute_degree!)
lemma qmod4 : (X : ℚ[X]) ^ 4 %ₘ fq = X + 1 :=
  (div_modByMonic_unique (f := X ^ 4) 1 (X + 1) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2
lemma qmod5 : (X : ℚ[X]) ^ 5 %ₘ fq = X ^ 2 + X :=
  (div_modByMonic_unique (f := X ^ 5) X (X ^ 2 + X) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2
lemma qmod6 : (X : ℚ[X]) ^ 6 %ₘ fq = X ^ 3 + X ^ 2 :=
  (div_modByMonic_unique (f := X ^ 6) (X ^ 2) (X ^ 3 + X ^ 2) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2
lemma qmod7 : (X : ℚ[X]) ^ 7 %ₘ fq = X ^ 3 + X + 1 :=
  (div_modByMonic_unique (f := X ^ 7) (X ^ 3 + 1) (X ^ 3 + X + 1) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2
lemma qmod8 : (X : ℚ[X]) ^ 8 %ₘ fq = X ^ 2 + 2 * X + 1 :=
  (div_modByMonic_unique (f := X ^ 8) (X ^ 4 + X + 1) (X ^ 2 + 2 * X + 1) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2
lemma qmod9 : (X : ℚ[X]) ^ 9 %ₘ fq = X ^ 3 + 2 * X ^ 2 + X :=
  (div_modByMonic_unique (f := X ^ 9) (X ^ 5 + X ^ 2 + X) (X ^ 3 + 2 * X ^ 2 + X) fq_monic
    ⟨by unfold fq; ring, by rw [fq_degree]; compute_degree!⟩).2

-- Power sums (traces) for the quartic.
lemma q0 : Algebra.trace ℚ Kq (root fq ^ 0) = 4 := by
  rw [trace_eval_q, qmod0, qmod1, qmod2, qmod3]
  simp only [coeff_X_pow, coeff_X, coeff_one]; norm_num
lemma q1 : Algebra.trace ℚ Kq (root fq ^ 1) = 0 := by
  rw [trace_eval_q, qmod1, qmod2, qmod3, qmod4]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add]; norm_num
lemma q2 : Algebra.trace ℚ Kq (root fq ^ 2) = 0 := by
  rw [trace_eval_q, qmod2, qmod3, qmod4, qmod5]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add]; norm_num
lemma q3 : Algebra.trace ℚ Kq (root fq ^ 3) = 3 := by
  rw [trace_eval_q, qmod3, qmod4, qmod5, qmod6]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add]; norm_num
lemma q4 : Algebra.trace ℚ Kq (root fq ^ 4) = 4 := by
  rw [trace_eval_q, qmod4, qmod5, qmod6, qmod7]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add]; norm_num
lemma q5 : Algebra.trace ℚ Kq (root fq ^ 5) = 0 := by
  rw [trace_eval_q, qmod5, qmod6, qmod7, qmod8]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num
lemma q6 : Algebra.trace ℚ Kq (root fq ^ 6) = 3 := by
  rw [trace_eval_q, qmod6, qmod7, qmod8, qmod9]
  simp only [coeff_X_pow, coeff_X, coeff_one, coeff_add, coeff_ofNat_mul]; norm_num

/-- The reindexed (Fin 4) trace-form Gram matrix is the explicit power-sum matrix. -/
lemma traceMatrix_fin4 :
    Algebra.traceMatrix ℚ ((powerBasis' fq_monic).basis ∘ (finCongr qdim).symm) =
      !![(4 : ℚ), 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hcomp : ∀ k : Fin 4, ((powerBasis' fq_monic).basis ∘ (finCongr qdim).symm) k
      = root fq ^ ((finCongr qdim).symm k : ℕ) := by
    intro k
    simp only [Function.comp_apply]
    rw [(powerBasis' fq_monic).basis_eq_pow, powerBasis'_gen]
  rw [hcomp, hcomp, ← pow_add]
  have he : ∀ k : Fin 4, ((finCongr qdim).symm k : ℕ) = (k : ℕ) := fun k => rfl
  rw [he, he]
  fin_cases i <;> fin_cases j <;>
    (simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Nat.reduceAdd,
      show ((3 : Fin 4) : ℕ) = 3 from rfl]
     first
       | rw [q0] | rw [q1] | rw [q2] | rw [q3] | rw [q4] | rw [q5] | rw [q6]
     simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
       Matrix.cons_val_three, Matrix.tail_cons])

/-- **GENUINE discriminant of x⁴ − x − 1.**
The discriminant of the power basis `{1, Q, Q², Q³}` of `ℚ[x]/(x⁴−x−1)` is `-283`. -/
theorem discr_quartic : Algebra.discr ℚ (powerBasis' fq_monic).basis = -283 := by
  rw [← Algebra.discr_reindex ℚ (powerBasis' fq_monic).basis (finCongr qdim),
    Algebra.discr_def, traceMatrix_fin4]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_fin_const,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val', Matrix.cons_val_fin_one,
    Matrix.empty_val', Matrix.of_apply, Fin.castSucc_zero, Fin.castSucc_one,
    show (Fin.castSucc 2 : Fin 4) = 2 from rfl]

end

end PDT
