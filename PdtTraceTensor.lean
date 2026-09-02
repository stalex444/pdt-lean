import Mathlib
import PdtTraceCompositum

/-!
# The trace form of a tensor product of algebras, and the signature of a tensor product of
quadratic forms

General statements, for arbitrary finite free algebras `A`, `B` over a commutative ring `R` and
arbitrary quadratic forms over a linearly ordered field:

* `trace_tmul_general`      : `Tr_{A ⊗ B}(a ⊗ b) = Tr_A a · Tr_B b`;
* `traceForm_tmul_general`  : `⟨a ⊗ b, a' ⊗ b'⟩_{A ⊗ B} = ⟨a, a'⟩_A · ⟨b, b'⟩_B`;
* `traceMatrix_tensorProduct` : the Gram matrix of a tensor basis is the Kronecker product;
* `discr_tensorProduct`     : `disc(bA ⊗ bB) = disc(bA)^{|κ|} · disc(bB)^{|ι|}`;
* `sigPos_tmul`, `sigNeg_tmul` : the Sylvester signature of a tensor product of quadratic forms
  is `(p₁p₂ + n₁n₂, p₁n₂ + n₁p₂)`;
* `qTrace_tensor`           : the trace quadratic form of `A ⊗ B` is the tensor product of the
  trace quadratic forms.

The compositum results of `PdtTraceCompositum` are then re-derived as instances.
-/

namespace PDT

open Module TensorProduct
open scoped Kronecker

section General

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Left multiplication by a pure tensor is the tensor product of the left multiplications. -/
theorem lmul_tmul_general (a : A) (b : B) :
    Algebra.lmul R (A ⊗[R] B) (a ⊗ₜ b)
      = TensorProduct.map (Algebra.lmul R A a) (Algebra.lmul R B b) := by
  apply TensorProduct.ext'
  intro x y
  simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', TensorProduct.map_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]

/-- **The trace of a pure tensor is the product of the traces.** -/
theorem trace_tmul_general (a : A) (b : B) :
    Algebra.trace R (A ⊗[R] B) (a ⊗ₜ b) = Algebra.trace R A a * Algebra.trace R B b := by
  simp only [Algebra.trace_apply, lmul_tmul_general, LinearMap.trace_tensorProduct']

/-- **The trace form of a tensor product on pure tensors is the product of the trace forms.** -/
theorem traceForm_tmul_general (a a' : A) (b b' : B) :
    Algebra.traceForm R (A ⊗[R] B) (a ⊗ₜ b) (a' ⊗ₜ b')
      = Algebra.traceForm R A a a' * Algebra.traceForm R B b b' := by
  simp only [Algebra.traceForm_apply, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul_general]

variable {ι κ : Type*}

/-- **The Gram matrix of a tensor basis is the Kronecker product of the Gram matrices.** -/
theorem traceMatrix_tensorProduct (bA : Basis ι R A) (bB : Basis κ R B) :
    Algebra.traceMatrix R (⇑(bA.tensorProduct bB))
      = Algebra.traceMatrix R ⇑bA ⊗ₖ Algebra.traceMatrix R ⇑bB := by
  ext p q
  rw [Algebra.traceMatrix_apply, Basis.tensorProduct_apply', Basis.tensorProduct_apply',
    traceForm_tmul_general, Matrix.kroneckerMap_apply, Algebra.traceMatrix_apply,
    Algebra.traceMatrix_apply]

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The discriminant product formula for a tensor basis.** -/
theorem discr_tensorProduct (bA : Basis ι R A) (bB : Basis κ R B) :
    Algebra.discr R (⇑(bA.tensorProduct bB))
      = Algebra.discr R ⇑bA ^ Fintype.card κ * Algebra.discr R ⇑bB ^ Fintype.card ι := by
  rw [Algebra.discr_def, traceMatrix_tensorProduct, Matrix.det_kronecker, Algebra.discr_def,
    Algebra.discr_def]

end General

section Counting

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A product weight is positive iff both factors are positive or both are negative. -/
theorem ncard_pos_mul (w₁ : ι → K) (w₂ : κ → K) :
    {p : ι × κ | 0 < w₁ p.1 * w₂ p.2}.ncard
      = {i | 0 < w₁ i}.ncard * {j | 0 < w₂ j}.ncard
        + {i | w₁ i < 0}.ncard * {j | w₂ j < 0}.ncard := by
  have hset : {p : ι × κ | 0 < w₁ p.1 * w₂ p.2}
      = ({i | 0 < w₁ i} ×ˢ {j | 0 < w₂ j}) ∪ ({i | w₁ i < 0} ×ˢ {j | w₂ j < 0}) := by
    ext ⟨i, j⟩
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, mul_pos_iff]
  have hdisj : Disjoint ({i | 0 < w₁ i} ×ˢ {j | 0 < w₂ j})
      ({i | w₁ i < 0} ×ˢ {j | w₂ j < 0}) := by
    rw [Set.disjoint_prod]
    left
    rw [Set.disjoint_left]
    intro i hi hi'
    exact lt_asymm hi hi'
  rw [hset, Set.ncard_union_eq hdisj, Set.ncard_prod, Set.ncard_prod]

/-- A product weight is negative iff the factors have opposite strict signs. -/
theorem ncard_neg_mul (w₁ : ι → K) (w₂ : κ → K) :
    {p : ι × κ | w₁ p.1 * w₂ p.2 < 0}.ncard
      = {i | 0 < w₁ i}.ncard * {j | w₂ j < 0}.ncard
        + {i | w₁ i < 0}.ncard * {j | 0 < w₂ j}.ncard := by
  have hset : {p : ι × κ | w₁ p.1 * w₂ p.2 < 0}
      = ({i | 0 < w₁ i} ×ˢ {j | w₂ j < 0}) ∪ ({i | w₁ i < 0} ×ˢ {j | 0 < w₂ j}) := by
    ext ⟨i, j⟩
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, mul_neg_iff]
  have hdisj : Disjoint ({i | 0 < w₁ i} ×ˢ {j | w₂ j < 0})
      ({i | w₁ i < 0} ×ˢ {j | 0 < w₂ j}) := by
    rw [Set.disjoint_prod]
    left
    rw [Set.disjoint_left]
    intro i hi hi'
    exact lt_asymm hi hi'
  rw [hset, Set.ncard_union_eq hdisj, Set.ncard_prod, Set.ncard_prod]

end Counting

section Signature

open QuadraticMap

variable {K V W : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The tensor product of two orthogonal families is orthogonal for the tensor product form. -/
theorem isOrthoᵢ_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W)
    {ι κ : Type*} {v : ι → V} {w : κ → W}
    (hv : (associated (R := K) Q₁).IsOrthoᵢ v) (hw : (associated (R := K) Q₂).IsOrthoᵢ w) :
    (associated (R := K) (Q₁.tmul Q₂)).IsOrthoᵢ (fun p : ι × κ => v p.1 ⊗ₜ w p.2) := by
  intro p q hpq
  show associated (R := K) (Q₁.tmul Q₂) (v p.1 ⊗ₜ w p.2) (v q.1 ⊗ₜ w q.2) = 0
  rw [QuadraticForm.associated_tmul, LinearMap.BilinForm.tensorDistrib_tmul]
  rcases ne_or_eq p.1 q.1 with h1 | h1
  · rw [hv h1, smul_zero]
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    rw [hw h2, zero_smul]

/-- The tensor product of two quadratic forms, in the tensor product of orthogonal bases, is the
weighted sum of squares with the product weights. -/
theorem tmul_equivalent_weightedSumSquares (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : Basis ι K V) (w : Basis κ K W)
    (hv : (associated (R := K) Q₁).IsOrthoᵢ v) (hw : (associated (R := K) Q₂).IsOrthoᵢ w) :
    Equivalent (Q₁.tmul Q₂)
      (weightedSumSquares K (fun p : ι × κ => Q₁ (v p.1) * Q₂ (w p.2))) := by
  have hb : (associated (R := K) (Q₁.tmul Q₂)).IsOrthoᵢ (v.tensorProduct w) := by
    intro p q hpq
    show associated (R := K) (Q₁.tmul Q₂) (v.tensorProduct w p) (v.tensorProduct w q) = 0
    rw [Basis.tensorProduct_apply', Basis.tensorProduct_apply']
    exact isOrthoᵢ_tmul Q₁ Q₂ hv hw hpq
  have hrepr : (Q₁.tmul Q₂).basisRepr (v.tensorProduct w)
      = weightedSumSquares K (fun p : ι × κ => Q₁ (v p.1) * Q₂ (w p.2)) := by
    rw [basisRepr_eq_of_iIsOrtho _ _ hb]
    congr 1
    funext p
    rw [Basis.tensorProduct_apply', QuadraticForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]
  refine ⟨?_⟩
  rw [← hrepr]
  exact isometryEquivBasisRepr (Q₁.tmul Q₂) (v.tensorProduct w)

variable [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- **The signature product rule, positive part**:
`p(Q₁ ⊗ Q₂) = p(Q₁) p(Q₂) + n(Q₁) n(Q₂)`. -/
theorem sigPos_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigPos (Q₁.tmul Q₂) = sigPos Q₁ * sigPos Q₂ + sigNeg Q₁ * sigNeg Q₂ := by
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm K Q₁)
  obtain ⟨w, hw⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm K Q₂)
  have e₁ : Equivalent Q₁ (weightedSumSquares K fun i => Q₁ (v i)) :=
    ⟨Q₁.isometryEquivWeightedSumSquares v hv⟩
  have e₂ : Equivalent Q₂ (weightedSumSquares K fun j => Q₂ (w j)) :=
    ⟨Q₂.isometryEquivWeightedSumSquares w hw⟩
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
      (tmul_equivalent_weightedSumSquares Q₁ Q₂ v w hv hw),
    QuadraticForm.sigPos_of_equiv_weightedSumSquares e₁,
    QuadraticForm.sigPos_of_equiv_weightedSumSquares e₂,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares e₁,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares e₂]
  exact ncard_pos_mul (fun i => Q₁ (v i)) (fun j => Q₂ (w j))

/-- **The signature product rule, negative part**:
`n(Q₁ ⊗ Q₂) = p(Q₁) n(Q₂) + n(Q₁) p(Q₂)`. -/
theorem sigNeg_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigNeg (Q₁.tmul Q₂) = sigPos Q₁ * sigNeg Q₂ + sigNeg Q₁ * sigPos Q₂ := by
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm K Q₁)
  obtain ⟨w, hw⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm K Q₂)
  have e₁ : Equivalent Q₁ (weightedSumSquares K fun i => Q₁ (v i)) :=
    ⟨Q₁.isometryEquivWeightedSumSquares v hv⟩
  have e₂ : Equivalent Q₂ (weightedSumSquares K fun j => Q₂ (w j)) :=
    ⟨Q₂.isometryEquivWeightedSumSquares w hw⟩
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
      (tmul_equivalent_weightedSumSquares Q₁ Q₂ v w hv hw),
    QuadraticForm.sigPos_of_equiv_weightedSumSquares e₁,
    QuadraticForm.sigPos_of_equiv_weightedSumSquares e₂,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares e₁,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares e₂]
  exact ncard_neg_mul (fun i => Q₁ (v i)) (fun j => Q₂ (w j))

end Signature

section TraceQuadratic

open QuadraticMap

variable {R : Type*} [CommRing R]

/-- The trace form is symmetric (in the form `associated_left_inverse` expects). -/
theorem traceForm_comm (S : Type*) [CommRing S] [Algebra R S] (x y : S) :
    Algebra.traceForm R S x y = Algebra.traceForm R S y x := by
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]

variable [Invertible (2 : R)] {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]

/-- **The trace quadratic form `x ↦ Tr(x²)` of `A ⊗ B` is the tensor product of the trace
quadratic forms of `A` and `B`.** -/
theorem qTrace_tensor :
    LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R (A ⊗[R] B))
      = QuadraticForm.tmul (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R A))
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R B)) := by
  have h : associated (R := R) (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R (A ⊗[R] B)))
      = associated (R := R) (QuadraticForm.tmul
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R A))
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R B))) := by
    rw [QuadraticForm.associated_tmul]
    rw [associated_left_inverse R (traceForm_comm (R := R) (A ⊗[R] B)),
      associated_left_inverse R (traceForm_comm (R := R) A),
      associated_left_inverse R (traceForm_comm (R := R) B)]
    apply TensorProduct.ext'
    intro a b
    apply TensorProduct.ext'
    intro a' b'
    rw [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, traceForm_tmul_general, mul_comm]
  calc LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R (A ⊗[R] B))
      = (associated (R := R)
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R (A ⊗[R] B)))).toQuadraticMap :=
        (toQuadraticMap_associated R _).symm
    _ = (associated (R := R) (QuadraticForm.tmul
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R A))
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R B)))).toQuadraticMap := by
        rw [h]
    _ = QuadraticForm.tmul (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R A))
          (LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm R B)) :=
        toQuadraticMap_associated R _

end TraceQuadratic

/-! ### The compositum as an instance

`PdtTraceCompositum` makes `AdjoinRoot fρ` and `AdjoinRoot fQ` fields, so a second (propositionally
equal, but syntactically different) `ℚ`-algebra structure `DivisionRing.toRatAlgebra` becomes
available; it is switched off here so that the statements match the earlier files. -/

attribute [-instance] DivisionRing.toRatAlgebra

section Instance

local instance : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero

theorem discr_bρ : Algebra.discr ℚ (⇑bρ) = -23 := by
  rw [Algebra.discr_def, traceMatrix_bρ, detMρ]

theorem discr_bQ : Algebra.discr ℚ (⇑bQ) = -283 := by
  rw [Algebra.discr_def, traceMatrix_bQ, det_M]

/-- The compositum discriminant `(−23)⁴ · (−283)³` as an instance of `discr_tensorProduct`. -/
theorem discr_bL_of_general : Algebra.discr ℚ (⇑bL) = (-23) ^ 4 * (-283) ^ 3 := by
  unfold bL
  rw [discr_tensorProduct, discr_bρ, discr_bQ, Fintype.card_fin, Fintype.card_fin]

/-- The trace quadratic form of the compositum is the tensor product of the two trace forms. -/
theorem qTraceL_eq_tmul : qTraceL = qTraceρ.tmul qTraceQ :=
  qTrace_tensor (R := ℚ) (A := AdjoinRoot fρ) (B := AdjoinRoot fQ)

/-- Signature `(7, 5)` of the compositum as an instance of the signature product rule:
`2·3 + 1·1 = 7`. -/
theorem sigPos_traceL_of_general : sigPos qTraceL = 7 := by
  have h := sigPos_tmul qTraceρ qTraceQ
  rw [sigPos_traceρ, sigPos_traceQ, sigNeg_traceρ, sigNeg_traceQ] at h
  rw [qTraceL_eq_tmul]
  exact h

/-- `2·1 + 1·3 = 5`. -/
theorem sigNeg_traceL_of_general : sigNeg qTraceL = 5 := by
  have h := sigNeg_tmul qTraceρ qTraceQ
  rw [sigPos_traceρ, sigPos_traceQ, sigNeg_traceρ, sigNeg_traceQ] at h
  rw [qTraceL_eq_tmul]
  exact h

end Instance

end PDT
