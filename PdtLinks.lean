import PdtNorm
import PdtDiscriminant
import PdtTraceForm
import PdtSignature
import PdtSignatureRho
import PdtIrreducible

/-!
# Cross-module identification lemmas (dissolving the import islands)

Each `Pdt*.lean` file re-declares "the same" polynomial / matrix / algebra as a
private duplicate, linked to its twins only by matching literals. This module
imports the relevant files and states **kernel-checked** identity lemmas linking
the duplicated objects, so "the same object" is a proved statement, not an
observation about matching source text.

Every lemma here is `rfl`-level (the duplicate bodies are syntactically
identical) or an application of an existing genuine-API theorem.

No `sorry`, no `native_decide`; axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`.
-/

namespace PDT

open Polynomial AdjoinRoot Algebra

/-! ## Polynomial identifications

The quartic `X⁴ − X − 1` and cubic `X³ − X − 1` over `ℚ` are declared separately
in `PdtNorm` (`fQ`, `fρ`), `PdtDiscriminant` (`fq`, `fc`) and `PdtTraceForm`
(`f4`). All bodies are syntactically identical, so each bridge is `rfl`. -/

/-- The quartic of `PdtDiscriminant` is the quartic of `PdtNorm`. -/
theorem fq_eq_fQ : PDT.fq = PDT.fQ := rfl

/-- The cubic of `PdtDiscriminant` is the cubic of `PdtNorm`. -/
theorem fc_eq_fρ : PDT.fc = PDT.fρ := rfl

/-- The quartic abbrev of `PdtTraceForm` is the quartic of `PdtNorm`. -/
theorem f4_eq_fQ : PDT.f4 = PDT.fQ := rfl

/-- The quartic abbrev of `PdtTraceForm` is the quartic of `PdtDiscriminant`. -/
theorem f4_eq_fq : PDT.f4 = PDT.fq := rfl

/-! ## Quartic Gram-matrix identification

`PdtSignature.M` (the hand-written matrix analysed by the signature certificate)
and `PdtTraceForm.M4` (proved equal to the genuine `Algebra.traceForm` Gram
matrix, entrywise) are byte-identical literals, so `M = M4` is `rfl`. -/

/-- **The hand-written signature matrix IS the genuine trace-form Gram matrix.**
`PdtSignature.M` and `PdtTraceForm.M4` are literally equal; `M4` is proved
entrywise equal to `Algebra.traceForm` on the power basis in `PdtTraceForm`
(`traceForm_eq_M4`), so the `(3,1)`-signature certificate analyses the genuine
trace form. -/
theorem M_eq_M4 : PDT.M = PDT.M4 := rfl

/-- Consequence of `M_eq_M4`: each entry of the hand-written signature matrix `M`
equals the corresponding `Algebra.traceForm` Gram entry on the power basis of
`ℚ[x]/(x⁴−x−1)`. This is what makes `signature_3_1` a statement about the
genuine trace form. -/
theorem M_entry_eq_traceForm (i j : Fin 4) :
    PDT.M i j = Algebra.traceForm ℚ (AdjoinRoot PDT.f4) (PDT.pb4.basis (PDT.ι i)) (PDT.pb4.basis (PDT.ι j)) := by
  rw [M_eq_M4]; exact (PDT.traceForm_eq_M4 i j).symm

/-! ## Cubic Gram-matrix identification

`PdtSignatureRho.Mρ` (the hand-written cubic matrix analysed by the `(2,1)`
certificate) is byte-identical to the RHS of `PdtDiscriminant.traceMatrix_fin3`,
which is proved equal to the genuine `Algebra.traceMatrix` on the cubic power
basis. -/

/-- **The hand-written cubic signature matrix IS the genuine trace-form Gram
matrix** computed via `Algebra.traceMatrix` in `PdtDiscriminant`
(`traceMatrix_fin3`). -/
theorem Mρ_eq_traceMatrix_fin3 :
    PDT.Mρ = Algebra.traceMatrix ℚ
      ((powerBasis' PDT.fc_monic).basis ∘ (finCongr PDT.pdim).symm) :=
  PDT.traceMatrix_fin3.symm

/-! ## Irreducibility → fieldness at the `AdjoinRoot` sites

`PdtIrreducible` proves irreducibility over `ℚ` on raw literals; these `Fact`
instances re-anchor those proofs on `PdtNorm.fQ` / `PdtNorm.fρ`, so
`AdjoinRoot fQ` / `AdjoinRoot fρ` resolve as genuine `Field`s. -/

instance factIrreducible_fQ : Fact (Irreducible PDT.fQ) :=
  ⟨by simpa only [PDT.fQ] using PDT.quarticQ_irreducible⟩

instance factIrreducible_fρ : Fact (Irreducible PDT.fρ) :=
  ⟨by simpa only [PDT.fρ] using PDT.cubicQ_irreducible⟩

/-- With the `Fact (Irreducible fQ)` instance in scope, `AdjoinRoot fQ` is a field. -/
noncomputable example : Field (AdjoinRoot PDT.fQ) := inferInstance

/-- With the `Fact (Irreducible fρ)` instance in scope, `AdjoinRoot fρ` is a field. -/
noncomputable example : Field (AdjoinRoot PDT.fρ) := inferInstance

end PDT
