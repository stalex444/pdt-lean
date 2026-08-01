/-
PdtStabilizer.lean — THE STABILIZER IDENTITY (general N).

Setting: V = Fin N → ℚ, gl = Matrix (Fin N) (Fin N) ℚ,
sl N = trace-zero matrices = ker (Matrix.traceLinearMap).

For v ≠ 0 and N ≥ 2:
  (1) `slAction_surjective`  — X ↦ X *ᵥ v from sl N surjects onto V;
  (2) `finrank_stabilizer`   — the stabilizer (kernel in sl N) has
                               finrank N² − N − 1 (rank–nullity);
  (3) `finrank_glStabilizer` — the full gl-stabilizer has finrank N² − N;
      `stabilizer_corank_one`— the sl-stabilizer has corank 1 inside it;
      `exists_traceOne_mem_glStabilizer` — the difference IS the trace
                               character: the gl-stabilizer contains a
                               trace-1 element;
      `stabilizer_map_subtype` — the sl-stabilizer is exactly
                               sl N ⊓ (gl-stabilizer);
  (4) `finrank_sl_eq_add`    — dim sl(N) = N + (N² − N − 1)  (bonus).

Concrete instantiations: N = 4 (dim 11), N = 5 (dim 19), N = 15 (dim 209).

Pure mathematics; no physics claims. Zero sorries intended.
-/
import Mathlib

open Module LinearMap
open scoped Matrix

namespace PdtStabilizer

variable {N : ℕ}

/-! ### Definitions -/

/-- The action map `X ↦ X *ᵥ v` of `gl(N, ℚ)` on `ℚ^N`, linear in `X`. -/
def actionMap (v : Fin N → ℚ) : Matrix (Fin N) (Fin N) ℚ →ₗ[ℚ] (Fin N → ℚ) where
  toFun X := X *ᵥ v
  map_add' X Y := Matrix.add_mulVec X Y v
  map_smul' c X := Matrix.smul_mulVec c X v

@[simp] lemma actionMap_apply (v : Fin N → ℚ) (X : Matrix (Fin N) (Fin N) ℚ) :
    actionMap v X = X *ᵥ v := rfl

/-- The trace-zero subalgebra `sl(N, ℚ)` as a submodule of the matrix space. -/
def sl (N : ℕ) : Submodule ℚ (Matrix (Fin N) (Fin N) ℚ) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin N) ℚ ℚ)

@[simp] lemma mem_sl {X : Matrix (Fin N) (Fin N) ℚ} : X ∈ sl N ↔ X.trace = 0 := by
  simp [sl, LinearMap.mem_ker]

/-- The action map restricted to the trace-zero matrices. -/
def slAction (v : Fin N → ℚ) : sl N →ₗ[ℚ] (Fin N → ℚ) :=
  (actionMap v).comp (sl N).subtype

@[simp] lemma slAction_apply (v : Fin N → ℚ) (X : sl N) :
    slAction v X = (X : Matrix (Fin N) (Fin N) ℚ) *ᵥ v := rfl

/-- The stabilizer subalgebra of `v` inside `sl N`: the kernel of the restricted
action map. -/
def stabilizer (v : Fin N → ℚ) : Submodule ℚ (sl N) :=
  LinearMap.ker (slAction v)

/-! ### Explicit solvers (the constructive heart of surjectivity) -/

section Solvers

variable (v w : Fin N → ℚ) (i j : Fin N)

/-- The matrix supported on column `i` with entries `w k / v i`; it sends `v` to `w`. -/
def colSolve : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun k l => if l = i then w k / v i else 0

lemma colSolve_mulVec (hi : v i ≠ 0) : colSolve v w i *ᵥ v = w := by
  funext k
  simp only [colSolve, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact div_mul_cancel₀ (w k) hi

lemma trace_colSolve : (colSolve v w i).trace = w i / v i := by
  simp only [colSolve, Matrix.trace, Matrix.diag, Matrix.of_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- A matrix that annihilates `v` (rows supported on row `j`) but has trace `1`
when `j ≠ i` and `v i ≠ 0`. This witness IS the trace character's nonvanishing
on the full `gl` stabilizer. -/
def traceFixer : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.single j j 1 - Matrix.single j i (v j / v i)

lemma traceFixer_mulVec (hi : v i ≠ 0) : traceFixer v i j *ᵥ v = 0 := by
  rw [traceFixer, Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec, one_mul,
    div_mul_cancel₀ _ hi, sub_self]

lemma trace_traceFixer (hij : j ≠ i) : (traceFixer v i j).trace = 1 := by
  rw [traceFixer, Matrix.trace_sub, Matrix.trace_single_eq_same,
    Matrix.trace_single_eq_of_ne _ _ _ hij, sub_zero]

/-- The trace-zero solver: sends `v` to `w` and has trace `0`. -/
def slSolve : Matrix (Fin N) (Fin N) ℚ :=
  colSolve v w i - (w i / v i) • traceFixer v i j

lemma slSolve_mulVec (hi : v i ≠ 0) : slSolve v w i j *ᵥ v = w := by
  rw [slSolve, Matrix.sub_mulVec, Matrix.smul_mulVec, colSolve_mulVec v w i hi,
    traceFixer_mulVec v i j hi, smul_zero, sub_zero]

lemma trace_slSolve (hij : j ≠ i) : (slSolve v w i j).trace = 0 := by
  rw [slSolve, Matrix.trace_sub, Matrix.trace_smul, trace_colSolve,
    trace_traceFixer v i j hij, smul_eq_mul, mul_one, sub_self]

end Solvers

/-! ### (1) Surjectivity -/

/-- The unrestricted (`gl`) action map is surjective for `v ≠ 0`. -/
theorem actionMap_surjective {v : Fin N → ℚ} (hv : v ≠ 0) :
    Function.Surjective (actionMap v) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  intro w
  exact ⟨colSolve v w i, colSolve_mulVec v w i hi⟩

/-- **Surjectivity.** For `N ≥ 2` and `v ≠ 0`, the map `X ↦ X *ᵥ v` from the
trace-zero matrices `sl N` surjects onto all of `ℚ^N`. -/
theorem slAction_surjective (hN : 2 ≤ N) {v : Fin N → ℚ} (hv : v ≠ 0) :
    Function.Surjective (slAction v) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_fin]; omega) i
  intro w
  refine ⟨⟨slSolve v w i j, mem_sl.mpr (trace_slSolve v w i j hj)⟩, ?_⟩
  simpa using slSolve_mulVec v w i j hi

/-! ### Dimension bookkeeping (linear-arithmetic helpers, kept fully linear
so `omega` applies; `N²` enters only as an opaque atom `M`) -/

private lemma nat_sub₁ (M K : ℕ) (h : 1 + K = M) : K = M - 1 := by omega

private lemma nat_sub₂ (M K n : ℕ) (hle : n + 1 ≤ M) (h : n + K = M - 1) :
    K = M - n - 1 := by omega

private lemma nat_sub₃ (M K n : ℕ) (h : n + K = M) : K = M - n := by omega

private lemma nat_sub₄ (M n : ℕ) (h : n + 1 ≤ M) : M - n - 1 + 1 = M - n := by omega

private lemma nat_sub₅ (M n : ℕ) (h : n + 1 ≤ M) : M - 1 = n + (M - n - 1) := by omega

lemma aux_le (hN : 2 ≤ N) : N + 1 ≤ N ^ 2 := by
  rw [pow_two]
  calc N + 1 ≤ 2 * N := by omega
    _ ≤ N * N := Nat.mul_le_mul hN (le_refl N)

/-! ### Ambient dimensions -/

lemma finrank_gl : finrank ℚ (Matrix (Fin N) (Fin N) ℚ) = N * N := by
  rw [Module.finrank_matrix]
  simp [Fintype.card_fin]

/-- The trace functional is surjective (`N ≥ 2` suffices; `N ≥ 1` is what is used). -/
lemma traceLinearMap_surjective (hN : 2 ≤ N) :
    Function.Surjective (Matrix.traceLinearMap (Fin N) ℚ ℚ) := by
  intro c
  have hNe : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨(c / (N : ℚ)) • (1 : Matrix (Fin N) (Fin N) ℚ), ?_⟩
  rw [Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  exact div_mul_cancel₀ c hNe

/-- `dim sl(N) = N² − 1` — rank–nullity applied to the trace character. -/
theorem finrank_sl (hN : 2 ≤ N) : finrank ℚ (sl N) = N ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin N) ℚ ℚ)
  rw [LinearMap.range_eq_top.mpr (traceLinearMap_surjective hN), finrank_top,
    Module.finrank_self, finrank_gl] at h
  unfold sl
  rw [pow_two]
  exact nat_sub₁ (N * N) _ h

/-! ### (2) The stabilizer identity: finrank = N² − N − 1 -/

/-- **The stabilizer identity.** For `N ≥ 2` and `v ≠ 0`, the stabilizer
subalgebra `{X ∈ sl N | X *ᵥ v = 0}` has dimension `N² − N − 1`.
Proof: rank–nullity for `slAction v` on `sl N`, whose range is everything
by `slAction_surjective`. -/
theorem finrank_stabilizer (hN : 2 ≤ N) {v : Fin N → ℚ} (hv : v ≠ 0) :
    finrank ℚ (stabilizer v) = N ^ 2 - N - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (slAction v)
  rw [LinearMap.range_eq_top.mpr (slAction_surjective hN hv), finrank_top,
    Module.finrank_pi, Fintype.card_fin, finrank_sl hN] at h
  unfold stabilizer
  exact nat_sub₂ (N ^ 2) _ N (aux_le hN) h

/-! ### (3) Corank 1 against the full gl-stabilizer; the difference is the
trace character -/

/-- The full `gl` stabilizer `{X ∈ gl(N) | X *ᵥ v = 0}` has dimension `N² − N`. -/
theorem finrank_glStabilizer {v : Fin N → ℚ} (hv : v ≠ 0) :
    finrank ℚ (LinearMap.ker (actionMap v)) = N ^ 2 - N := by
  have h := LinearMap.finrank_range_add_finrank_ker (actionMap v)
  rw [LinearMap.range_eq_top.mpr (actionMap_surjective hv), finrank_top,
    Module.finrank_pi, Fintype.card_fin, finrank_gl] at h
  rw [pow_two]
  exact nat_sub₃ (N * N) _ N h

/-- **Corank 1.** The sl-stabilizer sits inside the gl-stabilizer with
codimension exactly 1: `(N² − N − 1) + 1 = N² − N`. -/
theorem stabilizer_corank_one (hN : 2 ≤ N) {v : Fin N → ℚ} (hv : v ≠ 0) :
    finrank ℚ (stabilizer v) + 1 = finrank ℚ (LinearMap.ker (actionMap v)) := by
  rw [finrank_stabilizer hN hv, finrank_glStabilizer hv]
  exact nat_sub₄ (N ^ 2) N (aux_le hN)

/-- The missing dimension IS the trace character: the gl-stabilizer contains an
element of trace `1` (the explicit witness `traceFixer`), so the trace
functional does not vanish on it — which is exactly why intersecting with
`sl N` costs one dimension. -/
theorem exists_traceOne_mem_glStabilizer (hN : 2 ≤ N) {v : Fin N → ℚ} (hv : v ≠ 0) :
    ∃ Y ∈ LinearMap.ker (actionMap v), Matrix.trace Y = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [Fintype.card_fin]; omega) i
  refine ⟨traceFixer v i j, ?_, trace_traceFixer v i j hj⟩
  rw [LinearMap.mem_ker, actionMap_apply]
  exact traceFixer_mulVec v i j hi

/-- Structurally, the sl-stabilizer (pushed into the matrix space) is exactly
the intersection of `sl N` with the full gl-stabilizer. -/
theorem stabilizer_map_subtype (v : Fin N → ℚ) :
    (stabilizer v).map (sl N).subtype = sl N ⊓ LinearMap.ker (actionMap v) := by
  unfold stabilizer slAction
  rw [LinearMap.ker_comp, Submodule.map_comap_subtype]

/-! ### (4) Bonus: `dim sl(N) = N + (N² − N − 1)` -/

/-- The moving directions (`N` of them, by surjectivity) plus the stabilizer
(`N² − N − 1`) exhaust `sl(N)`: `N² − 1 = N + (N² − N − 1)`. -/
theorem finrank_sl_eq_add (hN : 2 ≤ N) : finrank ℚ (sl N) = N + (N ^ 2 - N - 1) := by
  rw [finrank_sl hN]
  exact nat_sub₅ (N ^ 2) N (aux_le hN)

/-! ### Concrete instantiations: N = 4, 5, 15 -/

theorem finrank_stabilizer_four {v : Fin 4 → ℚ} (hv : v ≠ 0) :
    finrank ℚ (stabilizer v) = 11 := by
  have h := finrank_stabilizer (by norm_num) hv
  norm_num at h
  exact h

theorem finrank_stabilizer_five {v : Fin 5 → ℚ} (hv : v ≠ 0) :
    finrank ℚ (stabilizer v) = 19 := by
  have h := finrank_stabilizer (by norm_num) hv
  norm_num at h
  exact h

theorem finrank_stabilizer_fifteen {v : Fin 15 → ℚ} (hv : v ≠ 0) :
    finrank ℚ (stabilizer v) = 209 := by
  have h := finrank_stabilizer (by norm_num) hv
  norm_num at h
  exact h

theorem finrank_sl_four : finrank ℚ (sl 4) = 15 := by
  have h := finrank_sl (N := 4) (by norm_num)
  norm_num at h
  exact h

end PdtStabilizer

/-! ### Axiom audit -/

#print axioms PdtStabilizer.slAction_surjective
#print axioms PdtStabilizer.finrank_stabilizer
#print axioms PdtStabilizer.finrank_glStabilizer
#print axioms PdtStabilizer.stabilizer_corank_one
#print axioms PdtStabilizer.exists_traceOne_mem_glStabilizer
#print axioms PdtStabilizer.stabilizer_map_subtype
#print axioms PdtStabilizer.finrank_sl_eq_add
#print axioms PdtStabilizer.finrank_stabilizer_four
#print axioms PdtStabilizer.finrank_stabilizer_five
#print axioms PdtStabilizer.finrank_stabilizer_fifteen
