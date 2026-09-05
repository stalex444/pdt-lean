import Mathlib

/-!
# The Lüders rule: non-disturbance and the coherence characterization

Two classical theorems about the quantum measurement-update ("Lüders") rule,
formalized over `Matrix n n ℂ` in finite dimension.  Everything in this module is
generic quantum mechanics: **no PDT datum appears in any statement or proof.**

## Main results

* `PDT.Luders.ludersMap_fixed_iff_commute` — the finite-dimensional **generalized
  (unsharp) Lüders non-disturbance theorem** in its square-root form: for a
  family `A i` of Hermitian matrices with `∑ i, A i * A i = 1`, the Lüders map
  `L B = ∑ i, A i * B * A i` fixes `B` **iff** every `A i` commutes with `B`.
* `PDT.Luders.luders_fixed_iff_commute_effects` — the same theorem in the form
  stated by Arias–Gheondea–Gudder, *Fixed points of quantum operations*,
  J. Math. Phys. **43** (2002) 5872–5881, **Theorem 3.5(a)**: for effects `E i`
  (positive semidefinite, `∑ i, E i = 1`) and `A i = √(E i)`,
  `L B = B ↔ ∀ i, Commute (E i) B`.  In operator-algebra language: in finite
  dimension the fixed-point set of the Lüders operation is *exactly* the
  commutant of the effects.

## Scope riders (binding — these theorems are narrower than they look)

* **Non-disturbance, not uniqueness.**  `ludersMap_fixed_iff_commute` and
  `luders_fixed_iff_commute_effects` are *fixed-point* theorems.  They say which
  observables are undisturbed by a given Lüders measurement.  They do **not**
  say that the Lüders map is the only admissible state-update rule; nothing here
  licenses "the update *is* `Q ρ Q`".  (That is a separate theorem — see
  `coherence_forces_luders` below.)
* **Finite dimension is load-bearing, not a convenience.**  The implication
  `∑ᵢ Eᵢ^½ B Eᵢ^½ = B → B ∈ {Eᵢ}′` is **false** in general on an
  infinite-dimensional Hilbert space: Arias–Gheondea–Gudder 2002, Thm 4.2
  (five effects) and Liu–Wu, *On fixed points of Lüders operation*,
  J. Math. Phys. **50** (2009), Thm 1 (three effects) give counterexamples on
  `ℓ²(F₂)`.  Every known counterexample turns on non-injectivity of a von
  Neumann algebra, which cannot happen in finite dimension.  The `[Fintype n]`
  hypothesis below is therefore essential.
* **The historical attribution.**  Lüders (1951) *postulated* the update rule
  (his word: *Ansatz*) and proved a *commutation* characterization; he proved no
  uniqueness theorem.  Sudbery, arXiv:2402.15280, argues the rule is Dirac's
  (1930).  This module claims neither.

## Prior art (no novelty is claimed for the Lüders *map*)

The Lüders update *map* is already formalized elsewhere — as `density_collapse`
in the Isabelle/AFP entry `Projective_Measurements` (Echenim, 2021) and as
`POVM.measurementMap` / `POVM.measureForget` / `pinching_map` in Lean's
`physlib` and its ancestor `Lean-QuantumInfo` (Meiburg, Lessa).  What is
formalized here is the *theorems*, for which no prior formalization was found in
any proof assistant as of 2026-08-27.
-/

namespace PDT
namespace Luders

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ## The Lüders map -/

/-- **The generalized (unsharp) Lüders map** attached to a family of square
roots `A : ι → Matrix n n ℂ`: `L B = ∑ i, A i * B * A i`.  When
`A i = √(E i)` for a family of effects `E` summing to `1`, this is the
non-selective Lüders update of the associated measurement. -/
def ludersMap {ι n : Type*} [Fintype ι] [Fintype n]
    (A : ι → Matrix n n ℂ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, A i * B * A i

@[simp]
theorem ludersMap_apply {ι n : Type*} [Fintype ι] [Fintype n]
    (A : ι → Matrix n n ℂ) (B : Matrix n n ℂ) :
    ludersMap A B = ∑ i, A i * B * A i := rfl

/-! ## GATE 1 — the generalized Lüders non-disturbance theorem (AGG 3.5(a)) -/

/-- **The finite-dimensional generalized (unsharp) Lüders non-disturbance
theorem, square-root form.**  Let `A : ι → Matrix n n ℂ` be Hermitian with
`∑ i, A i * A i = 1`.  Then the Lüders map `L B = ∑ i, A i * B * A i` fixes `B`
if and only if every `A i` commutes with `B`.

This is Arias–Gheondea–Gudder 2002, Theorem 3.5(a), in the form in which their
Lemma 3.3 proves it; the commutation conclusion for the square roots `A i` is
stronger than the conclusion for the effects `A i * A i`.

Scope: this is a **non-disturbance / fixed-point** statement, not a uniqueness
theorem for the update map. -/
theorem ludersMap_fixed_iff_commute {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] (A : ι → Matrix n n ℂ) (hherm : ∀ i, (A i).IsHermitian)
    (hres : ∑ i, A i * A i = 1) (B : Matrix n n ℂ) :
    ludersMap A B = B ↔ ∀ i, Commute (A i) B := by
  constructor
  · -- (⇒) the Arias–Gheondea–Gudder trace argument
    intro hfix i
    -- the commutators
    have hCH : ∀ j, (B * A j - A j * B)ᴴ = A j * Bᴴ - Bᴴ * A j := by
      intro j
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, (hherm j).eq]
    -- termwise trace identity
    have hterm : ∀ j, ((B * A j - A j * B) * (B * A j - A j * B)ᴴ).trace
        = (Bᴴ * B * (A j * A j)).trace + (B * Bᴴ * (A j * A j)).trace
          - 2 * (Bᴴ * (A j * B * A j)).trace := by
      intro j
      rw [hCH j]
      have hexp : (B * A j - A j * B) * (A j * Bᴴ - Bᴴ * A j)
          = B * (A j * A j) * Bᴴ + A j * (B * Bᴴ) * A j
            - B * A j * (Bᴴ * A j) - A j * B * A j * Bᴴ := by
        noncomm_ring
      have e1 : (B * (A j * A j) * Bᴴ).trace = (Bᴴ * B * (A j * A j)).trace :=
        Matrix.trace_mul_cycle B (A j * A j) Bᴴ
      have e2 : (A j * (B * Bᴴ) * A j).trace = (B * Bᴴ * (A j * A j)).trace := by
        rw [Matrix.trace_mul_cycle (A j) (B * Bᴴ) (A j),
          Matrix.trace_mul_comm (A j * A j) (B * Bᴴ)]
      have e3 : (B * A j * (Bᴴ * A j)).trace = (Bᴴ * (A j * B * A j)).trace := by
        rw [Matrix.trace_mul_comm (B * A j) (Bᴴ * A j)]
        congr 1
        noncomm_ring
      have e4 : (A j * B * A j * Bᴴ).trace = (Bᴴ * (A j * B * A j)).trace :=
        Matrix.trace_mul_comm (A j * B * A j) Bᴴ
      rw [hexp, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_add, e1, e2, e3, e4]
      ring
    -- the three sums
    have h1 : ∑ j, (Bᴴ * B * (A j * A j)).trace = (Bᴴ * B).trace := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, hres, Matrix.mul_one]
    have h2 : ∑ j, (B * Bᴴ * (A j * A j)).trace = (B * Bᴴ).trace := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, hres, Matrix.mul_one]
    have hfix' : ∑ j, A j * B * A j = B := hfix
    have h3 : ∑ j, (Bᴴ * (A j * B * A j)).trace = (Bᴴ * B).trace := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, hfix']
    have h4 : (B * Bᴴ).trace = (Bᴴ * B).trace := Matrix.trace_mul_comm B Bᴴ
    -- the sum of the (nonnegative) traces vanishes
    have hsum0 : ∑ j, ((B * A j - A j * B) * (B * A j - A j * B)ᴴ).trace = 0 := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3, h4]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ ((B * A j - A j * B) * (B * A j - A j * B)ᴴ).trace :=
      fun j _ => (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
    have hzero : B * A i - A i * B = 0 :=
      Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (heach i (Finset.mem_univ i))
    exact (sub_eq_zero.mp hzero).symm
  · -- (⇐) trivial
    intro h
    have hstep : ∀ i, A i * B * A i = B * (A i * A i) := by
      intro i
      rw [(h i).eq, Matrix.mul_assoc]
    rw [ludersMap_apply, Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.mul_sum,
      hres, Matrix.mul_one]

/-- **The finite-dimensional generalized (unsharp) Lüders theorem, effect form**
— Arias–Gheondea–Gudder 2002, Theorem 3.5(a).  For a family of effects
`E : ι → Matrix n n ℂ` (positive semidefinite, `∑ i, E i = 1`), the Lüders map
`L B = ∑ i, √(E i) * B * √(E i)` fixes `B` **iff** `B` commutes with every
`E i`; i.e. the fixed-point set of the Lüders operation is exactly the commutant
of the effects.

`CFC.sqrt` is the positive square root supplied by the continuous functional
calculus; its positivity is what makes the reverse implication true (an
arbitrary Hermitian square root would not do: for `E = 1` and `A = diag(1,-1)`,
`A B A = B` fails for some `B` while `Commute 1 B` always holds).

Scope: **non-disturbance, not uniqueness**; and the `[Fintype n]` hypothesis is
essential (see the module docstring). -/
theorem luders_fixed_iff_commute_effects {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] (E : ι → Matrix n n ℂ) (hE : ∀ i, (E i).PosSemidef)
    (hres : ∑ i, E i = 1) (B : Matrix n n ℂ) :
    ludersMap (fun i => CFC.sqrt (E i)) B = B ↔ ∀ i, Commute (E i) B := by
  have hsq : ∀ i, CFC.sqrt (E i) * CFC.sqrt (E i) = E i := fun i =>
    CFC.sqrt_mul_sqrt_self (E i) (Matrix.nonneg_iff_posSemidef.mpr (hE i))
  have hherm : ∀ i, (CFC.sqrt (E i)).IsHermitian := fun i =>
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (E i))).isHermitian
  have hres' : ∑ i, CFC.sqrt (E i) * CFC.sqrt (E i) = 1 := by
    simp only [hsq]; exact hres
  rw [ludersMap_fixed_iff_commute (fun i => CFC.sqrt (E i)) hherm hres' B]
  constructor
  · intro h i
    have := (h i).mul_left (h i)
    rwa [hsq i] at this
  · intro h i
    have : Commute (cfcₙ NNReal.sqrt (E i)) B := (h i).cfcₙ_nnreal NNReal.sqrt
    exact this

/-! ## GATE 3 — elementary properties of the sharp Lüders update

These are stated first because Gate 2 uses `IsOrthProj` and `posSemidef_luders`. -/

/-- An **orthogonal projection**: a Hermitian idempotent.  (The second
component is definitionally `IsIdempotentElem M`; Mathlib at this pin has no
orthogonal-projection predicate for matrices.) -/
def IsOrthProj {n : Type*} [Fintype n] (M : Matrix n n ℂ) : Prop :=
  M.IsHermitian ∧ M * M = M

/-- The sharp Lüders update `ρ ↦ Q ρ Q` preserves positivity. -/
theorem posSemidef_luders {n : Type*} [Fintype n] [DecidableEq n]
    {Q ρ : Matrix n n ℂ} (hQ : IsOrthProj Q) (hρ : ρ.PosSemidef) :
    (Q * ρ * Q).PosSemidef := by
  have := hρ.conjTranspose_mul_mul_same Q
  rwa [hQ.1.eq] at this

/-- The sharp Lüders update is **trace preserving against the Born weight**:
`trace (Q ρ Q) = trace (Q ρ)`. -/
theorem trace_luders {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : IsOrthProj Q) (ρ : Matrix n n ℂ) :
    (Q * ρ * Q).trace = (Q * ρ).trace := by
  rw [Matrix.trace_mul_cycle Q ρ Q, hQ.2]

/-- The sharp Lüders update is **idempotent**: repeating the same measurement
changes nothing. -/
theorem luders_idem {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : IsOrthProj Q) (ρ : Matrix n n ℂ) :
    Q * (Q * ρ * Q) * Q = Q * ρ * Q := by
  calc Q * (Q * ρ * Q) * Q = Q * Q * ρ * (Q * Q) := by noncomm_ring
    _ = Q * ρ * Q := by rw [hQ.2]

/-- **The Lüders rule is coherent.**  If `P` is a subprojection of `Q`
(`P * Q = Q * P = P`), then a prior Lüders measurement of `Q` does not change
the Born statistics of `P`.  This is the *existence* half of Fiorentino &
Weigert's Theorem 1; `coherence_forces_luders` is the *uniqueness* half. -/
theorem luders_coherent {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hPQ : P * Q = P) (hQP : Q * P = P) (ρ : Matrix n n ℂ) :
    (P * (Q * ρ * Q)).trace = (P * ρ).trace := by
  have e1 : P * (Q * ρ * Q) = (P * Q * ρ) * Q := by noncomm_ring
  rw [e1, Matrix.trace_mul_comm]
  have e2 : Q * (P * Q * ρ) = (Q * P * Q) * ρ := by noncomm_ring
  rw [e2, hQP, hPQ]

/-! ## GATE 2 — the coherence characterization of the Lüders rule

**Fiorentino & Weigert, "Beyond the Projection Postulate and Back: Quantum
Theories with Generalised State-Update Rules", Phys. Rev. A 113, 012204 (2026),
Theorem 1** (the argument originates with Bell & Nauenberg, 1966).

MANDATORY SCOPE RIDER — **NON-COMPOSITE SYSTEMS ONLY.**
`coherence_forces_luders` below is the *single-system* theorem.  Fiorentino and
Weigert show explicitly that **coherence alone does NOT single out the
projection postulate for composite systems**; the composite case is their
*Theorem 2* (coherence **and** composition compatibility), which is **not**
formalized here.  Nothing in this module may be read as a statement about
composite systems, and in particular nothing here bears on any
bipartite/entanglement chain. -/

/-- `1 - Q` is an orthogonal projection when `Q` is. -/
theorem IsOrthProj.compl {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : IsOrthProj Q) : IsOrthProj (1 - Q) := by
  refine ⟨Matrix.isHermitian_one.sub hQ.1, ?_⟩
  have h : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
  rw [h, hQ.2]
  abel

/-- **Support lemma.**  A positive semidefinite matrix whose trace against the
complementary projection `1 - Q` vanishes is supported in the range of `Q`. -/
theorem support_of_trace_compl {n : Type*} [Fintype n] [DecidableEq n]
    {Q M : Matrix n n ℂ} (hQ : IsOrthProj Q) (hM : M.PosSemidef)
    (h : ((1 - Q) * M).trace = 0) : Q * M = M ∧ M * Q = M := by
  have hR : IsOrthProj (1 - Q) := hQ.compl
  have hS : CFC.sqrt M * CFC.sqrt M = M :=
    CFC.sqrt_mul_sqrt_self M (Matrix.nonneg_iff_posSemidef.mpr hM)
  have hSh : (CFC.sqrt M)ᴴ = CFC.sqrt M :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  have hcorner : ((1 - Q) * CFC.sqrt M) * ((1 - Q) * CFC.sqrt M)ᴴ
      = (1 - Q) * M * (1 - Q) := by
    rw [Matrix.conjTranspose_mul, hSh, hR.1.eq]
    calc ((1 - Q) * CFC.sqrt M) * (CFC.sqrt M * (1 - Q))
        = (1 - Q) * (CFC.sqrt M * CFC.sqrt M) * (1 - Q) := by noncomm_ring
      _ = (1 - Q) * M * (1 - Q) := by rw [hS]
  have htr : ((1 - Q) * M * (1 - Q)).trace = 0 := by
    rw [Matrix.trace_mul_cycle (1 - Q) M (1 - Q), hR.2]
    exact h
  have hzero : (1 - Q) * CFC.sqrt M = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (by rw [hcorner]; exact htr)
  have hRM : (1 - Q) * M = 0 := by
    rw [← hS, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
  have hMR : M * (1 - Q) = 0 := by
    have hh := congrArg Matrix.conjTranspose hRM
    rwa [Matrix.conjTranspose_mul, hM.isHermitian.eq, hR.1.eq,
      Matrix.conjTranspose_zero] at hh
  refine ⟨?_, ?_⟩
  · have h1 : M - Q * M = 0 := by rw [← hRM]; noncomm_ring
    exact (sub_eq_zero.mp h1).symm
  · have h2 : M - M * Q = 0 := by rw [← hMR]; noncomm_ring
    exact (sub_eq_zero.mp h2).symm

/-! ### Rank-one probes -/

/-- The outer product `x xᴴ` squares to `‖x‖² • x xᴴ`. -/
theorem outer_mul_outer {n : Type*} [Fintype n] (x : n → ℂ) :
    Matrix.vecMulVec x (star x) * Matrix.vecMulVec x (star x)
      = (star x ⬝ᵥ x) • Matrix.vecMulVec x (star x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.star_apply, dotProduct]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- If `Q` is Hermitian and fixes `x`, then `x xᴴ Q = x xᴴ`. -/
theorem outer_mul_right {n : Type*} [Fintype n] (x : n → ℂ) (Q : Matrix n n ℂ)
    (hQ : Q.IsHermitian) (hx : Q *ᵥ x = x) :
    Matrix.vecMulVec x (star x) * Q = Matrix.vecMulVec x (star x) := by
  have hQstar : ∀ a b, star (Q a b) = Q b a := by
    intro a b
    have hh := congr_fun (congr_fun hQ.eq b) a
    rwa [Matrix.conjTranspose_apply] at hh
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have hrow : (∑ k, Q j k * x k) = x j := by
    have hh := congr_fun hx j
    simpa [Matrix.mulVec, dotProduct] using hh
  calc ∑ k, x i * star (x k) * Q k j
      = ∑ k, x i * star (Q j k * x k) :=
        Finset.sum_congr rfl fun k _ => by rw [star_mul, hQstar j k]; ring
    _ = x i * star (∑ k, Q j k * x k) := by rw [← Finset.mul_sum, ← star_sum]
    _ = x i * star (x j) := by rw [hrow]

/-- If `Q` fixes `x`, then `Q x xᴴ = x xᴴ`. -/
theorem outer_mul_left {n : Type*} [Fintype n] (x : n → ℂ) (Q : Matrix n n ℂ)
    (hx : Q *ᵥ x = x) :
    Q * Matrix.vecMulVec x (star x) = Matrix.vecMulVec x (star x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have hrow : (∑ k, Q i k * x k) = x i := by
    have hh := congr_fun hx i
    simpa [Matrix.mulVec, dotProduct] using hh
  calc ∑ k, Q i k * (x k * star (x j))
      = (∑ k, Q i k * x k) * star (x j) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = x i * star (x j) := by rw [hrow]

/-- The quadratic form as a trace against the rank-one matrix `x xᴴ`. -/
theorem dotProduct_eq_trace {n : Type*} [Fintype n] (X : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (X *ᵥ x) = (X * Matrix.vecMulVec x (star x)).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- Conjugation identity for quadratic forms. -/
theorem quad_conj {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ) :
    star (N *ᵥ v) ⬝ᵥ (M *ᵥ (N *ᵥ v)) = star v ⬝ᵥ ((Nᴴ * M * N) *ᵥ v) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Probe lemma, range case.**  If the trace of `D` against every
subprojection of `Q` vanishes, then the quadratic form of `D` vanishes on every
vector fixed by `Q`. -/
theorem quad_zero_of_fixed {n : Type*} [Fintype n] [DecidableEq n]
    {Q D : Matrix n n ℂ} (hQ : IsOrthProj Q)
    (hsub : ∀ P : Matrix n n ℂ, IsOrthProj P → P * Q = P → Q * P = P → (P * D).trace = 0)
    (x : n → ℂ) (hQx : Q *ᵥ x = x) : star x ⬝ᵥ (D *ᵥ x) = 0 := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have hcnn : (0 : ℂ) ≤ star x ⬝ᵥ x := _root_.dotProduct_star_self_nonneg x
    have hcsa : star (star x ⬝ᵥ x) = star x ⬝ᵥ x :=
      (IsSelfAdjoint.of_nonneg hcnn).star_eq
    have hcinv : star ((star x ⬝ᵥ x)⁻¹) = (star x ⬝ᵥ x)⁻¹ := by
      rw [star_inv₀, hcsa]
    have hc : star x ⬝ᵥ x ≠ 0 :=
      fun hh => hx0 (_root_.dotProduct_star_self_eq_zero.mp hh)
    obtain ⟨P, hPdef⟩ : ∃ P : Matrix n n ℂ,
        P = (star x ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x (star x) := ⟨_, rfl⟩
    have hWh : (Matrix.vecMulVec x (star x)).IsHermitian :=
      (Matrix.posSemidef_vecMulVec_self_star x).isHermitian
    have hPh : P.IsHermitian := by
      show Pᴴ = P
      rw [hPdef, Matrix.conjTranspose_smul, hWh.eq, hcinv]
    have hPP : P * P = P := by
      rw [hPdef, Matrix.smul_mul, Matrix.mul_smul, outer_mul_outer, smul_smul, smul_smul]
      congr 1
      field_simp
    have hPQ : P * Q = P := by
      rw [hPdef, Matrix.smul_mul, outer_mul_right x Q hQ.1 hQx]
    have hQP : Q * P = P := by
      rw [hPdef, Matrix.mul_smul, outer_mul_left x Q hQx]
    have h0 := hsub P ⟨hPh, hPP⟩ hPQ hQP
    rw [hPdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h0
    have htr0 : (Matrix.vecMulVec x (star x) * D).trace = 0 := by
      rcases mul_eq_zero.mp h0 with hh | hh
      · exact absurd hh (inv_ne_zero hc)
      · exact hh
    rw [dotProduct_eq_trace D x, Matrix.trace_mul_comm]
    exact htr0

/-- **The coherence characterization of the Lüders rule** — Fiorentino &
Weigert, Phys. Rev. A **113**, 012204 (2026), **Theorem 1**.

Let `ω` assign to each orthogonal projection `Q` and each positive semidefinite
`ρ` a positive semidefinite post-measurement operator `ω Q ρ`, subject to

* **(Born)** `trace (ω Q ρ) = trace (Q * ρ)`, and
* **(coherence)** `trace (P * ω Q ρ) = trace (P * ρ)` for every orthogonal
  projection `P` with `P * Q = P` and `Q * P = P` — i.e. a prior measurement of
  `Q` does not disturb the statistics of any refinement of `Q`.

Then `ω` **is** the Lüders rule: `ω Q ρ = Q * ρ * Q`.

No linearity, no complete positivity and no Kraus form is assumed of `ω`; that
is what makes the theorem a derivation of the projection postulate rather than a
normalization of one.  Nor is any normalization assumed of the input: `ρ` ranges
over *all* positive semidefinite matrices, not only unit-trace ones, so the
1-homogeneity condition of Fiorentino & Weigert's Definition 1 is not needed
here.

**SCOPE RIDER (binding): NON-COMPOSITE SYSTEMS ONLY.**  Coherence alone does
*not* single out the projection postulate for composite systems — that is
Fiorentino & Weigert's Theorem 2 (coherence **and** composition compatibility),
which is not formalized here.  This theorem must never be quoted for a
bipartite/entangled setting. -/
theorem coherence_forces_luders {n : Type*} [Fintype n] [DecidableEq n]
    (ω : Matrix n n ℂ → Matrix n n ℂ → Matrix n n ℂ)
    (hpos : ∀ Q ρ, IsOrthProj Q → ρ.PosSemidef → (ω Q ρ).PosSemidef)
    (hborn : ∀ Q ρ, IsOrthProj Q → ρ.PosSemidef → (ω Q ρ).trace = (Q * ρ).trace)
    (hcoh : ∀ P Q ρ, IsOrthProj P → IsOrthProj Q → ρ.PosSemidef →
      P * Q = P → Q * P = P → (P * ω Q ρ).trace = (P * ρ).trace)
    (Q ρ : Matrix n n ℂ) (hQ : IsOrthProj Q) (hρ : ρ.PosSemidef) :
    ω Q ρ = Q * ρ * Q := by
  have hσ : (ω Q ρ).PosSemidef := hpos Q ρ hQ hρ
  have hτ : (Q * ρ * Q).PosSemidef := posSemidef_luders hQ hρ
  -- (1) `ω Q ρ` is supported in the range of `Q`
  have hQσ : ((1 - Q) * ω Q ρ).trace = 0 := by
    have hc := hcoh Q Q ρ hQ hQ hρ hQ.2 hQ.2
    have hb := hborn Q ρ hQ hρ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hb, hc, sub_self]
  obtain ⟨hσQ1, hσQ2⟩ := support_of_trace_compl hQ hσ hQσ
  -- (2) so is `Q ρ Q`, trivially
  have hτQ1 : Q * (Q * ρ * Q) = Q * ρ * Q := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ.2]
  have hτQ2 : (Q * ρ * Q) * Q = Q * ρ * Q := by
    rw [Matrix.mul_assoc, hQ.2]
  -- (3) the difference is Hermitian, supported in the range of `Q`, and has
  --     vanishing trace against every subprojection of `Q`
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix n n ℂ, D = ω Q ρ - Q * ρ * Q := ⟨_, rfl⟩
  have hDh : D.IsHermitian := by
    rw [hDdef]; exact hσ.isHermitian.sub hτ.isHermitian
  have hQD : Q * D = D := by rw [hDdef, Matrix.mul_sub, hσQ1, hτQ1]
  have hDQ : D * Q = D := by rw [hDdef, Matrix.sub_mul, hσQ2, hτQ2]
  have hsub : ∀ P : Matrix n n ℂ, IsOrthProj P → P * Q = P → Q * P = P →
      (P * D).trace = 0 := by
    intro P hP hPQ hQP
    have h1 : (P * ω Q ρ).trace = (P * ρ).trace := hcoh P Q ρ hP hQ hρ hPQ hQP
    have h2 : (P * (Q * ρ * Q)).trace = (P * ρ).trace := luders_coherent hPQ hQP ρ
    rw [hDdef, Matrix.mul_sub, Matrix.trace_sub, h1, h2, sub_self]
  -- (4) the quadratic form of `D` vanishes identically
  have hconj : Qᴴ * D * Q = D := by rw [hQ.1.eq, hQD, hDQ]
  have hquad : ∀ y : n → ℂ, star y ⬝ᵥ (D *ᵥ y) = 0 := by
    intro y
    have hQx : Q *ᵥ (Q *ᵥ y) = Q *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hQ.2]
    have hz := quad_zero_of_fixed hQ hsub (Q *ᵥ y) hQx
    rw [quad_conj D Q y, hconj] at hz
    exact hz
  -- (5) hence `D = 0`
  have hDpsd : D.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDh fun y => by rw [hquad y]
  have hDneg : (-D).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hDh.neg fun y => by
      rw [Matrix.neg_mulVec, dotProduct_neg, hquad y, neg_zero]
  have ht : D.trace = 0 := by
    have h1 : (0 : ℂ) ≤ D.trace := hDpsd.trace_nonneg
    have h2 : (0 : ℂ) ≤ (-D).trace := hDneg.trace_nonneg
    rw [Matrix.trace_neg] at h2
    exact le_antisymm (neg_nonneg.mp h2) h1
  have hD0 : D = 0 := hDpsd.trace_eq_zero_iff.mp ht
  rw [hDdef] at hD0
  exact sub_eq_zero.mp hD0

/-- **Non-vacuity of `coherence_forces_luders`.**  The Lüders rule
`ω Q ρ = Q ρ Q` does satisfy positivity, Born consistency and coherence, so the
hypothesis set of the uniqueness theorem is satisfiable — the uniqueness
statement is not vacuously true.

Note what is *not* claimed: no global `∃!` over update rules, because the
hypotheses constrain `ω Q ρ` only for `Q` an orthogonal projection and `ρ`
positive semidefinite, and leave `ω` entirely free off that domain.  Uniqueness
holds exactly on the domain, which is what `coherence_forces_luders` states.

Scope rider as above: **non-composite systems only**. -/
theorem exists_coherent_update {n : Type*} [Fintype n] [DecidableEq n] :
    ∃ ω : Matrix n n ℂ → Matrix n n ℂ → Matrix n n ℂ,
      (∀ Q ρ, IsOrthProj Q → ρ.PosSemidef → (ω Q ρ).PosSemidef) ∧
      (∀ Q ρ, IsOrthProj Q → ρ.PosSemidef → (ω Q ρ).trace = (Q * ρ).trace) ∧
      (∀ P Q ρ, IsOrthProj P → IsOrthProj Q → ρ.PosSemidef →
        P * Q = P → Q * P = P → (P * ω Q ρ).trace = (P * ρ).trace) := by
  refine ⟨fun Q ρ => Q * ρ * Q, ?_, ?_, ?_⟩
  · intro Q ρ hQ hρ
    exact posSemidef_luders hQ hρ
  · intro Q ρ hQ _
    exact trace_luders hQ ρ
  · intro P Q ρ _ _ _ hPQ hQP
    exact luders_coherent hPQ hQP ρ


end Luders
end PDT

#print axioms PDT.Luders.ludersMap_fixed_iff_commute
#print axioms PDT.Luders.luders_fixed_iff_commute_effects
#print axioms PDT.Luders.posSemidef_luders
#print axioms PDT.Luders.trace_luders
#print axioms PDT.Luders.luders_idem
#print axioms PDT.Luders.IsOrthProj.compl
#print axioms PDT.Luders.support_of_trace_compl
#print axioms PDT.Luders.quad_zero_of_fixed
#print axioms PDT.Luders.ludersMap_apply
#print axioms PDT.Luders.luders_coherent
#print axioms PDT.Luders.outer_mul_outer
#print axioms PDT.Luders.outer_mul_right
#print axioms PDT.Luders.outer_mul_left
#print axioms PDT.Luders.dotProduct_eq_trace
#print axioms PDT.Luders.quad_conj
#print axioms PDT.Luders.coherence_forces_luders
#print axioms PDT.Luders.exists_coherent_update
