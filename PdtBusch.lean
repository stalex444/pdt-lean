/-
PdtBusch — Busch's theorem, finite dimension.

Busch (2003): a nonnegative, additive, normalized frame function on the
effects of a finite-dimensional complex matrix algebra is represented by
a unique density matrix. Born-rule uniqueness in the POVM reading, valid
in every finite dimension (the statement assumes only `[Nonempty n]`) —
in particular at dimension 2, where Gleason's theorem does not apply.

Positivity is spelled via
`Matrix.PosSemidef` throughout: Mathlib's order on matrices is the
Loewner order, provided as a scoped instance (`open scoped MatrixOrder`,
in `Mathlib.Analysis.Matrix.Order`, where `Matrix.nonneg_iff_posSemidef`
gives `0 ≤ A ↔ A.PosSemidef`); this file spells the effect interval via
`PosSemidef` directly and never opens that scoped matrix order (only
the standard scoped `ComplexOrder` on the scalars).
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

namespace PDT
namespace Busch

open Matrix Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An effect: a positive semidefinite matrix below the identity. -/
def IsEffect (a : Matrix n n ℂ) : Prop :=
  a.PosSemidef ∧ (1 - a).PosSemidef

/-- A generalized probability measure (frame function) on effects:
nonnegative, finitely additive where the sum stays an effect, and
normalized at the identity. -/
structure IsFrameFunction (f : Matrix n n ℂ → ℝ) : Prop where
  nonneg : ∀ a : Matrix n n ℂ, IsEffect a → 0 ≤ f a
  add : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
    (1 - (a + b)).PosSemidef → f (a + b) = f a + f b
  norm_one : f 1 = 1

/-! ### The bootstrap: additivity forces homogeneity -/

omit [DecidableEq n] [Fintype n] in
/-- Real scalar multiples of PSD matrices by nonnegative reals are PSD. -/
lemma smul_posSemidef {a : Matrix n n ℂ} (ha : a.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • a).PosSemidef := by
  have h : (c • a) = ((c : ℂ) • a) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [h]
  exact ha.smul (by exact_mod_cast hc)

omit [Fintype n] in
lemma effect_zero : IsEffect (0 : Matrix n n ℂ) := by
  refine ⟨PosSemidef.zero, ?_⟩
  simpa using (PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef)

omit [Fintype n] in
lemma effect_one : IsEffect (1 : Matrix n n ℂ) := by
  refine ⟨PosSemidef.one, ?_⟩
  simpa using (PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)

section Bootstrap

variable {f : Matrix n n ℂ → ℝ} (hf : IsFrameFunction f)

include hf

omit [Fintype n] in
lemma frame_zero : f 0 = 0 := by
  have h := hf.add 0 0 PosSemidef.zero PosSemidef.zero
    (by simpa using (PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef))
  simp only [add_zero] at h
  linarith

omit [Fintype n] in
/-- Monotonicity: if `a` is PSD, `b - a` is PSD, and `b` is an effect,
then `f a ≤ f b`. -/
lemma frame_mono {a b : Matrix n n ℂ} (ha : a.PosSemidef)
    (hab : (b - a).PosSemidef) (hb1 : (1 - b).PosSemidef) : f a ≤ f b := by
  have hb : b = a + (b - a) := by abel
  have h1 : (1 - (a + (b - a))).PosSemidef := by
    rw [← hb]; exact hb1
  have hadd := hf.add a (b - a) ha hab h1
  have hnn : 0 ≤ f (b - a) := by
    refine hf.nonneg _ ⟨hab, ?_⟩
    have : 1 - (b - a) = (1 - b) + a := by abel
    rw [this]
    exact hb1.add ha
  calc f a ≤ f a + f (b - a) := by linarith
    _ = f (a + (b - a)) := (hadd).symm
    _ = f b := by rw [← hb]

omit [Fintype n] in
lemma frame_effect_le_one {a : Matrix n n ℂ} (h : IsEffect a) : f a ≤ 1 := by
  have := frame_mono hf h.1 (by simpa using h.2) (by simpa using
    (PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef))
  simpa [hf.norm_one] using this

omit [Fintype n] in
/-- Natural scaling: `f (k • a) = k * f a` whenever `k • a` stays an effect. -/
lemma frame_nsmul {a : Matrix n n ℂ} (ha : a.PosSemidef) :
    ∀ k : ℕ, (1 - (k : ℝ) • a).PosSemidef → f ((k : ℝ) • a) = k * f a := by
  intro k
  induction k with
  | zero => intro _; simpa using frame_zero hf
  | succ k ih =>
      intro hk1
      have hka : ((k : ℝ) • a).PosSemidef := smul_posSemidef ha (by positivity)
      have hsplit : ((k + 1 : ℕ) : ℝ) • a = (k : ℝ) • a + a := by
        push_cast
        module
      have hprev : (1 - (k : ℝ) • a).PosSemidef := by
        have : 1 - (k : ℝ) • a = (1 - ((k + 1 : ℕ) : ℝ) • a) + a := by
          push_cast
          module
        rw [this]
        exact hk1.add ha
      have hadd := hf.add ((k : ℝ) • a) a hka ha (by rw [← hsplit]; exact hk1)
      rw [hsplit, hadd, ih hprev]
      push_cast
      ring

omit [Fintype n] in
/-- Division: `f ((1/m) • a) = f a / m` for an effect `a`. -/
lemma frame_inv_smul {a : Matrix n n ℂ} (ha : a.PosSemidef)
    (h1 : (1 - a).PosSemidef) {m : ℕ} (hm : 0 < m) :
    f ((m : ℝ)⁻¹ • a) = f a / m := by
  have hb : ((m : ℝ)⁻¹ • a).PosSemidef :=
    smul_posSemidef ha (by positivity)
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hsm : (m : ℝ) • ((m : ℝ)⁻¹ • a) = a := by
    rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]
  have h := frame_nsmul hf hb m (by rw [hsm]; exact h1)
  rw [hsm] at h
  rw [eq_div_iff hm0, mul_comm]
  exact h.symm

omit [Fintype n] in
/-- Rational scaling: `f ((p/m) • a) = (p/m) * f a` for `p ≤ m`. -/
lemma frame_rat_smul {a : Matrix n n ℂ} (ha : a.PosSemidef)
    (h1 : (1 - a).PosSemidef) {p m : ℕ} (hpm : p ≤ m) (hm : 0 < m) :
    f (((p : ℝ) / m) • a) = (p : ℝ) / m * f a := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hb : ((m : ℝ)⁻¹ • a).PosSemidef := smul_posSemidef ha (by positivity)
  have hsplit : ((p : ℝ) / m) • a = (p : ℝ) • ((m : ℝ)⁻¹ • a) := by
    rw [smul_smul, div_eq_mul_inv]
  have hclose : (1 - (p : ℝ) • ((m : ℝ)⁻¹ • a)).PosSemidef := by
    have hc1 : (p : ℝ) • ((m : ℝ)⁻¹ • a) = ((p : ℝ) / m) • a := by
      rw [smul_smul, div_eq_mul_inv]
    have hc2 : (1 : Matrix n n ℂ) - ((p : ℝ) / m) • a
        = (1 - a) + (1 - (p : ℝ) / m) • a := by module
    rw [hc1, hc2]
    refine h1.add (smul_posSemidef ha ?_)
    have hple : (p : ℝ) / m ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hpm
    linarith
  rw [hsplit, frame_nsmul hf hb p hclose, frame_inv_smul hf ha h1 hm]
  field_simp

omit [Fintype n] in
/-- Scalar monotonicity in the coefficient. -/
lemma frame_smul_mono {a : Matrix n n ℂ} (ha : a.PosSemidef)
    (h1 : (1 - a).PosSemidef) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) : f (s • a) ≤ f (t • a) := by
  refine frame_mono hf (smul_posSemidef ha hs) ?_ ?_
  · have : t • a - s • a = (t - s) • a := by module
    rw [this]
    exact smul_posSemidef ha (by linarith)
  · have : 1 - t • a = (1 - a) + (1 - t) • a := by module
    rw [this]
    exact h1.add (smul_posSemidef ha (by linarith))

omit [Fintype n] in
/-- **Real homogeneity by monotone squeeze**: no continuity hypothesis is
needed; monotonicity substitutes. The analytic heart of Busch's proof. -/
lemma frame_smul {a : Matrix n n ℂ} (ha : a.PosSemidef)
    (h1 : (1 - a).PosSemidef) {t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ 1) :
    f (t • a) = t * f a := by
  have hfa0 : 0 ≤ f a := hf.nonneg a ⟨ha, h1⟩
  -- reduce a rational q in [0,1] to frame_rat_smul
  have hq : ∀ q : ℚ, 0 ≤ q → (q : ℝ) ≤ 1 → f ((q : ℝ) • a) = q * f a := by
    intro q hq0 hq1
    have hnum : ((q.num.toNat : ℝ) / (q.den : ℝ)) = (q : ℝ) := by
      have h0 : (q.num.toNat : ℤ) = q.num :=
        Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)
      have h0' : ((q.num.toNat : ℝ)) = ((q.num : ℤ) : ℝ) := by
        exact_mod_cast h0
      rw [h0']
      exact_mod_cast Rat.num_div_den q
    have hle : q.num.toNat ≤ q.den := by
      have h2 : (q.num.toNat : ℝ) ≤ (q.den : ℝ) :=
        (div_le_one (by positivity : (0:ℝ) < (q.den : ℝ))).mp
          (by rw [hnum]; exact hq1)
      exact_mod_cast h2
    rw [← hnum, frame_rat_smul hf ha h1 hle q.den_pos, hnum]
  refine le_antisymm ?_ ?_
  · -- f (t • a) ≤ t * f a : squeeze from above by rationals
    by_cases hfa : f a = 0
    · have hle1 : f (t • a) ≤ f ((1 : ℝ) • a) :=
        frame_smul_mono hf ha h1 h0 ht le_rfl
      simp only [one_smul] at hle1
      have hge : 0 ≤ f (t • a) := by
        refine hf.nonneg _ ⟨smul_posSemidef ha h0, ?_⟩
        have : 1 - t • a = (1 - a) + (1 - t) • a := by module
        rw [this]
        exact h1.add (smul_posSemidef ha (by linarith))
      rw [hfa]
      simp only [mul_zero]
      linarith
    · have hfapos : 0 < f a := lt_of_le_of_ne hfa0 (Ne.symm hfa)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      rcases lt_or_ge (t + ε / f a) 1 with hlt | hge
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
          (show t < t + ε / f a by linarith [div_pos hε hfapos])
        have hq0 : (0:ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt h0 hq1)
        have hqle : (q : ℝ) ≤ 1 := le_of_lt (lt_trans hq2 hlt)
        have hmono := frame_smul_mono hf ha h1 h0 (le_of_lt hq1) hqle
        rw [hq q (by exact_mod_cast hq0) hqle] at hmono
        calc f (t • a) ≤ q * f a := hmono
          _ ≤ (t + ε / f a) * f a := by
              apply mul_le_mul_of_nonneg_right (le_of_lt hq2) hfa0
          _ = t * f a + ε := by field_simp
      · have hmono := frame_smul_mono hf ha h1 h0 ht le_rfl
        simp only [one_smul] at hmono
        calc f (t • a) ≤ f a := hmono
          _ = 1 * f a := (one_mul _).symm
          _ ≤ (t + ε / f a) * f a :=
              mul_le_mul_of_nonneg_right hge hfa0
          _ = t * f a + ε := by field_simp
  · -- t * f a ≤ f (t • a) : squeeze from below by rationals
    by_cases hfa : f a = 0
    · have hge : 0 ≤ f (t • a) := by
        refine hf.nonneg _ ⟨smul_posSemidef ha h0, ?_⟩
        have : 1 - t • a = (1 - a) + (1 - t) • a := by module
        rw [this]
        exact h1.add (smul_posSemidef ha (by linarith))
      rw [hfa]
      simpa using hge
    · have hfapos : 0 < f a := lt_of_le_of_ne hfa0 (Ne.symm hfa)
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      rcases lt_or_ge (t - ε / f a) 0 with hlt | hge
      · have hge0 : 0 ≤ f (t • a) := by
          refine hf.nonneg _ ⟨smul_posSemidef ha h0, ?_⟩
          have : 1 - t • a = (1 - a) + (1 - t) • a := by module
          rw [this]
          exact h1.add (smul_posSemidef ha (by linarith))
        have hlt2 : t * f a < ε := by
          have h2 : t < ε / f a := by linarith
          calc t * f a < (ε / f a) * f a :=
                mul_lt_mul_of_pos_right h2 hfapos
            _ = ε := by field_simp
        linarith
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
          (show t - ε / f a < t by linarith [div_pos hε hfapos])
        have hq0 : (0:ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt hge hq1)
        have hqle : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq2 ht)
        have hmono := frame_smul_mono hf ha h1
          (by exact_mod_cast hq0) (le_of_lt hq2) ht
        rw [hq q (by exact_mod_cast hq0) hqle] at hmono
        have hchain : (t - ε / f a) * f a ≤ (q : ℝ) * f a :=
          mul_le_mul_of_nonneg_right (le_of_lt hq1) hfa0
        have hexp : (t - ε / f a) * f a = t * f a - ε := by
          field_simp
        linarith

end Bootstrap

/-! ### Extension from effects to all PSD and Hermitian matrices -/

/-- Conjugation by the eigenvector unitary preserves positive
semidefiniteness of the diagonal core: if the entries are nonnegative,
the conjugated matrix is PSD. -/
lemma posSemidef_conjAut {A : Matrix n n ℂ} (hH : A.IsHermitian)
    {d : n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    ((conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
      (diagonal (fun i => (d i : ℂ)))).PosSemidef := by
  rw [conjStarAlgAut_apply]
  have hdiag : (diagonal (fun i => (d i : ℂ))).PosSemidef := by
    refine PosSemidef.diagonal ?_
    intro i
    show (0 : ℂ) ≤ (d i : ℂ)
    exact_mod_cast hd i
  have h := hdiag.conjTranspose_mul_mul_same
    (B := (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
  simpa [Matrix.star_eq_conjTranspose, mul_assoc] using h

/-- The canonical scale for a PSD matrix: one plus the sum of its
eigenvalues (= one plus its trace). -/
noncomputable def scaleOf (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then (∑ i, h.eigenvalues i) + 1 else 1

lemma scaleOf_pos {A : Matrix n n ℂ} (hA : A.PosSemidef) : 0 < scaleOf A := by
  rw [scaleOf, dif_pos hA.isHermitian]
  have : 0 ≤ ∑ i, hA.isHermitian.eigenvalues i :=
    Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i
  linarith

lemma one_le_scaleOf {A : Matrix n n ℂ} (hA : A.PosSemidef) : 1 ≤ scaleOf A := by
  rw [scaleOf, dif_pos hA.isHermitian]
  have : 0 ≤ ∑ i, hA.isHermitian.eigenvalues i :=
    Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i
  linarith

/-- **Scaling into the effect interval**: for PSD `A`, `(scaleOf A)⁻¹ • A`
is an effect. Proof: conjugate the claim to the eigenvalue diagonal. -/
lemma effect_inv_scale_smul {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    IsEffect ((scaleOf A)⁻¹ • A) := by
  have hH := hA.isHermitian
  set c : ℝ := scaleOf A with hc
  have hc0 : 0 < c := scaleOf_pos hA
  refine ⟨smul_posSemidef hA (by positivity), ?_⟩
  have hsm : ∀ (M : Matrix n n ℂ) (r : ℝ), r • M = (r : ℂ) • M := by
    intro M r
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  have key : (1 : Matrix n n ℂ) - c⁻¹ • A
      = (conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
          (diagonal (fun i => ((1 - c⁻¹ * hH.eigenvalues i : ℝ) : ℂ))) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [hsm]
    rw [← map_one (conjStarAlgAut ℂ _ hH.eigenvectorUnitary),
      ← map_smul, ← map_sub]
    congr 1
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.smul_apply, Matrix.one_apply_eq, Function.comp,
        Matrix.diagonal_apply_eq]
      try push_cast
      try ring
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij,
        Matrix.smul_apply]
  rw [key]
  refine posSemidef_conjAut hH ?_
  intro i
  have hle : hH.eigenvalues i ≤ ∑ j, hH.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hsum : (∑ j, hH.eigenvalues j) + 1 = c := by rw [hc, scaleOf, dif_pos hH]
  have h1 : c⁻¹ * hH.eigenvalues i ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one hc0]
    linarith
  linarith

section Extension

variable {f : Matrix n n ℂ → ℝ} (hf : IsFrameFunction f)

/-- The canonical extension of a frame function to all PSD matrices. -/
noncomputable def ext (f : Matrix n n ℂ → ℝ) (A : Matrix n n ℂ) : ℝ :=
  scaleOf A * f ((scaleOf A)⁻¹ • A)

include hf

omit [Fintype n] in
/-- Scale independence: any valid scale computes the same extension. -/
lemma scale_indep {A : Matrix n n ℂ} (_hA : A.PosSemidef) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hdc : d ≤ c) (hde : IsEffect (d⁻¹ • A)) :
    c * f (c⁻¹ • A) = d * f (d⁻¹ • A) := by
  have hsplit : c⁻¹ • A = (d / c) • (d⁻¹ • A) := by
    rw [smul_smul]
    congr 1
    field_simp
  have ht0 : 0 ≤ d / c := by positivity
  have ht1 : d / c ≤ 1 := by
    rw [div_le_one hc]
    exact hdc
  rw [hsplit, frame_smul hf hde.1 hde.2 ht0 ht1]
  field_simp

/-- The extension agrees with `f` on effects. -/
lemma ext_eq_on_effect {A : Matrix n n ℂ} (h : IsEffect A) :
    ext f A = f A := by
  rw [ext]
  have h1 := scale_indep hf h.1 (scaleOf_pos h.1) one_pos
    (one_le_scaleOf h.1) (by simpa using h)
  rw [inv_one, one_smul, one_mul] at h1
  exact h1

omit hf in
/-- Scales dominate componentwise: `scaleOf A ≤ scaleOf (A + B)` for PSD
`A`, `B` (trace additivity plus nonnegativity). -/
lemma scaleOf_le_add {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : scaleOf A ≤ scaleOf (A + B) := by
  have hAB : (A + B).PosSemidef := hA.add hB
  rw [scaleOf, scaleOf, dif_pos hA.isHermitian, dif_pos hAB.isHermitian]
  have htr : ∀ {X : Matrix n n ℂ} (hX : X.PosSemidef),
      ((∑ i, hX.isHermitian.eigenvalues i : ℝ) : ℂ) = X.trace := by
    intro X hX
    rw [hX.isHermitian.trace_eq_sum_eigenvalues]
    push_cast
    rfl
  have hA' := htr hA
  have hB' := htr hB
  have hAB' := htr hAB
  have hsum : ((∑ i, hAB.isHermitian.eigenvalues i : ℝ) : ℂ)
      = ((∑ i, hA.isHermitian.eigenvalues i : ℝ) : ℂ)
        + ((∑ i, hB.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hA', hB', hAB', trace_add]
  have hsumR : (∑ i, hAB.isHermitian.eigenvalues i)
      = (∑ i, hA.isHermitian.eigenvalues i)
        + (∑ i, hB.isHermitian.eigenvalues i) := by
    exact_mod_cast hsum
  have hBnn : 0 ≤ ∑ i, hB.isHermitian.eigenvalues i :=
    Finset.sum_nonneg fun i _ => hB.eigenvalues_nonneg i
  linarith

/-- The extension is additive on PSD matrices. -/
lemma ext_add {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ext f (A + B) = ext f A + ext f B := by
  set e : ℝ := scaleOf (A + B) with he
  have hAB : (A + B).PosSemidef := hA.add hB
  have he0 : 0 < e := scaleOf_pos hAB
  have heff := effect_inv_scale_smul hAB
  have hsub : ∀ {X Y : Matrix n n ℂ}, X.PosSemidef → Y.PosSemidef →
      IsEffect (e⁻¹ • (X + Y)) → IsEffect (e⁻¹ • X) := by
    intro X Y hX hY hXY
    refine ⟨smul_posSemidef hX (by positivity), ?_⟩
    have hkey : (1 : Matrix n n ℂ) - e⁻¹ • X
        = (1 - e⁻¹ • (X + Y)) + e⁻¹ • Y := by
      rw [smul_add]
      abel
    rw [hkey]
    exact hXY.2.add (smul_posSemidef hY (by positivity))
  have heA : IsEffect (e⁻¹ • A) := hsub hA hB heff
  have heB : IsEffect (e⁻¹ • B) := by
    refine hsub hB hA ?_
    rwa [add_comm]
  have hsum : e⁻¹ • A + e⁻¹ • B = e⁻¹ • (A + B) := by rw [smul_add]
  have hadd := hf.add (e⁻¹ • A) (e⁻¹ • B) heA.1 heB.1
    (by rw [hsum]; exact heff.2)
  have hextA : e * f (e⁻¹ • A) = ext f A := by
    rw [ext]
    exact scale_indep hf hA he0 (scaleOf_pos hA) (scaleOf_le_add hA hB)
      (effect_inv_scale_smul hA)
  have hextB : e * f (e⁻¹ • B) = ext f B := by
    rw [ext]
    have hle : scaleOf B ≤ e := by
      have := scaleOf_le_add hB hA
      rwa [add_comm] at this
    exact scale_indep hf hB he0 (scaleOf_pos hB) hle
      (effect_inv_scale_smul hB)
  have hgoal : ext f (A + B) = e * f (e⁻¹ • (A + B)) := by rw [ext]
  rw [hgoal, ← hsum, hadd, mul_add, hextA, hextB]

/-- Homogeneity of the extension under nonnegative real scaling. -/
lemma ext_smul {A : Matrix n n ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    ext f (t • A) = t * ext f A := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rw [zero_smul, zero_mul, ext, smul_zero, frame_zero hf, mul_zero]
  · have htA : (t • A).PosSemidef := smul_posSemidef hA ht
    have hs0 : 0 < t * scaleOf A := by
      have := scaleOf_pos hA
      positivity
    have hcollapse : (t * scaleOf A)⁻¹ • (t • A) = (scaleOf A)⁻¹ • A := by
      rw [smul_smul]
      congr 1
      rw [mul_inv, mul_comm t⁻¹ (scaleOf A)⁻¹, mul_assoc,
        inv_mul_cancel₀ (ne_of_gt htpos), mul_one]
    have hseff : IsEffect ((t * scaleOf A)⁻¹ • (t • A)) := by
      rw [hcollapse]
      exact effect_inv_scale_smul hA
    have hc' : 0 < scaleOf (t • A) := scaleOf_pos htA
    have hkey : scaleOf (t • A) * f ((scaleOf (t • A))⁻¹ • (t • A))
        = (t * scaleOf A) * f ((t * scaleOf A)⁻¹ • (t • A)) := by
      rcases le_total (t * scaleOf A) (scaleOf (t • A)) with hle | hle
      · exact scale_indep hf htA hc' hs0 hle hseff
      · exact (scale_indep hf htA hs0 hc' hle (effect_inv_scale_smul htA)).symm
    rw [ext, hkey, hcollapse, ext]
    ring

omit hf in
lemma ext_nonneg_of_frame (hf' : IsFrameFunction f) {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : 0 ≤ ext f A := by
  rw [ext]
  have h1 := hf'.nonneg _ (effect_inv_scale_smul hA)
  have h0 := scaleOf_pos hA
  positivity

/-- `ext` of a nonnegative multiple of the identity. -/
lemma ext_smul_one {c : ℝ} (hc : 0 ≤ c) : ext f (c • 1) = c := by
  rw [ext_smul hf PosSemidef.one hc, ext_eq_on_effect hf effect_one,
    hf.norm_one, mul_one]

end Extension

/-! ### The Hermitian layer -/

/-- Canonical PSD shift for a Hermitian matrix: one plus the sum of the
absolute values of its eigenvalues. -/
noncomputable def shiftOf (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then (∑ i, |h.eigenvalues i|) + 1 else 1

lemma shiftOf_nonneg (A : Matrix n n ℂ) : 0 ≤ shiftOf A := by
  rw [shiftOf]
  by_cases h : A.IsHermitian
  · rw [dif_pos h]
    have h1 : (0:ℝ) ≤ ∑ i, |h.eigenvalues i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  · rw [dif_neg h]
    linarith

/-- The canonical shift makes a Hermitian matrix PSD. -/
lemma shift_posSemidef {A : Matrix n n ℂ} (hH : A.IsHermitian) :
    (A + shiftOf A • 1).PosSemidef := by
  set s : ℝ := shiftOf A with hs
  have hsm : ∀ (M : Matrix n n ℂ) (r : ℝ), r • M = (r : ℂ) • M := by
    intro M r
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  have key : A + s • 1
      = (conjStarAlgAut ℂ _ hH.eigenvectorUnitary)
          (diagonal (fun i => ((hH.eigenvalues i + s : ℝ) : ℂ))) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [hsm]
    rw [← map_one (conjStarAlgAut ℂ _ hH.eigenvectorUnitary), ← map_smul,
      ← map_add]
    congr 1
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.smul_apply, Matrix.one_apply_eq, Function.comp,
        Matrix.diagonal_apply_eq]
      try push_cast
      try ring
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij,
        Matrix.smul_apply]
  rw [key]
  refine posSemidef_conjAut hH ?_
  intro i
  have h1 : |hH.eigenvalues i| ≤ ∑ j, |hH.eigenvalues j| :=
    Finset.single_le_sum (f := fun j => |hH.eigenvalues j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : (∑ j, |hH.eigenvalues j|) + 1 = s := by
    rw [hs, shiftOf, dif_pos hH]
  have h3 : -(hH.eigenvalues i) ≤ |hH.eigenvalues i| := neg_le_abs _
  linarith

section HermitianLayer

variable {f : Matrix n n ℂ → ℝ} (hf : IsFrameFunction f)

/-- The extension of a frame function to all Hermitian matrices. -/
noncomputable def extH (f : Matrix n n ℂ → ℝ) (A : Matrix n n ℂ) : ℝ :=
  ext f (A + shiftOf A • 1) - shiftOf A

include hf

/-- Shift independence: any PSD-making shift computes the same value. -/
lemma extH_eq_shift {A : Matrix n n ℂ} (hH : A.IsHermitian) {s : ℝ}
    (hs : 0 ≤ s) (hpsd : (A + s • 1).PosSemidef) :
    extH f A = ext f (A + s • 1) - s := by
  have hS := shiftOf_nonneg A
  have hSpsd := shift_posSemidef hH
  -- compare both shifts through their maximum
  have hcomm : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → u ≤ v →
      (A + u • 1).PosSemidef → ext f (A + v • 1) - v = ext f (A + u • 1) - u := by
    intro u v hu hv huv hupsd
    have hsplit : A + v • 1 = (A + u • 1) + (v - u) • 1 := by
      have : (v : ℝ) • (1 : Matrix n n ℂ) = u • 1 + (v - u) • 1 := by
        rw [← add_smul]
        congr 1
        ring
      rw [this]
      abel
    rw [hsplit, ext_add hf hupsd (smul_posSemidef PosSemidef.one (by linarith)),
      ext_smul_one hf (by linarith)]
    ring
  rcases le_total s (shiftOf A) with hle | hle
  · rw [extH, hcomm hs hS hle hpsd]
  · rw [extH, ← hcomm hS hs hle hSpsd]

/-- `extH` agrees with `ext` on PSD matrices. -/
lemma extH_eq_ext {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    extH f A = ext f A := by
  have h := extH_eq_shift hf hA.isHermitian le_rfl
    (by simpa using hA)
  simpa using h

/-- Additivity of `extH` on Hermitian matrices. -/
lemma extH_add {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    extH f (A + B) = extH f A + extH f B := by
  set sA := shiftOf A
  set sB := shiftOf B
  have hApsd := shift_posSemidef hA
  have hBpsd := shift_posSemidef hB
  have hs : 0 ≤ sA + sB := by
    have := shiftOf_nonneg A
    have := shiftOf_nonneg B
    linarith
  have hsplit : (A + B) + (sA + sB) • 1 = (A + sA • 1) + (B + sB • 1) := by
    rw [add_smul]
    abel
  have hABpsd : ((A + B) + (sA + sB) • 1).PosSemidef := by
    rw [hsplit]
    exact hApsd.add hBpsd
  rw [extH_eq_shift hf (hA.add hB) hs hABpsd, hsplit,
    ext_add hf hApsd hBpsd, extH, extH]
  ring

/-- `extH` vanishes at zero. -/
lemma extH_zero : extH f 0 = 0 := by
  have h := extH_eq_shift hf (isHermitian_zero) le_rfl (by simpa using
    (PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef))
  simpa [ext, frame_zero hf] using h

/-- `extH` respects negation on Hermitian matrices. -/
lemma extH_neg {A : Matrix n n ℂ} (hH : A.IsHermitian) :
    extH f (-A) = - extH f A := by
  have h := extH_add hf hH hH.neg
  rw [add_neg_cancel, extH_zero hf] at h
  linarith

omit [DecidableEq n] [Fintype n] hf in
lemma isHermitian_real_smul {A : Matrix n n ℂ} (hH : A.IsHermitian)
    (t : ℝ) : (t • A).IsHermitian := by
  show (t • A)ᴴ = t • A
  rw [Matrix.conjTranspose_smul, star_trivial, hH]

/-- Real homogeneity of `extH` for nonnegative scalars. -/
lemma extH_smul_nonneg {A : Matrix n n ℂ} (hH : A.IsHermitian) {t : ℝ}
    (ht : 0 ≤ t) : extH f (t • A) = t * extH f A := by
  set s := shiftOf A with hsdef
  have hpsd := shift_posSemidef hH
  have hts : 0 ≤ t * s := mul_nonneg ht (shiftOf_nonneg A)
  have hkey : t • A + (t * s) • 1 = t • (A + s • 1) := by
    rw [smul_add, smul_smul]
  have htpsd : (t • A + (t * s) • 1).PosSemidef := by
    rw [hkey]
    exact smul_posSemidef hpsd ht
  rw [extH_eq_shift hf (isHermitian_real_smul hH t) hts htpsd, hkey,
    ext_smul hf hpsd ht, extH]
  ring

/-- Full real homogeneity of `extH` on Hermitian matrices. -/
lemma extH_smul {A : Matrix n n ℂ} (hH : A.IsHermitian) (t : ℝ) :
    extH f (t • A) = t * extH f A := by
  rcases le_total 0 t with ht | ht
  · exact extH_smul_nonneg hf hH ht
  · have h1 : t • A = -((-t) • A) := by
      rw [neg_smul, neg_neg]
    rw [h1, extH_neg hf (isHermitian_real_smul hH (-t)),
      extH_smul_nonneg hf hH (by linarith : (0:ℝ) ≤ -t)]
    ring

end HermitianLayer

/-! ### The density matrix -/

/-- Matrix unit `e i j` (self-contained; avoids external basis API). -/
noncomputable def eb (i j : n) : Matrix n n ℂ :=
  of fun p q => if p = i ∧ q = j then 1 else 0

omit [Fintype n] in
lemma eb_apply (i j p q : n) :
    eb i j p q = if p = i ∧ q = j then 1 else 0 := rfl

omit [Fintype n] in
lemma eb_conjTranspose (i j : n) : (eb i j)ᴴ = eb j i := by
  ext p q
  simp only [conjTranspose_apply, eb_apply]
  rcases eq_or_ne p j with rfl | hp <;> rcases eq_or_ne q i with rfl | hq <;>
    simp [*, and_comm]

/-- Symmetrized Hermitian basis element. -/
noncomputable def SB (i j : n) : Matrix n n ℂ := eb i j + eb j i

/-- Antisymmetrized Hermitian basis element. -/
noncomputable def TB (i j : n) : Matrix n n ℂ :=
  Complex.I • eb i j - Complex.I • eb j i

omit [Fintype n] in
lemma SB_hermitian (i j : n) : (SB i j).IsHermitian := by
  show (SB i j)ᴴ = SB i j
  rw [SB, conjTranspose_add, eb_conjTranspose, eb_conjTranspose, add_comm]

omit [Fintype n] in
lemma TB_hermitian (i j : n) : (TB i j).IsHermitian := by
  show (TB i j)ᴴ = TB i j
  rw [TB, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
    eb_conjTranspose, eb_conjTranspose]
  simp only [Complex.star_def, Complex.conj_I]
  module

omit [Fintype n] in
lemma SB_symm (i j : n) : SB j i = SB i j := add_comm _ _

omit [Fintype n] in
lemma TB_antisymm (i j : n) : TB j i = -TB i j := by
  rw [TB, TB]
  module

omit [Fintype n] in
lemma TB_self (i : n) : TB i i = 0 := by
  rw [TB]
  module

/-- The density matrix of a frame function, entry by entry from the
Hermitian extension on the basis. -/
noncomputable def rho (f : Matrix n n ℂ → ℝ) : Matrix n n ℂ :=
  of fun i j =>
    ((extH f (SB i j) : ℂ) + Complex.I * (extH f (TB i j) : ℂ)) / 2

lemma rho_apply (f : Matrix n n ℂ → ℝ) (i j : n) :
    rho f i j
      = ((extH f (SB i j) : ℂ) + Complex.I * (extH f (TB i j) : ℂ)) / 2 :=
  rfl

/-- Trace against a matrix unit picks out an entry. -/
lemma trace_mul_eb (M : Matrix n n ℂ) (i j : n) :
    (M * eb i j).trace = M j i := by
  have h : ∀ p, (M * eb i j) p p = if p = j then M p i else 0 := by
    intro p
    simp only [mul_apply, eb_apply]
    rcases eq_or_ne p j with rfl | hp
    · simp
    · simp [hp]
  rw [Matrix.trace]
  simp only [Matrix.diag]
  rw [Finset.sum_congr rfl fun p _ => h p]
  simp

section RhoTrace

variable {f : Matrix n n ℂ → ℝ} (hf : IsFrameFunction f)

include hf

omit hf in
lemma trace_mul_SB (M : Matrix n n ℂ) (i j : n) :
    (M * SB i j).trace = M j i + M i j := by
  rw [SB, mul_add, trace_add, trace_mul_eb, trace_mul_eb]

omit hf in
lemma trace_mul_TB (M : Matrix n n ℂ) (i j : n) :
    (M * TB i j).trace = Complex.I * M j i - Complex.I * M i j := by
  rw [TB, mul_sub, trace_sub, mul_smul_comm, mul_smul_comm, trace_smul,
    trace_smul, trace_mul_eb, trace_mul_eb, smul_eq_mul, smul_eq_mul]

/-- Trace of `rho` against the symmetric basis element. -/
lemma trace_rho_SB (i j : n) :
    (rho f * SB i j).trace = (extH f (SB i j) : ℂ) := by
  rw [trace_mul_SB, rho_apply, rho_apply, SB_symm, TB_antisymm,
    extH_neg hf (TB_hermitian i j)]
  push_cast
  ring

/-- Trace of `rho` against the antisymmetric basis element. -/
lemma trace_rho_TB (i j : n) :
    (rho f * TB i j).trace = (extH f (TB i j) : ℂ) := by
  rw [trace_mul_TB, rho_apply, rho_apply, SB_symm, TB_antisymm,
    extH_neg hf (TB_hermitian i j)]
  push_cast
  linear_combination (-(extH f (TB i j) : ℂ)) * Complex.I_sq

omit [DecidableEq n] [Fintype n] hf in
lemma isHermitian_finsetSum {ι : Type*} {s : Finset ι}
    {g : ι → Matrix n n ℂ} (hg : ∀ k ∈ s, (g k).IsHermitian) :
    (∑ k ∈ s, g k).IsHermitian := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (hg a (Finset.mem_cons_self a s)).add
        (ih fun k hk => hg k (Finset.mem_cons_of_mem hk))

lemma extH_finsetSum {ι : Type*} {s : Finset ι} {g : ι → Matrix n n ℂ}
    (hg : ∀ k ∈ s, (g k).IsHermitian) :
    extH f (∑ k ∈ s, g k) = ∑ k ∈ s, extH f (g k) := by
  induction s using Finset.cons_induction with
  | empty => simpa using extH_zero hf
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        extH_add hf (hg a (Finset.mem_cons_self a s))
          (isHermitian_finsetSum fun k hk => hg k (Finset.mem_cons_of_mem hk)),
        ih fun k hk => hg k (Finset.mem_cons_of_mem hk)]

omit hf in
/-- Hermitian matrices decompose over the `SB`/`TB` basis. -/
lemma hermitian_decomp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M = (2⁻¹ : ℝ) • ∑ i, ∑ j,
      ((M i j).re • SB i j + (M i j).im • TB i j) := by
  have hentry : ∀ p q, M q p = star (M p q) := by
    intro p q
    have h := congrFun (congrFun hM p) q
    rw [conjTranspose_apply] at h
    rw [← h, star_star]
  ext p q
  have collapse : ∀ (c : n → n → ℂ),
      (∑ i, ∑ j, c i j * (if p = i ∧ q = j then (1:ℂ) else 0)) = c p q := by
    intro c
    have hrow : ∀ i, (∑ j, c i j * (if p = i ∧ q = j then (1:ℂ) else 0))
        = if p = i then c i q else 0 := by
      intro i
      rcases eq_or_ne p i with rfl | hpi
      · simp
      · simp [hpi]
    rw [Finset.sum_congr rfl fun i _ => hrow i]
    simp
  have h1 : ∀ i j : n, ((M i j).re • SB i j + (M i j).im • TB i j) p q
      = (((M i j).re : ℂ) + Complex.I * (M i j).im)
          * (if p = i ∧ q = j then (1:ℂ) else 0)
        + (((M i j).re : ℂ) - Complex.I * (M i j).im)
          * (if p = j ∧ q = i then (1:ℂ) else 0) := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, SB, TB, Matrix.sub_apply,
      eb_apply, smul_eq_mul, Complex.real_smul]
    ring
  have hbig : (∑ i, ∑ j, ((M i j).re • SB i j + (M i j).im • TB i j)) p q
      = (((M p q).re : ℂ) + Complex.I * (M p q).im)
        + (((M q p).re : ℂ) - Complex.I * (M q p).im) := by
    simp only [Matrix.sum_apply]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [collapse (fun i j => ((M i j).re : ℂ) + Complex.I * (M i j).im)]
    have hswap : (∑ i, ∑ j, ((((M i j).re : ℂ) - Complex.I * (M i j).im)
        * (if p = j ∧ q = i then (1:ℂ) else 0)))
        = ((M q p).re : ℂ) - Complex.I * (M q p).im := by
      rw [Finset.sum_comm]
      exact collapse fun a b => ((M b a).re : ℂ) - Complex.I * (M b a).im
    rw [hswap]
  rw [Matrix.smul_apply, hbig, hentry p q]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Complex.real_smul]
  push_cast
  have hM' := Complex.re_add_im (M p q)
  linear_combination -hM'

/-- **The trace formula**: `rho` represents the Hermitian extension. -/
lemma trace_rho_mul {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (rho f * M).trace = (extH f M : ℂ) := by
  have hsummand : ∀ i j : n,
      ((M i j).re • SB i j + (M i j).im • TB i j).IsHermitian := fun i j =>
    (isHermitian_real_smul (SB_hermitian i j) _).add
      (isHermitian_real_smul (TB_hermitian i j) _)
  have hrhs : extH f M = 2⁻¹ * ∑ i, ∑ j,
      ((M i j).re * extH f (SB i j) + (M i j).im * extH f (TB i j)) := by
    conv_lhs => rw [hermitian_decomp hM]
    rw [extH_smul hf (isHermitian_finsetSum fun i _ =>
        isHermitian_finsetSum fun j _ => hsummand i j)]
    congr 1
    rw [extH_finsetSum hf fun i _ =>
      isHermitian_finsetSum fun j _ => hsummand i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [extH_finsetSum hf fun j _ => hsummand i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [extH_add hf (isHermitian_real_smul (SB_hermitian i j) _)
        (isHermitian_real_smul (TB_hermitian i j) _),
      extH_smul hf (SB_hermitian i j), extH_smul hf (TB_hermitian i j)]
  have hlhs : (rho f * M).trace = ((2⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j,
      (((M i j).re : ℂ) * (extH f (SB i j) : ℂ)
        + ((M i j).im : ℂ) * (extH f (TB i j) : ℂ)) := by
    conv_lhs => rw [hermitian_decomp hM]
    rw [mul_smul_comm, trace_smul, Finset.mul_sum, trace_sum]
    rw [Complex.real_smul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, trace_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_add, trace_add, mul_smul_comm, mul_smul_comm, trace_smul,
      trace_smul, trace_rho_SB hf, trace_rho_TB hf, Complex.real_smul,
      Complex.real_smul]
  rw [hlhs, hrhs]
  push_cast
  ring

/-- `rho` is Hermitian. -/
lemma rho_hermitian : (rho f).IsHermitian := by
  show (rho f)ᴴ = rho f
  ext i j
  rw [conjTranspose_apply, rho_apply, rho_apply, SB_symm, TB_antisymm,
    extH_neg hf (TB_hermitian i j)]
  push_cast
  simp only [star_div₀, star_add, star_mul, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal, map_neg, map_ofNat]
  ring

omit hf in
omit [DecidableEq n] in
/-- Outer products are PSD (direct computation). -/
lemma outer_posSemidef (x : n → ℂ) : (vecMulVec x (star x)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show (vecMulVec x (star x))ᴴ = vecMulVec x (star x)
    ext p q
    simp [vecMulVec_apply, conjTranspose_apply, Pi.star_apply, mul_comm]
  · intro y
    have hmv : ∀ q, (vecMulVec x (star x) *ᵥ y) q
        = x q * (star x ⬝ᵥ y) := by
      intro q
      simp [mulVec, vecMulVec_apply, dotProduct, Finset.mul_sum, mul_assoc]
    have hkey : star y ⬝ᵥ (vecMulVec x (star x) *ᵥ y)
        = star (star x ⬝ᵥ y) * (star x ⬝ᵥ y) := by
      calc star y ⬝ᵥ (vecMulVec x (star x) *ᵥ y)
          = ∑ q, star (y q) * (x q * (star x ⬝ᵥ y)) := by
            rw [dotProduct]
            exact Finset.sum_congr rfl fun q _ => by
              rw [hmv q, Pi.star_apply]
        _ = (∑ q, star (y q) * x q) * (star x ⬝ᵥ y) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ = star (star x ⬝ᵥ y) * (star x ⬝ᵥ y) := by
            congr 1
            rw [dotProduct, star_sum]
            exact Finset.sum_congr rfl fun q _ => by
              rw [Pi.star_apply, star_mul, star_star, mul_comm]
    rw [hkey]
    exact star_mul_self_nonneg _

end RhoTrace

/-! ### Assembly -/

omit [DecidableEq n] in
lemma dotProduct_eq_trace (X : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (X *ᵥ x) = (X * vecMulVec x (star x)).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag, mul_apply, vecMulVec_apply, Pi.star_apply]
  rw [dotProduct]
  simp only [mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    ring

lemma sum_eb_diag : (∑ i, eb i i) = (1 : Matrix n n ℂ) := by
  ext p q
  simp only [Matrix.sum_apply, eb_apply, Matrix.one_apply]
  rcases eq_or_ne p q with rfl | hpq
  · simp
  · rw [if_neg hpq, Finset.sum_eq_zero]
    intro i _
    rcases eq_or_ne p i with rfl | h1
    · simp [Ne.symm hpq]
    · simp [h1]

omit [Fintype n] in
lemma eb_diag_hermitian (i : n) : (eb i i).IsHermitian := by
  show (eb i i)ᴴ = eb i i
  rw [eb_conjTranspose]

section Assembly

variable {f : Matrix n n ℂ → ℝ} (hf : IsFrameFunction f)

include hf

lemma rho_posSemidef : (rho f).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (rho_hermitian hf) ?_
  intro x
  rw [dotProduct_eq_trace]
  have houter := outer_posSemidef x
  rw [trace_rho_mul hf houter.isHermitian, extH_eq_ext hf houter]
  have h := ext_nonneg_of_frame hf houter
  exact_mod_cast h

lemma rho_trace_one : (rho f).trace = 1 := by
  have hdiag : ∀ i, rho f i i = (extH f (eb i i) : ℂ) := by
    intro i
    rw [rho_apply, TB_self, extH_zero hf]
    have hSB : extH f (SB i i) = extH f (eb i i) + extH f (eb i i) := by
      rw [SB]
      exact extH_add hf (eb_diag_hermitian i) (eb_diag_hermitian i)
    rw [hSB]
    push_cast
    ring
  rw [Matrix.trace]
  simp only [Matrix.diag]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, ← Complex.ofReal_sum,
    ← extH_finsetSum hf fun i _ => eb_diag_hermitian i, sum_eb_diag,
    extH_eq_ext hf PosSemidef.one, ext_eq_on_effect hf effect_one,
    hf.norm_one]
  norm_num

end Assembly

/-- **Busch's theorem**, finite dimension: every frame function on the
effects of `Matrix n n ℂ` is `a ↦ trace (ρ * a)` for a unique density
matrix `ρ`. Born-rule uniqueness in the POVM reading, valid from
dimension 2 (Busch 2003). -/
theorem busch [Nonempty n] (f : Matrix n n ℂ → ℝ) (hf : IsFrameFunction f) :
    ∃! ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a : Matrix n n ℂ, IsEffect a → (ρ * a).trace = (f a : ℂ) := by
  refine ⟨rho f, ⟨rho_posSemidef hf, rho_trace_one hf, fun a ha => ?_⟩,
    fun ρ' h' => ?_⟩
  · rw [trace_rho_mul hf ha.1.isHermitian, extH_eq_ext hf ha.1,
      ext_eq_on_effect hf ha]
  · obtain ⟨hpsd', htr', hrep'⟩ := h'
    have hPSD : ∀ A : Matrix n n ℂ, A.PosSemidef →
        (ρ' * A).trace = (ext f A : ℂ) := by
      intro A hA
      have hc := scaleOf_pos hA
      have heff := effect_inv_scale_smul hA
      have hs : A = scaleOf A • ((scaleOf A)⁻¹ • A) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
      calc (ρ' * A).trace
          = (ρ' * (scaleOf A • ((scaleOf A)⁻¹ • A))).trace := by rw [← hs]
        _ = scaleOf A • (ρ' * ((scaleOf A)⁻¹ • A)).trace := by
            rw [mul_smul_comm, trace_smul]
        _ = scaleOf A • ((f ((scaleOf A)⁻¹ • A) : ℝ) : ℂ) := by
            rw [hrep' _ heff]
        _ = (ext f A : ℂ) := by
            rw [ext, Complex.real_smul]
            push_cast
            ring
    have hHerm : ∀ A : Matrix n n ℂ, A.IsHermitian →
        (ρ' * A).trace = (extH f A : ℂ) := by
      intro A hH
      have hpsd := shift_posSemidef hH
      have h1 := hPSD _ hpsd
      have hexp : ρ' * (A + shiftOf A • 1) = ρ' * A + shiftOf A • ρ' := by
        rw [mul_add, mul_smul_comm, mul_one]
      rw [hexp, trace_add, trace_smul, htr'] at h1
      rw [Complex.real_smul, mul_one] at h1
      have h3 : (ρ' * A).trace
          = (ext f (A + shiftOf A • 1) : ℂ) - (shiftOf A : ℂ) := by
        linear_combination h1
      rw [h3, extH]
      push_cast
      ring
    have hsame : ∀ A : Matrix n n ℂ, A.IsHermitian →
        ((ρ' - rho f) * A).trace = 0 := by
      intro A hH
      rw [sub_mul, trace_sub, hHerm A hH, trace_rho_mul hf hH, sub_self]
    have hentry : ∀ i j, (ρ' - rho f) i j = 0 := by
      intro i j
      have hS := hsame _ (SB_hermitian i j)
      have hT := hsame _ (TB_hermitian i j)
      rw [trace_mul_SB] at hS
      rw [trace_mul_TB] at hT
      have h5 : Complex.I * ((ρ' - rho f) j i - (ρ' - rho f) i j) = 0 := by
        linear_combination hT
      have h4 : (ρ' - rho f) j i = (ρ' - rho f) i j := by
        rcases mul_eq_zero.mp h5 with h | h
        · exact absurd h Complex.I_ne_zero
        · exact sub_eq_zero.mp h
      rw [h4] at hS
      linear_combination hS / 2
    have hzero : ρ' - rho f = 0 := by
      ext i j
      rw [Matrix.zero_apply]
      exact hentry i j
    exact sub_eq_zero.mp hzero

end Busch
end PDT

#print axioms PDT.Busch.busch
