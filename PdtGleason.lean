import Mathlib

/-!
# Gleason's theorem — the analytic core on the unit sphere of ℝ³

Gleason (1957), *Measures on the closed subspaces of a Hilbert space*,
J. Math. Mech. 6, 885–893, §2.  A *frame function* of weight `W` on the unit
sphere `S ⊂ ℝ³` is a function whose values on every orthonormal triple sum
to `W`.  Gleason's Theorem 2.8: every non-negative frame function is
*regular*, i.e. the restriction to `S` of a quadratic form.

This file follows Gleason's own elementary continuity argument (Lemmas 2.5,
2.6, 2.7 and the first half of Theorem 2.8) and states the harmonic-analysis
half (Theorem 2.3: continuous ⇒ regular) as a separate hypothesis-carrying
theorem.  Physics vocabulary appears only in docstrings.
-/

open scoped RealInnerProductSpace
open scoped Matrix

namespace PDT.Gleason

/-- Three-dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- A *weak frame function* of weight `W`: even, and summing to `W` on every
orthonormal triple.  No positivity is required (the class is closed under
subtraction, which is used to normalise the weight). -/
structure IsWeakFrame (f : E → ℝ) (W : ℝ) : Prop where
  even : ∀ x, f (-x) = f x
  sum_eq : ∀ x y z : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖z‖ = 1 →
    ⟪x, y⟫ = 0 → ⟪x, z⟫ = 0 → ⟪y, z⟫ = 0 → f x + f y + f z = W

/-- Gleason's frame function of weight `W`: a weak frame function that is
non-negative on the unit sphere. -/
structure IsFrameFunction (f : E → ℝ) (W : ℝ) : Prop extends IsWeakFrame f W where
  nonneg : ∀ x, ‖x‖ = 1 → 0 ≤ f x

/-- Gleason's *regular* frame functions: those given on the unit sphere by a
quadratic form `x ↦ ⟪x, A x⟫` with `A` a symmetric `3 × 3` matrix. -/
def IsRegular (f : E → ℝ) : Prop :=
  ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧
    ∀ x : E, ‖x‖ = 1 → f x = ⟪x, Matrix.toEuclideanLin A x⟫

/-! ### Elementary vector facts -/

theorem norm_eq_one_of_sq {v : E} (h : ‖v‖ ^ 2 = 1) : ‖v‖ = 1 := by
  have h0 := norm_nonneg v
  nlinarith

theorem inner_self_of_unit {v : E} (hv : ‖v‖ = 1) : ⟪v, v⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hv, one_pow]

theorem inner_eq_dot (x y : E) : ⟪x, y⟫ = dotProduct (WithLp.ofLp x) (WithLp.ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The cross product on `E`. -/
def cross (a b : E) : E := WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

theorem ofLp_cross (a b : E) :
    WithLp.ofLp (cross a b) = crossProduct (WithLp.ofLp a) (WithLp.ofLp b) := rfl

theorem inner_cross_left (a b : E) : ⟪a, cross a b⟫ = 0 := by
  rw [inner_eq_dot, ofLp_cross, dot_self_cross]

theorem inner_cross_right (a b : E) : ⟪b, cross a b⟫ = 0 := by
  rw [inner_eq_dot, ofLp_cross, dot_cross_self]

theorem inner_cross_cross (u v w x : E) :
    ⟪cross u v, cross w x⟫ = ⟪u, w⟫ * ⟪v, x⟫ - ⟪u, x⟫ * ⟪v, w⟫ := by
  simp only [inner_eq_dot, ofLp_cross]
  exact cross_dot_cross _ _ _ _

theorem norm_cross_sq (a b : E) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cross_cross, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm b a]
  ring

theorem cross_neg_right (a b : E) : cross a (-b) = -cross a b := by
  unfold cross
  rw [WithLp.ofLp_neg, map_neg, WithLp.toLp_neg]

/-- Every unit vector extends to an orthonormal triple. -/
theorem exists_orthonormal_triple (x : E) (hx : ‖x‖ = 1) :
    ∃ y z : E, ‖y‖ = 1 ∧ ‖z‖ = 1 ∧ ⟪x, y⟫ = 0 ∧ ⟪x, z⟫ = 0 ∧ ⟪y, z⟫ = 0 := by
  have hcard : Module.finrank ℝ E = Fintype.card (Fin 3) := by simp
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ => x)) := by
    refine ⟨fun i => by simpa using hx, ?_⟩
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp hi).trans
      (Set.mem_singleton_iff.mp hj).symm)) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have h0 : b 0 = x := hb 0 (Set.mem_singleton 0)
  have ho := b.orthonormal
  refine ⟨b 1, b 2, ho.1 1, ho.1 2, ?_, ?_, ?_⟩
  · rw [← h0]; exact ho.2 (by decide)
  · rw [← h0]; exact ho.2 (by decide)
  · exact ho.2 (by decide)

/-- An orthonormal pair extends to an orthonormal triple, explicitly by the
cross product. -/
theorem cross_unit_of_orthonormal {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫ = 0) : ‖cross x y‖ = 1 :=
  norm_eq_one_of_sq (by rw [norm_cross_sq, hx, hy, hxy]; norm_num)

/-! ### Closure properties of frame functions -/

namespace IsWeakFrame

variable {f g : E → ℝ} {W V : ℝ}

/-- Composition with any map preserving inner products and negation
(in particular any orthogonal transformation). -/
theorem comp (hf : IsWeakFrame f W) (σ : E → E)
    (hσ : ∀ x y, ⟪σ x, σ y⟫ = ⟪x, y⟫) (hneg : ∀ x, σ (-x) = -σ x) :
    IsWeakFrame (fun x => f (σ x)) W where
  even x := by simp only [hneg, hf.even]
  sum_eq x y z hx hy hz hxy hxz hyz := by
    have hn : ∀ v : E, ‖v‖ = 1 → ‖σ v‖ = 1 := fun v hv =>
      norm_eq_one_of_sq (by rw [← real_inner_self_eq_norm_sq, hσ, inner_self_of_unit hv])
    exact hf.sum_eq _ _ _ (hn x hx) (hn y hy) (hn z hz) (by rw [hσ, hxy]) (by rw [hσ, hxz])
      (by rw [hσ, hyz])

theorem add (hf : IsWeakFrame f W) (hg : IsWeakFrame g V) :
    IsWeakFrame (fun x => f x + g x) (W + V) where
  even x := by simp only [hf.even, hg.even]
  sum_eq x y z hx hy hz hxy hxz hyz := by
    have := hf.sum_eq x y z hx hy hz hxy hxz hyz
    have := hg.sum_eq x y z hx hy hz hxy hxz hyz
    linarith

theorem neg (hf : IsWeakFrame f W) : IsWeakFrame (fun x => -f x) (-W) where
  even x := by simp only [hf.even]
  sum_eq x y z hx hy hz hxy hxz hyz := by
    have := hf.sum_eq x y z hx hy hz hxy hxz hyz
    linarith

theorem smul (hf : IsWeakFrame f W) (c : ℝ) : IsWeakFrame (fun x => c * f x) (c * W) where
  even x := by simp only [hf.even]
  sum_eq x y z hx hy hz hxy hxz hyz := by
    have := hf.sum_eq x y z hx hy hz hxy hxz hyz
    rw [← this]; ring

theorem const (c : ℝ) : IsWeakFrame (fun _ => c) (3 * c) where
  even _ := rfl
  sum_eq _ _ _ _ _ _ _ _ _ := by ring

theorem sub_const (hf : IsWeakFrame f W) (c : ℝ) :
    IsWeakFrame (fun x => f x - c) (W - 3 * c) := by
  have := hf.add (const (-c))
  simpa [sub_eq_add_neg, mul_neg] using this

/-- The weight-zero normalisation. -/
theorem weight_zero (hf : IsWeakFrame f W) : IsWeakFrame (fun x => f x - W / 3) 0 := by
  have h := hf.sub_const (W / 3)
  rwa [show W - 3 * (W / 3) = 0 by ring] at h

end IsWeakFrame

/-- Evenness on the sphere is automatic from the triple condition. -/
theorem even_of_sum_eq {f : E → ℝ} {W : ℝ}
    (h : ∀ x y z : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖z‖ = 1 →
      ⟪x, y⟫ = 0 → ⟪x, z⟫ = 0 → ⟪y, z⟫ = 0 → f x + f y + f z = W)
    {x : E} (hx : ‖x‖ = 1) : f (-x) = f x := by
  obtain ⟨y, z, hy, hz, hxy, hxz, hyz⟩ := exists_orthonormal_triple x hx
  have h1 := h x y z hx hy hz hxy hxz hyz
  have h2 := h (-x) y z (by simpa using hx) hy hz (by simpa using hxy) (by simpa using hxz) hyz
  linarith

namespace IsFrameFunction

variable {f : E → ℝ} {W : ℝ}

theorem comp (hf : IsFrameFunction f W) (σ : E → E)
    (hσ : ∀ x y, ⟪σ x, σ y⟫ = ⟪x, y⟫) (hneg : ∀ x, σ (-x) = -σ x) :
    IsFrameFunction (fun x => f (σ x)) W where
  toIsWeakFrame := hf.toIsWeakFrame.comp σ hσ hneg
  nonneg x hx := hf.nonneg _ (norm_eq_one_of_sq
    (by rw [← real_inner_self_eq_norm_sq, hσ, inner_self_of_unit hx]))

/-- `frame_comp_orthogonal`: a frame function composed with an orthogonal
transformation is a frame function of the same weight. -/
theorem comp_isometry (hf : IsFrameFunction f W) (e : E ≃ₗᵢ[ℝ] E) :
    IsFrameFunction (fun x => f (e x)) W :=
  hf.comp e (fun x y => e.inner_map_map x y) (fun x => by simp)

theorem add {g : E → ℝ} {V : ℝ} (hf : IsFrameFunction f W) (hg : IsFrameFunction g V) :
    IsFrameFunction (fun x => f x + g x) (W + V) where
  toIsWeakFrame := hf.toIsWeakFrame.add hg.toIsWeakFrame
  nonneg x hx := add_nonneg (hf.nonneg x hx) (hg.nonneg x hx)

/-- `bounded_of_nonneg`: a non-negative frame function is bounded by its weight. -/
theorem le_weight (hf : IsFrameFunction f W) {x : E} (hx : ‖x‖ = 1) : f x ≤ W := by
  obtain ⟨y, z, hy, hz, hxy, hxz, hyz⟩ := exists_orthonormal_triple x hx
  have := hf.sum_eq x y z hx hy hz hxy hxz hyz
  have := hf.nonneg y hy
  have := hf.nonneg z hz
  linarith

theorem weight_nonneg (hf : IsFrameFunction f W) : 0 ≤ W := by
  have hx : ‖(PiLp.single 2 (0 : Fin 3) (1 : ℝ) : E)‖ = 1 := by
    rw [PiLp.norm_single]; simp
  exact (hf.nonneg _ hx).trans (hf.le_weight hx)

/-- The weight-zero normalisation of a non-negative frame function is bounded
by the weight in absolute value. -/
theorem abs_sub_third_le (hf : IsFrameFunction f W) {x : E} (hx : ‖x‖ = 1) :
    |f x - W / 3| ≤ W := by
  have := hf.nonneg x hx
  have := hf.le_weight hx
  have := hf.weight_nonneg
  rw [abs_le]; constructor <;> linarith

end IsFrameFunction

/-! ### Great circles -/

/-- The point at angle `θ` on the great circle through the orthonormal pair `u, v`. -/
noncomputable def circ (u v : E) (θ : ℝ) : E := Real.cos θ • u + Real.sin θ • v

theorem inner_circ_right (w u v : E) (θ : ℝ) :
    ⟪w, circ u v θ⟫ = Real.cos θ * ⟪w, u⟫ + Real.sin θ * ⟪w, v⟫ := by
  simp only [circ, inner_add_right, real_inner_smul_right]

theorem inner_circ_left (w u v : E) (θ : ℝ) :
    ⟪circ u v θ, w⟫ = Real.cos θ * ⟪u, w⟫ + Real.sin θ * ⟪v, w⟫ := by
  simp only [circ, inner_add_left, real_inner_smul_left]

theorem inner_circ_circ {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
    (θ φ : ℝ) : ⟪circ u v θ, circ u v φ⟫ = Real.cos (θ - φ) := by
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  simp only [inner_circ_left, inner_circ_right, inner_self_of_unit hu, inner_self_of_unit hv,
    huv, hvu, Real.cos_sub]
  ring

theorem norm_circ {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (θ : ℝ) :
    ‖circ u v θ‖ = 1 :=
  norm_eq_one_of_sq (by
    rw [← real_inner_self_eq_norm_sq, inner_circ_circ hu hv huv, sub_self, Real.cos_zero])

theorem inner_circ_quarter {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
    (θ : ℝ) : ⟪circ u v θ, circ u v (θ + Real.pi / 2)⟫ = 0 := by
  rw [inner_circ_circ hu hv huv, show θ - (θ + Real.pi / 2) = -(Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_pi_div_two]

theorem inner_circ_of_orth {w u v : E} (hwu : ⟪w, u⟫ = 0) (hwv : ⟪w, v⟫ = 0) (θ : ℝ) :
    ⟪w, circ u v θ⟫ = 0 := by
  rw [inner_circ_right, hwu, hwv]; ring

@[simp] theorem circ_zero (u v : E) : circ u v 0 = u := by simp [circ]

theorem circ_pi_div_two (u v : E) : circ u v (Real.pi / 2) = v := by simp [circ]

theorem circ_add_pi (u v : E) (θ : ℝ) : circ u v (θ + Real.pi) = -circ u v θ := by
  simp only [circ, Real.cos_add_pi, Real.sin_add_pi, neg_smul, neg_add]

/-- The (true) circle lemma: along the great circle through an orthonormal pair
`u, v` with third vector `w`, orthogonal pairs of points have the constant sum
`W - f w`; together with evenness (period `π`) this is all a single great
circle knows. -/
theorem IsWeakFrame.circle_pair_sum {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W)
    {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) (θ : ℝ) :
    f (circ u v θ) + f (circ u v (θ + Real.pi / 2)) = W - f w := by
  have h := hf.sum_eq (circ u v θ) (circ u v (θ + Real.pi / 2)) w (norm_circ hu hv huv θ)
    (norm_circ hu hv huv _) hw (inner_circ_quarter hu hv huv θ)
    (by rw [inner_circ_left, huw, hvw]; ring) (by rw [inner_circ_left, huw, hvw]; ring)
  linarith

theorem IsWeakFrame.circle_periodic {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W)
    (u v : E) (θ : ℝ) : f (circ u v (θ + Real.pi)) = f (circ u v θ) := by
  rw [circ_add_pi, hf.even]

/-- Two orthonormal pairs `(a, a')`, `(b, b')` orthogonal to a common unit
vector `n` (so spanning the same plane) have equal pair sums. -/
theorem IsWeakFrame.pair_sum_eq {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W)
    {a a' b b' n : E} (ha : ‖a‖ = 1) (ha' : ‖a'‖ = 1) (hb : ‖b‖ = 1) (hb' : ‖b'‖ = 1)
    (hn : ‖n‖ = 1) (haa' : ⟪a, a'⟫ = 0) (hbb' : ⟪b, b'⟫ = 0)
    (hna : ⟪a, n⟫ = 0) (hna' : ⟪a', n⟫ = 0) (hnb : ⟪b, n⟫ = 0) (hnb' : ⟪b', n⟫ = 0) :
    f a + f a' = f b + f b' := by
  have h1 := hf.sum_eq a a' n ha ha' hn haa' hna hna'
  have h2 := hf.sum_eq b b' n hb hb' hn hbb' hnb hnb'
  linarith

/-! ### Normalisation -/

/-- `v / ‖v‖`. -/
noncomputable def unitOf (v : E) : E := ‖v‖⁻¹ • v

theorem norm_unitOf {v : E} (hv : v ≠ 0) : ‖unitOf v‖ = 1 := by
  rw [unitOf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem inner_unitOf_right (w v : E) : ⟪w, unitOf v⟫ = ‖v‖⁻¹ * ⟪w, v⟫ := by
  rw [unitOf, real_inner_smul_right]

theorem inner_unitOf_left (w v : E) : ⟪unitOf v, w⟫ = ‖v‖⁻¹ * ⟪v, w⟫ := by
  rw [unitOf, real_inner_smul_left]

theorem ne_zero_of_norm_sq_pos {v : E} (h : 0 < ‖v‖ ^ 2) : v ≠ 0 := by
  rintro rfl; simp at h

/-! ### EW great circles (Gleason §2.4)

Fix a unit vector `p` (the north pole).  Through every unit vector `x ≠ ±p`
there is a unique great circle tangent to the circle of latitude through `x`,
the *EW great circle* through `x`; its pole is the horizontal component
`ewPole p x = p - ⟪p, x⟫ x` of `p`, and it meets the equator at
`ewEq p x = unitOf (cross p x)`.  A unit vector `y` lies on it iff
`⟪y, p⟫ = ⟪p, x⟫ ⟪y, x⟫`. -/

section EW

variable (p : E)

/-- `y` lies on the EW great circle through `x` (pole `p`). -/
def OnEW (x y : E) : Prop := ⟪y, p⟫ = ⟪p, x⟫ * ⟪y, x⟫

/-- The unnormalised pole of the EW great circle through `x`. -/
noncomputable def ewPole (x : E) : E := p - ⟪p, x⟫ • x

/-- The equatorial point of the EW great circle through `x`. -/
noncomputable def ewEq (x : E) : E := unitOf (cross p x)

/-- The orthogonal partner of `y` on the EW great circle through `x`. -/
noncomputable def ewPartner (x y : E) : E := cross (unitOf (ewPole p x)) y

variable {p}

theorem inner_ewPole (x y : E) : ⟪y, ewPole p x⟫ = ⟪y, p⟫ - ⟪p, x⟫ * ⟪y, x⟫ := by
  simp only [ewPole, inner_sub_right, real_inner_smul_right]

theorem onEW_iff (x y : E) : OnEW p x y ↔ ⟪y, ewPole p x⟫ = 0 := by
  rw [inner_ewPole, OnEW, sub_eq_zero]

theorem norm_ewPole_sq (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) :
    ‖ewPole p x‖ ^ 2 = 1 - ⟪p, x⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_ewPole]
  simp only [ewPole, inner_sub_left, real_inner_smul_left, inner_self_of_unit hp,
    inner_self_of_unit hx, real_inner_comm p x]
  ring

theorem ewPole_ne_zero (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1) :
    ewPole p x ≠ 0 :=
  ne_zero_of_norm_sq_pos (by rw [norm_ewPole_sq hp hx]; linarith)

theorem onEW_self (x : E) (hx : ‖x‖ = 1) : OnEW p x x := by
  rw [OnEW, inner_self_of_unit hx, real_inner_comm]; ring

theorem norm_cross_pole_sq (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) :
    ‖cross p x‖ ^ 2 = 1 - ⟪p, x⟫ ^ 2 := by
  rw [norm_cross_sq, hp, hx]; ring

theorem norm_ewEq (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1) :
    ‖ewEq p x‖ = 1 :=
  norm_unitOf (ne_zero_of_norm_sq_pos (by rw [norm_cross_pole_sq hp hx]; linarith))

theorem inner_ewEq_pole (x : E) : ⟪ewEq p x, p⟫ = 0 := by
  rw [ewEq, inner_unitOf_left, real_inner_comm, inner_cross_left, mul_zero]

theorem inner_ewEq_self (x : E) : ⟪x, ewEq p x⟫ = 0 := by
  rw [ewEq, inner_unitOf_right, inner_cross_right, mul_zero]

theorem onEW_ewEq (x : E) : OnEW p x (ewEq p x) := by
  rw [OnEW, inner_ewEq_pole, real_inner_comm x (ewEq p x), inner_ewEq_self, mul_zero]

/-- Parametrisation of the EW great circle through `x`. -/
theorem onEW_circ {x : E} (hx : ‖x‖ = 1) (t : ℝ) : OnEW p x (circ x (ewEq p x) t) := by
  rw [OnEW, inner_circ_left, inner_circ_left, inner_ewEq_pole, inner_self_of_unit hx,
    real_inner_comm x (ewEq p x), inner_ewEq_self, real_inner_comm p x]
  ring

theorem inner_circ_ew_pole {x : E} (t : ℝ) : ⟪circ x (ewEq p x) t, p⟫ = Real.cos t * ⟪x, p⟫ := by
  rw [inner_circ_left, inner_ewEq_pole]; ring

theorem inner_ewPartner_self (x y : E) : ⟪y, ewPartner p x y⟫ = 0 := inner_cross_right _ _

theorem onEW_ewPartner (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1) (y : E) :
    OnEW p x (ewPartner p x y) := by
  rw [onEW_iff, ewPartner]
  have h := inner_cross_left (unitOf (ewPole p x)) y
  rw [real_inner_comm, inner_unitOf_right] at h
  exact (mul_eq_zero.mp h).resolve_left
    (inv_ne_zero (norm_ne_zero_iff.mpr (ewPole_ne_zero hp hx hx1)))

theorem norm_ewPartner (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1)
    {y : E} (hy : ‖y‖ = 1) (hxy : OnEW p x y) : ‖ewPartner p x y‖ = 1 := by
  apply cross_unit_of_orthonormal (norm_unitOf (ewPole_ne_zero hp hx hx1)) hy
  rw [inner_unitOf_left, real_inner_comm, (onEW_iff x y).mp hxy, mul_zero]

/-- Frame identity on the EW great circle through `x`: two orthogonal unit
vectors on it have pair sum `W - f (unitOf (ewPole p x))`. -/
theorem IsWeakFrame.ew_pair {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W) (hp : ‖p‖ = 1)
    {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1) {y y' : E} (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (hyy' : ⟪y, y'⟫ = 0) (h1 : OnEW p x y) (h2 : OnEW p x y') :
    f y + f y' = W - f (unitOf (ewPole p x)) := by
  have hn := norm_unitOf (ewPole_ne_zero hp hx hx1)
  have e1 : ⟪y, unitOf (ewPole p x)⟫ = 0 := by
    rw [inner_unitOf_right, (onEW_iff x y).mp h1, mul_zero]
  have e2 : ⟪y', unitOf (ewPole p x)⟫ = 0 := by
    rw [inner_unitOf_right, (onEW_iff x y').mp h2, mul_zero]
  have := hf.sum_eq y y' _ hy hy' hn hyy' e1 e2
  linarith

/-- Gleason's basic relation: `f x + f (ewEq p x) = f y + f y'` for any orthogonal
unit pair `y, y'` on the EW circle through `x`. -/
theorem IsWeakFrame.ew_pair_eq_top {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W) (hp : ‖p‖ = 1)
    {x : E} (hx : ‖x‖ = 1) (hx1 : ⟪p, x⟫ ^ 2 < 1) {y y' : E} (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (hyy' : ⟪y, y'⟫ = 0) (h1 : OnEW p x y) (h2 : OnEW p x y') :
    f y + f y' = f x + f (ewEq p x) := by
  rw [hf.ew_pair hp hx hx1 hy hy' hyy' h1 h2,
    hf.ew_pair hp hx hx1 hx (norm_ewEq hp hx hx1) (inner_ewEq_self x) (onEW_self x hx)
      (onEW_ewEq x)]

end EW

/-! ### Further EW facts -/

theorem sq_lt_one_of_north {p x : E} (h0 : 0 ≤ ⟪x, p⟫) (h1 : ⟪x, p⟫ < 1) : ⟪p, x⟫ ^ 2 < 1 := by
  rw [real_inner_comm]; nlinarith

theorem inner_sq_le_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ ^ 2 ≤ 1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at h
  have := abs_nonneg ⟪x, y⟫
  nlinarith [sq_abs ⟪x, y⟫]

/-- A point of the EW circle through `r ≠ ±p` is itself `≠ ±p`. -/
theorem inner_pole_sq_lt_of_onEW {p r t : E} (hr : ‖r‖ = 1) (ht : ‖t‖ = 1)
    (hr1 : ⟪p, r⟫ ^ 2 < 1) (h : OnEW p r t) : ⟪p, t⟫ ^ 2 < 1 := by
  rw [real_inner_comm, h, mul_pow]
  have := inner_sq_le_one ht hr
  nlinarith [sq_nonneg ⟪p, r⟫]

theorem cross_self' (a : E) : cross a a = 0 := by
  unfold cross; rw [cross_self]; rfl

/-- A unit vector orthogonal to `u` and to an arbitrary `s`. -/
theorem exists_unit_orth_two (u s : E) (hu : ‖u‖ = 1) :
    ∃ v : E, ‖v‖ = 1 ∧ ⟪v, u⟫ = 0 ∧ ⟪v, s⟫ = 0 := by
  by_cases hc : cross u s = 0
  · obtain ⟨v, -, hv, -, hvu, -, -⟩ := exists_orthonormal_triple u hu
    refine ⟨v, hv, by rw [real_inner_comm]; exact hvu, ?_⟩
    -- `cross u s = 0` forces `s = ⟪u, s⟫ • u`
    have hn : ‖s - ⟪u, s⟫ • u‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        inner_self_of_unit hu, real_inner_comm u s]
      have := norm_cross_sq u s
      rw [hc, norm_zero, hu] at this
      rw [real_inner_self_eq_norm_sq]; nlinarith
    have hs : s = ⟪u, s⟫ • u := by
      have := (sq_eq_zero_iff.mp hn)
      rw [norm_eq_zero, sub_eq_zero] at this; exact this
    rw [hs, real_inner_smul_right, real_inner_comm u v, hvu, mul_zero]
  · refine ⟨unitOf (cross u s), norm_unitOf hc, ?_, ?_⟩
    · rw [inner_unitOf_left, real_inner_comm, inner_cross_left, mul_zero]
    · rw [inner_unitOf_left, real_inner_comm, inner_cross_right, mul_zero]

/-! ### Gram–Schmidt partners in a plane -/

theorem unitOf_smul_of_pos {s : ℝ} (hs : 0 < s) (v : E) : unitOf (s • v) = unitOf v := by
  rw [unitOf, unitOf, norm_smul, Real.norm_eq_abs, abs_of_pos hs, smul_smul, mul_inv,
    mul_comm s⁻¹, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]

theorem unitOf_of_norm_one {v : E} (hv : ‖v‖ = 1) : unitOf v = v := by
  rw [unitOf, hv, inv_one, one_smul]

theorem gs1_ne_zero {r x : E} (hr : ‖r‖ = 1) (hx : ‖x‖ = 1) (h : ⟪x, r⟫ ^ 2 < 1) :
    x - ⟪x, r⟫ • r ≠ 0 :=
  ne_zero_of_norm_sq_pos (by
    rw [norm_sub_sq_real, hx, norm_smul, Real.norm_eq_abs, hr, mul_one, sq_abs,
      real_inner_smul_right]
    nlinarith)

theorem gs2_ne_zero {r x : E} (hr : ‖r‖ = 1) (hx : ‖x‖ = 1) (h : ⟪x, r⟫ ^ 2 < 1) :
    ⟪r, x⟫ • x - r ≠ 0 :=
  ne_zero_of_norm_sq_pos (by
    rw [norm_sub_sq_real, hr, norm_smul, Real.norm_eq_abs, hx, mul_one, sq_abs,
      real_inner_smul_left, real_inner_comm x r]
    nlinarith)

theorem norm_gs1 {r x : E} (hr : ‖r‖ = 1) (hx : ‖x‖ = 1) (h : ⟪x, r⟫ ^ 2 < 1) :
    ‖unitOf (x - ⟪x, r⟫ • r)‖ = 1 := norm_unitOf (gs1_ne_zero hr hx h)

theorem norm_gs2 {r x : E} (hr : ‖r‖ = 1) (hx : ‖x‖ = 1) (h : ⟪x, r⟫ ^ 2 < 1) :
    ‖unitOf (⟪r, x⟫ • x - r)‖ = 1 := norm_unitOf (gs2_ne_zero hr hx h)

/-- The Gram–Schmidt partners of `r` and of `x` in the plane they span form two
orthonormal bases of that plane, hence have equal pair sums. -/
theorem IsWeakFrame.plane_pair_sum {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W) {r x : E}
    (hr : ‖r‖ = 1) (hx : ‖x‖ = 1) (h : ⟪x, r⟫ ^ 2 < 1) :
    f r + f (unitOf (x - ⟪x, r⟫ • r)) = f x + f (unitOf (⟪r, x⟫ • x - r)) := by
  have hrx : ⟪r, x⟫ = ⟪x, r⟫ := real_inner_comm x r
  have hn3 : ‖cross r x‖ ^ 2 = 1 - ⟪x, r⟫ ^ 2 := by rw [norm_cross_sq, hr, hx, hrx]; ring
  have h3 := ne_zero_of_norm_sq_pos (by rw [hn3]; linarith)
  refine hf.pair_sum_eq hr (norm_gs1 hr hx h) hx (norm_gs2 hr hx h) (norm_unitOf h3)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [inner_unitOf_right, inner_sub_right, real_inner_smul_right, inner_self_of_unit hr, hrx]
    ring
  · rw [inner_unitOf_right, inner_sub_right, real_inner_smul_right, inner_self_of_unit hx, hrx]
    ring
  · rw [inner_unitOf_right, inner_cross_left, mul_zero]
  · rw [inner_unitOf_left, inner_unitOf_right, inner_sub_left, real_inner_smul_left,
      inner_cross_right, inner_cross_left]
    ring
  · rw [inner_unitOf_right, inner_cross_right, mul_zero]
  · rw [inner_unitOf_left, inner_unitOf_right, inner_sub_left, real_inner_smul_left,
      inner_cross_right, inner_cross_left]
    ring

/-! ### Oscillation (Gleason §2.4–2.7) -/

/-- `OscLE f U α`: `f` varies by at most `α` on the unit vectors of `U`. -/
def OscLE (f : E → ℝ) (U : Set E) (α : ℝ) : Prop :=
  ∀ x ∈ U, ‖x‖ = 1 → ∀ y ∈ U, ‖y‖ = 1 → f x - f y ≤ α

theorem OscLE.mono {f : E → ℝ} {U V : Set E} {α : ℝ} (h : OscLE f U α) (hVU : V ⊆ U) :
    OscLE f V α := fun x hx hx1 y hy hy1 => h x (hVU hx) hx1 y (hVU hy) hy1

theorem OscLE.of_le {f : E → ℝ} {U : Set E} {α β : ℝ} (h : OscLE f U α) (hab : α ≤ β) :
    OscLE f U β := fun x hx hx1 y hy hy1 => (h x hx hx1 y hy hy1).trans hab

/-- **Gleason, Lemma 2.5** (geometric).  For a unit vector `z` in the closed
northern hemisphere, `z ≠ p`, the set of `x` in the northern hemisphere from
which `z` is reached in two EW steps (`y` on the EW circle through `x`, `z` on
the EW circle through `y`) has non-empty interior. -/
theorem ew_two_step_interior {p : E} (hp : ‖p‖ = 1) {z : E} (hz : ‖z‖ = 1)
    (hz0 : 0 ≤ ⟪z, p⟫) (hz1 : ⟪z, p⟫ < 1) :
    ∃ U : Set E, IsOpen U ∧ (∃ x ∈ U, ‖x‖ = 1) ∧ ∀ x ∈ U, ‖x‖ = 1 →
      0 ≤ ⟪x, p⟫ ∧ ⟪x, p⟫ < 1 ∧
      ∃ y : E, ‖y‖ = 1 ∧ 0 ≤ ⟪y, p⟫ ∧ ⟪y, p⟫ < 1 ∧ OnEW p x y ∧ OnEW p y z := by
  have hc : Continuous fun x : E => ⟪x, p⟫ := continuous_id.inner continuous_const
  -- the witness `x₀ = unitOf (z + p)`, on the meridian of `z`, above `z`
  have hzp : ‖z + p‖ ^ 2 = 2 + 2 * ⟪z, p⟫ := by rw [norm_add_sq_real, hz, hp]; ring
  have hzp0 : z + p ≠ 0 := ne_zero_of_norm_sq_pos (by rw [hzp]; linarith)
  have hne : ‖z + p‖ ≠ 0 := norm_ne_zero_iff.mpr hzp0
  have hx₀ : ‖unitOf (z + p)‖ = 1 := norm_unitOf hzp0
  have hk2 : ‖z + p‖⁻¹ ^ 2 * (2 + 2 * ⟪z, p⟫) = 1 := by
    rw [inv_pow, ← hzp, inv_mul_cancel₀ (pow_ne_zero 2 hne)]
  have hx₀p : ⟪unitOf (z + p), p⟫ = ‖z + p‖⁻¹ * (⟪z, p⟫ + 1) := by
    rw [inner_unitOf_left, inner_add_left, inner_self_of_unit hp]
  have hx₀z : ⟪z, unitOf (z + p)⟫ = ‖z + p‖⁻¹ * (1 + ⟪z, p⟫) := by
    rw [inner_unitOf_right, inner_add_right, inner_self_of_unit hz]
  have hkpos : 0 < ‖z + p‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hzp0)
  have hsq : (‖z + p‖⁻¹ * (⟪z, p⟫ + 1)) ^ 2 = (⟪z, p⟫ + 1) / 2 := by
    linear_combination ((⟪z, p⟫ + 1) / 2) * hk2
  have hx₀p0 : 0 < ⟪unitOf (z + p), p⟫ := by
    rw [hx₀p]; exact mul_pos hkpos (by linarith)
  have hx₀p1 : ⟪unitOf (z + p), p⟫ < 1 := by
    rw [hx₀p]; nlinarith [mul_pos hkpos (show (0:ℝ) < ⟪z, p⟫ + 1 by linarith)]
  rcases hz0.lt_or_eq with hs | hs
  · -- `0 < ⟪z, p⟫`: the intermediate-value argument along the EW circle through `x`
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E → ℝ, Ψ = fun y => ⟪z, p⟫ - ⟪p, y⟫ * ⟪z, y⟫ := ⟨_, rfl⟩
    have hΨa : ∀ y, Ψ y = ⟪z, p⟫ - ⟪p, y⟫ * ⟪z, y⟫ := fun y => by rw [hΨ]
    have hΨc : Continuous Ψ := by
      rw [hΨ]
      exact continuous_const.sub ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id))
    refine ⟨{x | 0 < ⟪x, p⟫ ∧ ⟪x, p⟫ < 1 ∧ Ψ x < 0}, ?_,
      ⟨unitOf (z + p), ⟨hx₀p0, hx₀p1, ?_⟩, hx₀⟩, ?_⟩
    · exact (isOpen_lt continuous_const hc).inter
        ((isOpen_lt hc continuous_const).inter (isOpen_lt hΨc continuous_const))
    · rw [hΨa, real_inner_comm (unitOf (z + p)) p, hx₀p, hx₀z]
      have : ‖z + p‖⁻¹ * (⟪z, p⟫ + 1) * (‖z + p‖⁻¹ * (1 + ⟪z, p⟫)) = (⟪z, p⟫ + 1) / 2 := by
        linear_combination ((⟪z, p⟫ + 1) / 2) * hk2
      rw [this]; linarith
    · rintro x ⟨hx0, hx1, hΨx⟩ hx
      refine ⟨hx0.le, hx1, ?_⟩
      have hx1' : ⟪p, x⟫ ^ 2 < 1 := sq_lt_one_of_north hx0.le hx1
      have he := norm_ewEq hp hx hx1'
      have hxe : ⟪x, ewEq p x⟫ = 0 := inner_ewEq_self x
      have hφc : Continuous fun t : ℝ => Ψ (circ x (ewEq p x) t) :=
        hΨc.comp ((Real.continuous_cos.smul continuous_const).add
          (Real.continuous_sin.smul continuous_const))
      have h0 : Ψ (circ x (ewEq p x) 0) < 0 := by rwa [circ_zero]
      have h1 : 0 < Ψ (circ x (ewEq p x) (Real.pi / 2)) := by
        rw [circ_pi_div_two, hΨa, real_inner_comm (ewEq p x) p, inner_ewEq_pole, zero_mul,
          sub_zero]
        exact hs
      obtain ⟨t₀, ht₀, hφt₀⟩ := intermediate_value_Icc (by positivity : (0:ℝ) ≤ Real.pi / 2)
        hφc.continuousOn (show (0:ℝ) ∈ Set.Icc _ _ from Set.mem_Icc.mpr ⟨h0.le, h1.le⟩)
      refine ⟨circ x (ewEq p x) t₀, norm_circ hx he hxe t₀, ?_, ?_, onEW_circ hx t₀, ?_⟩
      · rw [inner_circ_ew_pole]
        exact mul_nonneg (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [ht₀.1, Real.pi_pos], ht₀.2⟩) hx0.le
      · rw [inner_circ_ew_pole]
        nlinarith [Real.cos_le_one t₀, hx0, hx1]
      · rw [OnEW, ← sub_eq_zero, ← hΨa]
        exact hφt₀
  · -- `⟪z, p⟫ = 0`: `z` is on the equator, and one EW step reaches the equator
    refine ⟨{x | 0 < ⟪x, p⟫ ∧ ⟪x, p⟫ < 1}, (isOpen_lt continuous_const hc).inter
      (isOpen_lt hc continuous_const), ⟨unitOf (z + p), ⟨hx₀p0, hx₀p1⟩, hx₀⟩, ?_⟩
    rintro x ⟨hx0, hx1⟩ hx
    have hx1' := sq_lt_one_of_north hx0.le hx1
    refine ⟨hx0.le, hx1, ewEq p x, norm_ewEq hp hx hx1', (inner_ewEq_pole x).symm.le,
      by rw [inner_ewEq_pole]; norm_num, onEW_ewEq x, ?_⟩
    rw [OnEW, real_inner_comm (ewEq p x) p, inner_ewEq_pole, zero_mul, ← hs]

/-- **Gleason, Lemma 2.6.**  If `f` is a frame function with oscillation `≤ α`
on a neighbourhood `U` of `p`, then every point `q` of the great circle with
pole `p` has a neighbourhood on which the oscillation is `≤ 2α`. -/
theorem osc_polar_circle {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W) {p : E} (hp : ‖p‖ = 1)
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U) {α : ℝ} (hα : OscLE f U α)
    {q : E} (hq : ‖q‖ = 1) (hqp : ⟪q, p⟫ = 0) :
    ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ OscLE f V (2 * α) := by
  -- Step 1: a point `w = unitOf (p + c • q)` of the meridian of `q`, inside `U`
  have hcont : ContinuousAt (fun c : ℝ => unitOf (p + c • q)) 0 := by
    have hg : Continuous fun c : ℝ => p + c • q :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hne : ‖p + (0:ℝ) • q‖ ≠ 0 := by rw [zero_smul, add_zero, hp]; exact one_ne_zero
    exact (hg.norm.continuousAt.inv₀ hne).smul hg.continuousAt
  have hw0 : unitOf (p + (0:ℝ) • q) = p := by rw [zero_smul, add_zero, unitOf_of_norm_one hp]
  have hev : ∀ᶠ c in nhds (0:ℝ), unitOf (p + c • q) ∈ U :=
    hcont.preimage_mem_nhds (by
      show U ∈ nhds (unitOf (p + (0:ℝ) • q))
      rw [hw0]; exact hU.mem_nhds hpU)
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ε / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hwU : unitOf (p + c • q) ∈ U :=
    hεU (by rw [Real.dist_eq, sub_zero, abs_of_pos hc0, hcdef]; linarith)
  -- Step 2: the point `r = unitOf (q - c • p)` of the meridian, south of `q`
  have hqc : ‖q - c • p‖ ^ 2 = 1 + c ^ 2 := by
    rw [norm_sub_sq_real, hq, norm_smul, Real.norm_eq_abs, hp, mul_one, sq_abs,
      real_inner_smul_right, hqp]
    ring
  have hqc0 : q - c • p ≠ 0 := ne_zero_of_norm_sq_pos (by rw [hqc]; positivity)
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = ‖q - c • p‖⁻¹ := ⟨_, rfl⟩
  have hkpos : 0 < k := by rw [hkdef]; exact inv_pos.mpr (norm_pos_iff.mpr hqc0)
  have hkk : k * k * (1 + c ^ 2) = 1 := by
    rw [hkdef, ← sq, inv_pow, ← hqc, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hqc0))]
  obtain ⟨r, hrdef⟩ : ∃ r : E, r = unitOf (q - c • p) := ⟨_, rfl⟩
  have hr : ‖r‖ = 1 := by rw [hrdef]; exact norm_unitOf hqc0
  have hr' : r = k • (q - c • p) := by rw [hrdef, hkdef]; rfl
  have hqr : ⟪q, r⟫ = k := by
    rw [hr', real_inner_smul_right, inner_sub_right, inner_self_of_unit hq,
      real_inner_smul_right, hqp]
    ring
  have hrq : ⟪r, q⟫ = k := by rw [real_inner_comm]; exact hqr
  have hqr1 : ⟪q, r⟫ ^ 2 < 1 := by
    rw [hqr]; nlinarith [mul_pos (mul_pos hkpos hkpos) (mul_pos hc0 hc0)]
  -- Step 3: at `q` the Gram–Schmidt partners are `w` and `p`
  have hRq : unitOf (q - ⟪q, r⟫ • r) = unitOf (p + c • q) := by
    rw [hqr, hr', smul_smul]
    have e : q - (k * k) • (q - c • p) = (k * k * c) • (p + c • q) := by
      have h1 : (1:ℝ) - k * k = k * k * c * c := by linear_combination (-1 : ℝ) * hkk
      rw [show q - (k * k) • (q - c • p) = (1 - k * k) • q + (k * k * c) • p by module, h1]
      module
    rw [e, unitOf_smul_of_pos (mul_pos (mul_pos hkpos hkpos) hc0)]
  have hQq : unitOf (⟪r, q⟫ • q - r) = p := by
    rw [hrq, hr', show k • q - k • (q - c • p) = (k * c) • p by module,
      unitOf_smul_of_pos (mul_pos hkpos hc0), unitOf_of_norm_one hp]
  -- Step 4: continuity of the partners at `q` gives the neighbourhood `V`
  have hcR : ContinuousAt (fun x : E => unitOf (x - ⟪x, r⟫ • r)) q := by
    have hg : Continuous fun x : E => x - ⟪x, r⟫ • r :=
      continuous_id.sub ((continuous_id.inner continuous_const).smul continuous_const)
    have hne : ‖q - ⟪q, r⟫ • r‖ ≠ 0 := norm_ne_zero_iff.mpr (gs1_ne_zero hr hq hqr1)
    exact (hg.norm.continuousAt.inv₀ hne).smul hg.continuousAt
  have hcQ : ContinuousAt (fun x : E => unitOf (⟪r, x⟫ • x - r)) q := by
    have hg : Continuous fun x : E => ⟪r, x⟫ • x - r :=
      ((continuous_const.inner continuous_id).smul continuous_id).sub continuous_const
    have hne : ‖⟪r, q⟫ • q - r‖ ≠ 0 := norm_ne_zero_iff.mpr (gs2_ne_zero hr hq hqr1)
    exact (hg.norm.continuousAt.inv₀ hne).smul hg.continuousAt
  have hev1 : ∀ᶠ x in nhds q, unitOf (x - ⟪x, r⟫ • r) ∈ U :=
    hcR.preimage_mem_nhds (by
      show U ∈ nhds (unitOf (q - ⟪q, r⟫ • r))
      rw [hRq]; exact hU.mem_nhds hwU)
  have hev2 : ∀ᶠ x in nhds q, unitOf (⟪r, x⟫ • x - r) ∈ U :=
    hcQ.preimage_mem_nhds (by
      show U ∈ nhds (unitOf (⟪r, q⟫ • q - r))
      rw [hQq]; exact hU.mem_nhds hpU)
  have hev3 : ∀ᶠ x in nhds q, ⟪x, r⟫ ^ 2 < 1 :=
    (isOpen_lt ((continuous_id.inner continuous_const).pow 2) continuous_const).mem_nhds hqr1
  obtain ⟨V, hVsub, hVo, hqV⟩ := mem_nhds_iff.mp ((hev1.and hev2).and hev3)
  refine ⟨V, hVo, hqV, ?_⟩
  intro x₁ hx₁V hx₁ x₂ hx₂V hx₂
  obtain ⟨⟨hR₁, hQ₁⟩, h₁⟩ := hVsub hx₁V
  obtain ⟨⟨hR₂, hQ₂⟩, h₂⟩ := hVsub hx₂V
  have e₁ := hf.plane_pair_sum hr hx₁ h₁
  have e₂ := hf.plane_pair_sum hr hx₂ h₂
  have a₁ := hα _ hR₁ (norm_gs1 hr hx₁ h₁) _ hR₂ (norm_gs1 hr hx₂ h₂)
  have a₂ := hα _ hQ₂ (norm_gs2 hr hx₂ h₂) _ hQ₁ (norm_gs2 hr hx₁ h₁)
  linarith

/-- **Gleason, Lemma 2.7.**  If `f` is a frame function with oscillation `≤ α`
on an open set `U` containing a unit vector, then every unit vector has a
neighbourhood on which the oscillation is `≤ 4α`. -/
theorem osc_everywhere {f : E → ℝ} {W : ℝ} (hf : IsWeakFrame f W) {U : Set E} (hU : IsOpen U)
    {u : E} (hu : ‖u‖ = 1) (huU : u ∈ U) {α : ℝ} (hα : OscLE f U α)
    {s : E} (hs : ‖s‖ = 1) : ∃ V : Set E, IsOpen V ∧ s ∈ V ∧ OscLE f V (4 * α) := by
  obtain ⟨v, hv, hvu, hvs⟩ := exists_unit_orth_two u s hu
  obtain ⟨V₁, hV₁, hvV₁, hosc₁⟩ := osc_polar_circle hf hu hU huU hα hv hvu
  obtain ⟨V, hV, hsV, hosc⟩ := osc_polar_circle hf hv hV₁ hvV₁ hosc₁ hs
    (by rw [real_inner_comm]; exact hvs)
  exact ⟨V, hV, hsV, hosc.of_le (by linarith)⟩

/-! ### Gleason's Theorem 2.8, first half: non-negative frame functions are continuous -/

section Continuity

variable {f : E → ℝ} {W : ℝ}

/-- The polar rotation by `π/2` about the unit vector `p`: `x ↦ ⟪x, p⟫ p + p × x`. -/
noncomputable def polarRot (p x : E) : E := ⟪x, p⟫ • p + cross p x

theorem inner_polarRot {p : E} (hp : ‖p‖ = 1) (x y : E) :
    ⟪polarRot p x, polarRot p y⟫ = ⟪x, y⟫ := by
  have h1 : ⟪cross p x, p⟫ = 0 := by rw [real_inner_comm]; exact inner_cross_left p x
  have h2 : ⟪p, cross p y⟫ = 0 := inner_cross_left p y
  simp only [polarRot, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_self_of_unit hp, h1, h2, inner_cross_cross]
  rw [real_inner_comm y p]
  ring

theorem polarRot_neg (p x : E) : polarRot p (-x) = -polarRot p x := by
  simp only [polarRot, inner_neg_left, neg_smul, cross_neg_right, neg_add]

theorem polarRot_self {p : E} (hp : ‖p‖ = 1) : polarRot p p = p := by
  simp [polarRot, cross_self', hp]

theorem polarRot_of_orth {p q : E} (hq : ⟪q, p⟫ = 0) : polarRot p q = cross p q := by
  simp [polarRot, hq]

theorem norm_polarRot {p : E} (hp : ‖p‖ = 1) {x : E} (hx : ‖x‖ = 1) : ‖polarRot p x‖ = 1 :=
  norm_eq_one_of_sq (by rw [← real_inner_self_eq_norm_sq, inner_polarRot hp, inner_self_of_unit hx])

/-- Gleason's inequalities (1) and (2) in the proof of Theorem 2.8, for a
non-negative weak frame function `g` of weight `V` that is constant (`= c`) on
the equator of `p`: (1) `g ≤ V - c` off `±p`; (2) `g r ≤ g s + (V - 2c)` for any
`s` on the EW great circle through `r`. -/
theorem step_ineq {g : E → ℝ} {V : ℝ} (hg : IsWeakFrame g V) (hg0 : ∀ x, ‖x‖ = 1 → 0 ≤ g x)
    {p : E} (hp : ‖p‖ = 1) {c : ℝ} (hc : ∀ q, ‖q‖ = 1 → ⟪q, p⟫ = 0 → g q = c) :
    (∀ r, ‖r‖ = 1 → ⟪p, r⟫ ^ 2 < 1 → g r ≤ V - c) ∧
    (∀ r, ‖r‖ = 1 → ⟪p, r⟫ ^ 2 < 1 → ∀ s, ‖s‖ = 1 → OnEW p r s →
      g r ≤ g s + (V - 2 * c)) := by
  have h1 : ∀ r, ‖r‖ = 1 → ⟪p, r⟫ ^ 2 < 1 → g r ≤ V - c := by
    intro r hr hr1
    have e := hg.ew_pair hp hr hr1 hr (norm_ewEq hp hr hr1) (inner_ewEq_self r)
      (onEW_self r hr) (onEW_ewEq r)
    have e2 := hc _ (norm_ewEq hp hr hr1) (inner_ewEq_pole r)
    have e3 := hg0 _ (norm_unitOf (ewPole_ne_zero hp hr hr1))
    linarith
  refine ⟨h1, fun r hr hr1 s hs hrs => ?_⟩
  have ht := norm_ewPartner hp hr hr1 hs hrs
  have hts := onEW_ewPartner hp hr hr1 s
  have e := hg.ew_pair_eq_top hp hr hr1 hs ht (inner_ewPartner_self r s) hrs hts
  have e2 := hc _ (norm_ewEq hp hr hr1) (inner_ewEq_pole r)
  have e3 := h1 _ ht (inner_pole_sq_lt_of_onEW hr ht hr1 hts)
  linarith

/-- **Gleason, Theorem 2.8 (continuity), normalised form.**  A non-negative
frame function whose infimum on the sphere is `0` has arbitrarily small
oscillation near every unit vector. -/
theorem exists_osc_small_of_inf_zero (hf : IsFrameFunction f W)
    (hinf : ∀ η > 0, ∃ p : E, ‖p‖ = 1 ∧ f p ≤ η) {ε : ℝ} (hε : 0 < ε) {u : E} (hu : ‖u‖ = 1) :
    ∃ V : Set E, IsOpen V ∧ u ∈ V ∧ OscLE f V ε := by
  have hη0 : 0 < ε / 88 := by positivity
  obtain ⟨p, hp, hfp⟩ := hinf (ε / 88) hη0
  obtain ⟨g, hgdef⟩ : ∃ g : E → ℝ, g = fun x => f x + f (polarRot p x) := ⟨_, rfl⟩
  have hgx : ∀ x, g x = f x + f (polarRot p x) := fun x => by rw [hgdef]
  have hgF : IsFrameFunction g (W + W) := by
    rw [hgdef]; exact hf.add (hf.comp _ (inner_polarRot hp) (polarRot_neg p))
  -- `g` is constant on the equator of `p`
  have hgeq : ∀ q : E, ‖q‖ = 1 → ⟪q, p⟫ = 0 → g q = W - f p := by
    intro q hq hqp
    have hpq : ⟪p, q⟫ = 0 := by rw [real_inner_comm]; exact hqp
    have h := hf.sum_eq p q (cross p q) hp hq (cross_unit_of_orthonormal hp hq hpq) hpq
      (inner_cross_left p q) (inner_cross_right p q)
    rw [hgx, polarRot_of_orth hqp]; linarith
  obtain ⟨-, h2⟩ := step_ineq hgF.toIsWeakFrame hgF.nonneg hp hgeq
  -- `β = inf` of `g` over the northern hemisphere minus the pole
  set S : Set ℝ := {t | ∃ x : E, ‖x‖ = 1 ∧ 0 ≤ ⟪x, p⟫ ∧ ⟪x, p⟫ < 1 ∧ t = g x} with hS
  have hSne : S.Nonempty := by
    obtain ⟨q, -, hq, -, hpq, -, -⟩ := exists_orthonormal_triple p hp
    have hqp : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact hpq
    exact ⟨g q, q, hq, hqp.symm.le, by rw [hqp]; norm_num, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro t ⟨x, hx, -, -, rfl⟩; exact hgF.nonneg x hx⟩
  obtain ⟨t, ⟨z, hz, hz0, hz1, rfl⟩, hzlt⟩ := Real.lt_sInf_add_pos hSne hη0
  have hβle : ∀ x, ‖x‖ = 1 → 0 ≤ ⟪x, p⟫ → ⟪x, p⟫ < 1 → sInf S ≤ g x :=
    fun x hx h0 h1 => csInf_le hSbdd ⟨x, hx, h0, h1, rfl⟩
  -- Lemma 2.5: an open set on which `g` oscillates by at most `5η`
  obtain ⟨U, hUo, ⟨x₀, hx₀U, hx₀⟩, hU⟩ := ew_two_step_interior hp hz hz0 hz1
  have hoscU : OscLE g U (5 * (ε / 88)) := by
    intro x hxU hx y hyU hy
    obtain ⟨hx0, hx1, y', hy', hy'0, hy'1, hxy', hy'z⟩ := hU x hxU hx
    have e1 := h2 x hx (sq_lt_one_of_north hx0 hx1) y' hy' hxy'
    have e2 := h2 y' hy' (sq_lt_one_of_north hy'0 hy'1) z hz hy'z
    have e3 := hβle y hy (hU y hyU hy).1 (hU y hyU hy).2.1
    linarith
  -- Lemma 2.7 at `p`, transferred from `g` to `f`
  obtain ⟨V, hVo, hpV, hoscV⟩ := osc_everywhere hgF.toIsWeakFrame hUo hx₀ hx₀U hoscU hp
  have hgp : g p = 2 * f p := by rw [hgx, polarRot_self hp]; ring
  have hoscfV : OscLE f V (22 * (ε / 88)) := by
    intro x hxV hx y hyV hy
    have e1 := hoscV x hxV hx p hpV hp
    have e2 := hf.nonneg (polarRot p x) (norm_polarRot hp hx)
    have e3 := hf.nonneg y hy
    rw [hgx, hgp] at e1
    linarith
  -- Lemma 2.7 at `u`
  obtain ⟨V', hV'o, huV', hoscV'⟩ := osc_everywhere hf.toIsWeakFrame hVo hp hpV hoscfV hu
  exact ⟨V', hV'o, huV', hoscV'.of_le (by linarith)⟩

/-- **Gleason, Theorem 2.8 (continuity).**  A non-negative frame function has
arbitrarily small oscillation near every unit vector. -/
theorem IsFrameFunction.exists_osc_small (hf : IsFrameFunction f W) {ε : ℝ} (hε : 0 < ε)
    {u : E} (hu : ‖u‖ = 1) : ∃ V : Set E, IsOpen V ∧ u ∈ V ∧ OscLE f V ε := by
  set S : Set ℝ := {t | ∃ x : E, ‖x‖ = 1 ∧ t = f x} with hS
  have hSne : S.Nonempty := ⟨f u, u, hu, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro t ⟨x, hx, rfl⟩; exact hf.nonneg x hx⟩
  have hf0 : IsFrameFunction (fun x => f x - sInf S) (W - 3 * sInf S) :=
    { toIsWeakFrame := hf.toIsWeakFrame.sub_const (sInf S)
      nonneg := fun x hx => sub_nonneg.mpr (csInf_le hSbdd ⟨x, hx, rfl⟩) }
  have hinf : ∀ η > 0, ∃ p : E, ‖p‖ = 1 ∧ f p - sInf S ≤ η := by
    intro η hη
    obtain ⟨t, ⟨p, hp, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hSne hη
    exact ⟨p, hp, by linarith⟩
  obtain ⟨V, hVo, huV, hosc⟩ := exists_osc_small_of_inf_zero hf0 hinf hε hu
  refine ⟨V, hVo, huV, fun x hx hx1 y hy hy1 => ?_⟩
  have := hosc x hx hx1 y hy hy1
  simp only at this
  linarith

/-- **Gleason, Theorem 2.8 (continuity).**  Every non-negative frame function on
the unit sphere of `ℝ³` is continuous on the sphere. -/
theorem IsFrameFunction.continuousOn (hf : IsFrameFunction f W) :
    ContinuousOn f (Metric.sphere (0 : E) 1) := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  rw [mem_sphere_zero_iff_norm] at hb
  obtain ⟨V, hVo, hbV, hosc⟩ := hf.exists_osc_small (half_pos hε) hb
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo b hbV
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  rw [mem_sphere_zero_iff_norm] at ha
  have haV : a ∈ V := hball (Metric.mem_ball.mpr hab)
  rw [Real.dist_eq, abs_lt]
  have := hosc a haV ha b hbV hb
  have := hosc b hbV hb a haV ha
  constructor <;> linarith

end Continuity

/-! ### The headline theorems -/

/-- **Gleason, Theorem 2.3**: a continuous frame function is regular.  Gleason
proves this by spherical harmonics (the continuous frame functions form a closed
rotation-invariant subspace of `C(S²)`; Lemma 2.2 excludes every harmonic degree
except `0` and `2`).  Left as the remaining gap of this file. -/
theorem regular_of_continuousOn {f : E → ℝ} {W : ℝ} (hf : IsFrameFunction f W)
    (hc : ContinuousOn f (Metric.sphere (0 : E) 1)) : IsRegular f := by
  sorry

/-- **Gleason, Theorem 2.8.**  Every non-negative frame function on the unit
sphere of `ℝ³` is regular. -/
theorem frameFunction_regular {f : E → ℝ} {W : ℝ} (hf : IsFrameFunction f W) : IsRegular f :=
  regular_of_continuousOn hf hf.continuousOn

/-! ### Consequences of regularity: trace `W` and positivity of the matrix -/

section Consequences

variable {f : E → ℝ} {W : ℝ}

/-- The standard basis vectors of `E`. -/
noncomputable def stdVec (i : Fin 3) : E := PiLp.single 2 i 1

theorem norm_stdVec (i : Fin 3) : ‖stdVec i‖ = 1 := by
  rw [stdVec, PiLp.norm_single, norm_one]

theorem inner_stdVec (i j : Fin 3) : ⟪stdVec i, stdVec j⟫ = if i = j then 1 else 0 := by
  rw [inner_eq_dot, stdVec, stdVec, PiLp.ofLp_single, PiLp.ofLp_single, single_one_dotProduct,
    Pi.single_apply]

theorem inner_stdVec_toEuclideanLin (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ⟪stdVec i, Matrix.toEuclideanLin A (stdVec i)⟫ = A i i := by
  rw [inner_eq_dot, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, stdVec, PiLp.ofLp_single,
    Matrix.mulVec_single_one, single_one_dotProduct]
  rfl

theorem inner_toLp_toEuclideanLin (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    ⟪(WithLp.toLp 2 x : E), Matrix.toEuclideanLin A (WithLp.toLp 2 x)⟫ = x ⬝ᵥ A *ᵥ x := by
  rw [inner_eq_dot, Matrix.toEuclideanLin_apply]

/-- If a frame function of weight `W` is given by the matrix `A` on the sphere,
then `trace A = W`. -/
theorem trace_eq_weight_of_regular (hf : IsFrameFunction f W) {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ x : E, ‖x‖ = 1 → f x = ⟪x, Matrix.toEuclideanLin A x⟫) : A.trace = W := by
  have h := hf.sum_eq (stdVec 0) (stdVec 1) (stdVec 2) (norm_stdVec 0) (norm_stdVec 1)
    (norm_stdVec 2) (by simp [inner_stdVec]) (by simp [inner_stdVec]) (by simp [inner_stdVec])
  rw [hA _ (norm_stdVec 0), hA _ (norm_stdVec 1), hA _ (norm_stdVec 2),
    inner_stdVec_toEuclideanLin, inner_stdVec_toEuclideanLin, inner_stdVec_toEuclideanLin] at h
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  exact h

/-- If a non-negative frame function is given by the matrix `A` on the sphere,
then the quadratic form of `A` is non-negative. -/
theorem dotProduct_mulVec_nonneg_of_regular (hf : IsFrameFunction f W)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ x : E, ‖x‖ = 1 → f x = ⟪x, Matrix.toEuclideanLin A x⟫) (x : Fin 3 → ℝ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hv : (WithLp.toLp 2 x : E) ≠ 0 := by
      intro h; apply hx
      simpa using congrArg WithLp.ofLp h
    have hu := hf.nonneg (unitOf (WithLp.toLp 2 x)) (norm_unitOf hv)
    rw [hA _ (norm_unitOf hv), unitOf, real_inner_smul_left, map_smul, real_inner_smul_right,
      inner_toLp_toEuclideanLin] at hu
    have hpos : 0 < ‖(WithLp.toLp 2 x : E)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hv)
    nlinarith [mul_pos hpos hpos]

/-- If a non-negative frame function is given by the symmetric matrix `A` on the
sphere, then `A` is positive semidefinite. -/
theorem posSemidef_of_regular (hf : IsFrameFunction f W) {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hs : A.IsSymm) (hA : ∀ x : E, ‖x‖ = 1 → f x = ⟪x, Matrix.toEuclideanLin A x⟫) :
    A.PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr hs)
    (fun x => by rw [star_trivial]; exact dotProduct_mulVec_nonneg_of_regular hf hA x)

end Consequences

/-- `frameFunction_eq_quadratic`: the symmetric matrix of Theorem 2.8, with its
consequences (positive semidefinite, trace `W`).  Depends on the gap
`regular_of_continuousOn`. -/
theorem frameFunction_eq_quadratic {f : E → ℝ} {W : ℝ} (hf : IsFrameFunction f W) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.IsSymm ∧ A.PosSemidef ∧ A.trace = W ∧
      ∀ x : E, ‖x‖ = 1 → f x = ⟪x, Matrix.toEuclideanLin A x⟫ := by
  obtain ⟨A, hs, hA⟩ := frameFunction_regular hf
  exact ⟨A, hs, posSemidef_of_regular hf hs hA, trace_eq_weight_of_regular hf hA, hA⟩

/-! ### The proposed "circle lemma" is false -/

/-- The circle lemma proposed in the brief for step 3 — that a continuous
`g : ℝ → ℝ` with `g θ + g (θ + π/2)` constant and `g (θ + π) = g θ` must be of
the form `a + b cos 2θ + c sin 2θ` — is FALSE: `cos 6θ` satisfies both
hypotheses and is not of that form.  A single great circle does not determine
the sinusoid; the whole 2-sphere structure is essential (Gleason's Lemma 2.2:
`cos nθ` is a frame function on the circle iff `n = 0` or `n ≡ 2 mod 4`). -/
theorem circle_lemma_of_brief_false :
    ¬ ∀ g : ℝ → ℝ, Continuous g → (∃ c, ∀ θ, g θ + g (θ + Real.pi / 2) = c) →
      (∀ θ, g (θ + Real.pi) = g θ) →
      ∃ a b c' : ℝ, ∀ θ, g θ = a + b * Real.cos (2 * θ) + c' * Real.sin (2 * θ) := by
  intro h
  have hcos : ∀ θ : ℝ, Real.cos (6 * (θ + Real.pi / 2)) = -Real.cos (6 * θ) := by
    intro θ
    rw [show 6 * (θ + Real.pi / 2) = 6 * θ + Real.pi + 2 * Real.pi by ring, Real.cos_add_two_pi,
      Real.cos_add_pi]
  have hper : ∀ θ : ℝ, Real.cos (6 * (θ + Real.pi)) = Real.cos (6 * θ) := by
    intro θ
    rw [show 6 * (θ + Real.pi) = 6 * θ + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi]
  obtain ⟨a, b, c', hg⟩ : ∃ a b c' : ℝ, ∀ θ,
      Real.cos (6 * θ) = a + b * Real.cos (2 * θ) + c' * Real.sin (2 * θ) :=
    h (fun θ => Real.cos (6 * θ)) (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨0, fun θ => by
        show Real.cos (6 * θ) + Real.cos (6 * (θ + Real.pi / 2)) = 0
        rw [hcos]; ring⟩
      (fun θ => by
        show Real.cos (6 * (θ + Real.pi)) = Real.cos (6 * θ)
        exact hper θ)
  have e0 := hg 0
  have e1 := hg (Real.pi / 2)
  have e2 := hg (Real.pi / 4)
  have e3 := hg (Real.pi / 8)
  simp only [mul_zero, Real.cos_zero, Real.sin_zero] at e0
  rw [show (6:ℝ) * (Real.pi / 2) = Real.pi + 2 * Real.pi by ring, Real.cos_add_two_pi,
    show (2:ℝ) * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, Real.sin_pi] at e1
  rw [show (6:ℝ) * (Real.pi / 4) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
    show (2:ℝ) * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two,
    Real.sin_pi_div_two] at e2
  rw [show (6:ℝ) * (Real.pi / 8) = Real.pi / 4 + Real.pi / 2 by ring, Real.cos_add_pi_div_two,
    show (2:ℝ) * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four,
    Real.sin_pi_div_four] at e3
  have ha : a = 0 := by linarith
  have hb : b = 1 := by linarith
  have hc : c' = 0 := by linarith
  rw [ha, hb, hc] at e3
  have hs : 0 < Real.sqrt 2 := by positivity
  linarith

end PDT.Gleason

#print axioms PDT.Gleason.IsFrameFunction.continuousOn
#print axioms PDT.Gleason.IsFrameFunction.exists_osc_small
#print axioms PDT.Gleason.ew_two_step_interior
#print axioms PDT.Gleason.osc_polar_circle
#print axioms PDT.Gleason.osc_everywhere
#print axioms PDT.Gleason.IsFrameFunction.comp_isometry
#print axioms PDT.Gleason.IsFrameFunction.le_weight
#print axioms PDT.Gleason.IsWeakFrame.weight_zero
#print axioms PDT.Gleason.IsWeakFrame.circle_pair_sum
#print axioms PDT.Gleason.IsWeakFrame.ew_pair_eq_top
#print axioms PDT.Gleason.circle_lemma_of_brief_false
#print axioms PDT.Gleason.trace_eq_weight_of_regular
#print axioms PDT.Gleason.posSemidef_of_regular
#print axioms PDT.Gleason.frameFunction_regular
#print axioms PDT.Gleason.frameFunction_eq_quadratic
