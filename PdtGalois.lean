import Mathlib
import PdtTraceLink
import PdtTraceCompositum

/-!
# Galois groups of `x³ − x − 1` and `x⁴ − x − 1`

* `galActionHom_bijective_of_quartic` — a general criterion: an irreducible monic quartic over `ℚ`
  with exactly two non-real roots and an irreducible resolvent cubic has Galois group `S₄`
  (its action on the four complex roots is the full symmetric group).
* `gal_cubic_bijective` — `Gal(x³ − x − 1) ≅ S₃`, via Mathlib's prime-degree criterion.
* `gal_quartic_bijective` — `Gal(x⁴ − x − 1) ≅ S₄`, via the criterion above with the resolvent
  cubic `x³ + 4x − 1` (irreducible mod `7`).
-/

namespace PDT

open Polynomial Module
open scoped IntermediateField

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-! ### (A0) A subgroup of `S₄` of order divisible by `12` containing a transposition is `S₄` -/

theorem perm_four_eq_top {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 4)
    (H : Subgroup (Equiv.Perm α)) (h4 : 4 ∣ Nat.card H) (h3 : 3 ∣ Nat.card H)
    {τ : Equiv.Perm α} (hτ : τ ∈ H) (hswap : τ.IsSwap) : H = ⊤ := by
  have h12 : 12 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hcard : Nat.card (Equiv.Perm α) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hα]; rfl
  have hmul := H.index_mul_card
  rw [hcard] at hmul
  obtain ⟨k, hk⟩ := h12
  have hik : H.index * k = 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 12 by norm_num)
    rw [show 12 * (H.index * k) = H.index * (12 * k) by ring, ← hk, hmul]
  have hidx : H.index ∣ 2 := Dvd.intro k hik
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2, Equiv.Perm.mem_alternatingGroup,
      hswap.sign_eq] at hτ
    exact units_ne_neg_self (1 : ℤˣ) hτ.symm

/-! ### (A1) The degree of an irreducible polynomial divides the order of its Galois group -/

theorem natDegree_dvd_card_gal {p : ℚ[X]} (p_irr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := (degree_pos_of_irreducible p_irr).ne'
  let α : p.SplittingField := rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral ℚ α := .of_finite ℚ α
  use Module.finrank ℚ⟮α⟯ p.SplittingField
  suffices (minpoly ℚ α).natDegree = p.natDegree by
    letI _ : AddCommGroup ℚ⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly ℚ α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd ℚ α
  rw [← eval_map_algebraMap]
  exact eval_rootOfSplits (SplittingField.splits p) (by rwa [degree_map])

/-! ### (A2) The resolvent cubic -/

/-- The resolvent cubic `X³ − b X² + (ac − 4d) X − (a²d − 4bd + c²)` of a monic quartic
`X⁴ + a X³ + b X² + c X + d`. -/
noncomputable def resolventCubic (p : ℚ[X]) : ℚ[X] :=
  X ^ 3 - C (p.coeff 2) * X ^ 2 + C (p.coeff 3 * p.coeff 1 - 4 * p.coeff 0) * X
    - C (p.coeff 3 ^ 2 * p.coeff 0 - 4 * p.coeff 2 * p.coeff 0 + p.coeff 1 ^ 2)

theorem resolventCubic_monic (p : ℚ[X]) : (resolventCubic p).Monic := by
  unfold resolventCubic; monicity!

theorem resolventCubic_natDegree (p : ℚ[X]) : (resolventCubic p).natDegree = 3 := by
  unfold resolventCubic; compute_degree!

/-- The expansion of a product of four linear factors. -/
theorem prod_four_linear {E : Type*} [CommRing E] (r₁ r₂ r₃ r₄ : E) :
    (X - C r₁) * ((X - C r₂) * ((X - C r₃) * (X - C r₄)))
      = X ^ 4 - C (r₁ + r₂ + r₃ + r₄) * X ^ 3
        + C (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄) * X ^ 2
        - C (r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄) * X
        + C (r₁ * r₂ * r₃ * r₄) := by
  simp only [map_add, map_mul]; ring

/-- A monic quartic, written out in its coefficients. -/
theorem quartic_eq_sum {p : ℚ[X]} (hm : p.Monic) (hd : p.natDegree = 4) :
    p = X ^ 4 + C (p.coeff 3) * X ^ 3 + C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X
      + C (p.coeff 0) := by
  have h4 : p.coeff 4 = 1 := by rw [← hd]; exact hm.coeff_natDegree
  have h := p.as_sum_range_C_mul_X_pow' (n := 5) (by omega)
  conv_lhs => rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h4, C_1]
  ring

/-- **Vieta for the resolvent.** If a monic quartic splits in `E`, then `r₁r₂ + r₃r₄` is a root of
its resolvent cubic. -/
theorem exists_resolvent_root_of_splits {E : Type*} [Field E] [Algebra ℚ E] {p : ℚ[X]}
    (hm : p.Monic) (hd : p.natDegree = 4) (hs : (p.map (algebraMap ℚ E)).Splits) :
    ∃ θ : E, aeval θ (resolventCubic p) = 0 := by
  have hm' : (p.map (algebraMap ℚ E)).Monic := hm.map _
  have hcard : Multiset.card (p.map (algebraMap ℚ E)).roots = 4 := by
    rw [← hs.natDegree_eq_card_roots, natDegree_map, hd]
  obtain ⟨r₁, r₂, r₃, r₄, hr⟩ := Multiset.card_eq_four.mp hcard
  have hprod := hs.eq_prod_roots_of_monic hm'
  rw [hr] at hprod
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hprod
  rw [prod_four_linear] at hprod
  have hmap : p.map (algebraMap ℚ E)
      = X ^ 4 + C (algebraMap ℚ E (p.coeff 3)) * X ^ 3 + C (algebraMap ℚ E (p.coeff 2)) * X ^ 2
        + C (algebraMap ℚ E (p.coeff 1)) * X + C (algebraMap ℚ E (p.coeff 0)) := by
    conv_lhs => rw [quartic_eq_sum hm hd]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
  rw [hmap] at hprod
  have h3 := Polynomial.ext_iff.mp hprod 3
  have h2 := Polynomial.ext_iff.mp hprod 2
  have h1 := Polynomial.ext_iff.mp hprod 1
  have h0 := Polynomial.ext_iff.mp hprod 0
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h3 h2 h1 h0
  norm_num at h3 h2 h1 h0
  have e3 : ((p.coeff 3 : ℚ) : E) = -(r₁ + r₂ + r₃ + r₄) := by linear_combination h3
  have e2 : ((p.coeff 2 : ℚ) : E)
      = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄ := by linear_combination h2
  have e1 : ((p.coeff 1 : ℚ) : E)
      = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₃ * r₄ + r₂ * r₃ * r₄) := by linear_combination h1
  have e0 : ((p.coeff 0 : ℚ) : E) = r₁ * r₂ * r₃ * r₄ := by linear_combination h0
  refine ⟨r₁ * r₂ + r₃ * r₄, ?_⟩
  simp only [resolventCubic, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_ofNat,
    eq_ratCast]
  rw [e3, e2, e1, e0]
  ring

/-- If the resolvent cubic is irreducible, `3` divides the order of the Galois group. -/
theorem three_dvd_card_gal {p : ℚ[X]} (p_irr : Irreducible p) (hm : p.Monic)
    (hd : p.natDegree = 4) (h_res : Irreducible (resolventCubic p)) : 3 ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  obtain ⟨θ, hθ⟩ := exists_resolvent_root_of_splits hm hd (SplittingField.splits p)
  have hθi : IsIntegral ℚ θ := .of_finite ℚ θ
  have hmin : resolventCubic p = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic h_res hθ (resolventCubic_monic p)
  use Module.finrank ℚ⟮θ⟯ p.SplittingField
  letI _ : AddCommGroup ℚ⟮θ⟯ := Ring.toAddCommGroup
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮θ⟯ p.SplittingField, IntermediateField.adjoin.finrank hθi,
    ← hmin, resolventCubic_natDegree]

/-! ### (A3) The criterion -/

/-- The number of complex roots of an irreducible rational polynomial is its degree. -/
theorem card_rootSet_complex {p : ℚ[X]} (p_irr : Irreducible p) :
    Fintype.card (p.rootSet ℂ) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup, ← Splits.natDegree_eq_card_roots, natDegree_map]
  · exact IsAlgClosed.splits _
  · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)

/-- **The `S₄` criterion.** An irreducible monic quartic over `ℚ` with exactly two non-real roots
whose resolvent cubic is irreducible has Galois group `S₄`: the Galois group acts on the four
complex roots as the full symmetric group. -/
theorem galActionHom_bijective_of_quartic {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree = 4) (p_monic : p.Monic)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2)
    (h_res : Irreducible (resolventCubic p)) : Function.Bijective (Gal.galActionHom p ℂ) := by
  classical
  have h1 : Fintype.card (p.rootSet ℂ) = 4 := by rw [card_rootSet_complex p_irr, p_deg]
  have hcard : Nat.card p.Gal = Nat.card (Gal.galActionHom p ℂ).range :=
    Nat.card_congr (MonoidHom.ofInjective (Gal.galActionHom_injective p ℂ)).toEquiv
  refine ⟨Gal.galActionHom_injective p ℂ, fun x =>
    (congr_arg (x ∈ ·) (show (Gal.galActionHom p ℂ).range = ⊤ from ?_)).mpr (Subgroup.mem_top x)⟩
  refine perm_four_eq_top h1 _ ?_ ?_
    (τ := Gal.galActionHom p ℂ (Gal.restrict p ℂ (Complex.conjAe.restrictScalars ℚ))) ⟨_, rfl⟩ ?_
  · rw [← hcard, ← p_deg]; exact natDegree_dvd_card_gal p_irr
  · rw [← hcard]; exact three_dvd_card_gal p_irr p_monic p_deg h_res
  · rw [← Equiv.Perm.card_support_eq_two]
    apply Nat.add_left_cancel
    rw [← p_roots, ← Set.toFinset_card (rootSet p ℝ), ← Set.toFinset_card (rootSet p ℂ)]
    exact (Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv p).symm

/-! ### (B1) The cubic `x³ − x − 1`: Galois group `S₃` -/

/-- Every real root of `x³ = x + 1` exceeds `1`. -/
theorem cubic_real_root_gt_one {x : ℝ} (hx : x ^ 3 = x + 1) : 1 < x := by
  by_contra hle
  push_neg at hle
  rcases le_or_gt x (-1) with h | h
  · nlinarith [hx, mul_nonneg (mul_nonneg
      (by linarith : (0:ℝ) ≤ -x) (by linarith : (0:ℝ) ≤ 1 - x))
      (by linarith : (0:ℝ) ≤ -1 - x)]
  · rcases le_or_gt x 0 with h0 | h0
    · nlinarith [hx, (by linarith : (0:ℝ) < x + 1),
        mul_nonneg (neg_nonneg.2 h0) (mul_self_nonneg x)]
    · nlinarith [hx, mul_nonneg h0.le (by nlinarith : (0:ℝ) ≤ 1 - x ^ 2)]

/-- `x³ = x + 1` has at most one real root above `1`. -/
theorem cubic_real_root_unique {x y : ℝ} (hx : x ^ 3 = x + 1) (h1x : 1 < x)
    (hy : y ^ 3 = y + 1) (h1y : 1 < y) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < y ^ 2 + y * x + x ^ 2 - 1)]
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < x ^ 2 + x * y + y ^ 2 - 1)]

/-- `x³ − x − 1` has exactly one real root. -/
theorem cubic_rootSet_real_card : Fintype.card ((X ^ 3 - X - 1 : ℚ[X]).rootSet ℝ) = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hivt := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2)
    (f := fun x : ℝ => x ^ 3 - x - 1) (by fun_prop)
  obtain ⟨ρ, -, hρ⟩ := hivt (show (0:ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1)
    ((fun x : ℝ => x ^ 3 - x - 1) 2) by norm_num)
  have hρ' : ρ ^ 3 - ρ - 1 = 0 := hρ
  have hne : (X ^ 3 - X - 1 : ℚ[X]) ≠ 0 := cubicQ_irreducible.ne_zero
  refine ⟨⟨ρ, ?_⟩, ?_⟩
  · rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    simp only [map_sub, map_pow, map_one, aeval_X]
    exact hρ'
  · rintro ⟨y, hy⟩
    rw [mem_rootSet] at hy
    have hy' : y ^ 3 - y - 1 = 0 := by simpa only [map_sub, map_pow, map_one, aeval_X] using hy.2
    exact Subtype.ext (cubic_real_root_unique (by linarith) (cubic_real_root_gt_one (by linarith))
      (by linarith) (cubic_real_root_gt_one (by linarith)))

theorem cubic_rootSet_complex_card : Fintype.card ((X ^ 3 - X - 1 : ℚ[X]).rootSet ℂ) = 3 := by
  rw [card_rootSet_complex cubicQ_irreducible]; compute_degree!

/-- **`Gal(x³ − x − 1) ≅ S₃`**: the Galois group acts on the three complex roots as the full
symmetric group. -/
theorem gal_cubic_bijective : Function.Bijective (Gal.galActionHom (X ^ 3 - X - 1 : ℚ[X]) ℂ) := by
  apply Gal.galActionHom_bijective_of_prime_degree cubicQ_irreducible
  · rw [show (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 by compute_degree!]; exact Nat.prime_three
  · rw [cubic_rootSet_complex_card, cubic_rootSet_real_card]

theorem gal_cubic_equiv_perm : Nonempty ((X ^ 3 - X - 1 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 3)) :=
  ⟨(MulEquiv.ofBijective _ gal_cubic_bijective).trans
    (Fintype.equivFinOfCardEq cubic_rootSet_complex_card).permCongrHom⟩

/-! ### (B2) The quartic `x⁴ − x − 1`: Galois group `S₄` -/

/-- The resolvent cubic of `X⁴ − X − 1` is `X³ + 4X − 1`. -/
theorem resolventCubic_quartic :
    resolventCubic (X ^ 4 - X - 1 : ℚ[X]) = X ^ 3 + 4 * X - 1 := by
  have c3 : (X ^ 4 - X - 1 : ℚ[X]).coeff 3 = 0 := by
    simp [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c2 : (X ^ 4 - X - 1 : ℚ[X]).coeff 2 = 0 := by
    simp [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c1 : (X ^ 4 - X - 1 : ℚ[X]).coeff 1 = -1 := by
    simp [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c0 : (X ^ 4 - X - 1 : ℚ[X]).coeff 0 = -1 := by
    simp [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  rw [resolventCubic, c3, c2, c1, c0]
  norm_num [C_ofNat]

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `X³ + 4X − 1` over `ℤ`. -/
noncomputable def resZ : ℤ[X] := X ^ 3 + 4 * X - 1

theorem resZ_monic : resZ.Monic := by
  unfold resZ; monicity!

theorem resZ_map7 : resZ.map (Int.castRingHom (ZMod 7)) = X ^ 3 + 4 * X - 1 := by
  unfold resZ
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]

/-- `X³ + 4X − 1` has no root mod `7`, hence is irreducible over `𝔽₇`. -/
theorem res_irred_zmod7 : Irreducible (X ^ 3 + 4 * X - 1 : (ZMod 7)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X ^ 3 + 4 * X - 1 : (ZMod 7)[X]).natDegree = 3 := by compute_degree!
    rw [Finset.mem_Icc, hd]; omega
  · intro x
    rw [IsRoot.def]
    simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_one, eval_ofNat]
    fin_cases x <;> decide

theorem resZ_irred : Irreducible resZ := by
  apply resZ_monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 7))
  rw [resZ_map7]; exact res_irred_zmod7

/-- `X³ + 4X − 1` is irreducible over `ℚ`. -/
theorem resQ_irreducible : Irreducible (X ^ 3 + 4 * X - 1 : ℚ[X]) := by
  have h := (resZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp resZ_irred
  have hmap : resZ.map (algebraMap ℤ ℚ) = (X ^ 3 + 4 * X - 1 : ℚ[X]) := by
    unfold resZ
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  rwa [hmap] at h

theorem quarticR_ne_zero : (X ^ 4 - X - 1 : ℝ[X]) ≠ 0 := by
  have h : (X ^ 4 - X - 1 : ℝ[X]).Monic := by monicity!
  exact h.ne_zero

/-- The derivative `4x³ − 1` has at most one real root. -/
theorem quarticR_derivative_roots_card :
    (derivative (X ^ 4 - X - 1 : ℝ[X])).roots.toFinset.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Multiset.mem_toFinset, mem_roots'] at ha hb
  have ha' := ha.2
  have hb' := hb.2
  simp at ha' hb'
  have h3 : a ^ 3 = b ^ 3 := by linarith
  exact (Odd.strictMono_pow (⟨1, by norm_num⟩ : Odd 3)).injective h3

theorem quarticR_roots_card_le : (X ^ 4 - X - 1 : ℝ[X]).roots.toFinset.card ≤ 2 := by
  have h := card_roots_toFinset_le_derivative (X ^ 4 - X - 1 : ℝ[X])
  have h' := quarticR_derivative_roots_card
  omega

/-- `x⁴ − x − 1` has a root in `[−1, 0]` and a root in `[1, 2]`. -/
theorem quarticR_roots_card_ge : 2 ≤ (X ^ 4 - X - 1 : ℝ[X]).roots.toFinset.card := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 4 - x - 1) (Set.Icc (-1) 0) := by fun_prop
  have hg : ContinuousOn (fun x : ℝ => x ^ 4 - x - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨r₁, ⟨-, h1b⟩, hr₁⟩ := intermediate_value_Icc' (by norm_num : (-1:ℝ) ≤ 0) hf
    (show (0:ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 - x - 1) 0) ((fun x : ℝ => x ^ 4 - x - 1) (-1))
      by norm_num)
  obtain ⟨r₂, ⟨h2a, -⟩, hr₂⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hg
    (show (0:ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 - x - 1) 1) ((fun x : ℝ => x ^ 4 - x - 1) 2)
      by norm_num)
  have hr₁' : r₁ ^ 4 - r₁ - 1 = 0 := hr₁
  have hr₂' : r₂ ^ 4 - r₂ - 1 = 0 := hr₂
  show 1 < _
  apply Finset.one_lt_card.mpr
  refine ⟨r₁, ?_, r₂, ?_, ne_of_lt (by linarith)⟩
  · rw [Multiset.mem_toFinset, mem_roots quarticR_ne_zero, IsRoot.def]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    exact hr₁'
  · rw [Multiset.mem_toFinset, mem_roots quarticR_ne_zero, IsRoot.def]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    exact hr₂'

theorem quartic_map_real : (X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℝ) = X ^ 4 - X - 1 := by
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]

/-- `x⁴ − x − 1` has exactly two real roots. -/
theorem quartic_rootSet_real_card : Fintype.card ((X ^ 4 - X - 1 : ℚ[X]).rootSet ℝ) = 2 := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [aroots_def, quartic_map_real]
  exact le_antisymm quarticR_roots_card_le quarticR_roots_card_ge

theorem quartic_rootSet_complex_card : Fintype.card ((X ^ 4 - X - 1 : ℚ[X]).rootSet ℂ) = 4 := by
  rw [card_rootSet_complex quarticQ_irreducible]; compute_degree!

/-- **`Gal(x⁴ − x − 1) ≅ S₄`**: the Galois group acts on the four complex roots as the full
symmetric group. -/
theorem gal_quartic_bijective : Function.Bijective (Gal.galActionHom (X ^ 4 - X - 1 : ℚ[X]) ℂ) := by
  apply galActionHom_bijective_of_quartic quarticQ_irreducible (by compute_degree!) (by monicity!)
  · rw [quartic_rootSet_complex_card, quartic_rootSet_real_card]
  · rw [resolventCubic_quartic]; exact resQ_irreducible

theorem gal_quartic_equiv_perm : Nonempty ((X ^ 4 - X - 1 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 4)) :=
  ⟨(MulEquiv.ofBijective _ gal_quartic_bijective).trans
    (Fintype.equivFinOfCardEq quartic_rootSet_complex_card).permCongrHom⟩

/-! ### (C) Multiplicative independence of the two real roots

If `ρ > 1` and `Q > 1` are real with `ρ³ = ρ + 1` and `Q⁴ = Q + 1`, then `ρ^a Q^b = 1` with
integers `a, b` forces `a = b = 0`.  Proof: `ρ^a = Q^(−b)` lies in `ℚ(ρ) ∩ ℚ(Q) = ℚ` (coprime
degrees `3` and `4`), so `ρ^a` is rational; but `ρ` and `ρ⁻¹ = ρ² − 1` are algebraic integers, so
`ρ^a` and `ρ^(−a)` are rational algebraic integers, i.e. integers `m, k` with `m k = 1`, forcing
`ρ^a = ±1`, impossible for `a ≠ 0` since `ρ > 1`. -/

/-- A real root of `x³ = x + 1` is an algebraic integer. -/
theorem cubic_root_isIntegral {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : IsIntegral ℤ ρ :=
  ⟨X ^ 3 - X - 1, by monicity!, by
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]; linarith⟩

/-- Its inverse `ρ⁻¹ = ρ² − 1` is an algebraic integer too (ρ is a unit). -/
theorem cubic_root_inv_isIntegral {ρ : ℝ} (hρ : ρ ^ 3 = ρ + 1) : IsIntegral ℤ ρ⁻¹ := by
  have h : ρ⁻¹ = ρ ^ 2 - 1 := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination hρ
  rw [h]
  exact ((cubic_root_isIntegral hρ).pow 2).sub isIntegral_one

/-- A real `x > 1` such that `x` and `x⁻¹` are both algebraic integers has no rational positive
power. -/
theorem pow_ne_ratCast {x : ℝ} (hx1 : 1 < x) (hi : IsIntegral ℤ x) (hi' : IsIntegral ℤ x⁻¹)
    {n : ℕ} (hn : n ≠ 0) (q : ℚ) : x ^ n ≠ q := by
  intro h
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, Rat.cast_zero] at h
    exact (pow_pos (by linarith : (0:ℝ) < x) n).ne' h
  have hq : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective, eq_ratCast, ← h]
    exact hi.pow n
  have hq' : IsIntegral ℤ q⁻¹ := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective, map_inv₀, eq_ratCast, ← h,
      ← inv_pow]
    exact hi'.pow n
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq'
  have hmk : m * k = 1 := by
    have h1 : algebraMap ℤ ℚ m * algebraMap ℤ ℚ k = 1 := by
      rw [hm, hk]; exact mul_inv_cancel₀ hq0
    simp only [eq_intCast] at h1
    exact_mod_cast h1
  have h1 : 1 < x ^ n := one_lt_pow₀ hx1 hn
  rw [h, ← hm] at h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmk with rfl | rfl
  · norm_num at h1
  · norm_num at h1

/-- The subfields `ℚ(ρ)` and `ℚ(Q)` of `ℝ` have coprime degrees `3` and `4`, hence meet in `ℚ`. -/
theorem adjoin_inf_eq_bot {ρ Q : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hQ : Q ^ 4 = Q + 1) :
    ℚ⟮ρ⟯ ⊓ ℚ⟮Q⟯ = ⊥ := by
  have hρ0 : aeval ρ (X ^ 3 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, map_one, aeval_X]; linarith
  have hQ0 : aeval Q (X ^ 4 - X - 1 : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, map_one, aeval_X]; linarith
  have hρi : IsIntegral ℚ ρ := ⟨X ^ 3 - X - 1, by monicity!, by rwa [← aeval_def]⟩
  have hQi : IsIntegral ℚ Q := ⟨X ^ 4 - X - 1, by monicity!, by rwa [← aeval_def]⟩
  have h1 : minpoly ℚ ρ = X ^ 3 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic cubicQ_irreducible hρ0 (by monicity!)).symm
  have h2 : minpoly ℚ Q = X ^ 4 - X - 1 :=
    (minpoly.eq_of_irreducible_of_monic quarticQ_irreducible hQ0 (by monicity!)).symm
  apply IntermediateField.LinearDisjoint.inf_eq_bot
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [IntermediateField.adjoin.finrank hρi, IntermediateField.adjoin.finrank hQi, h1, h2,
    show (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3 by compute_degree!,
    show (X ^ 4 - X - 1 : ℚ[X]).natDegree = 4 by compute_degree!]
  decide

/-- **Multiplicative independence of the real roots.** If `ρ > 1` and `Q > 1` are real with
`ρ³ = ρ + 1` and `Q⁴ = Q + 1`, then `ρ^a · Q^b = 1` with integers `a, b` forces `a = b = 0`. -/
theorem mul_indep {ρ Q : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hρ1 : 1 < ρ) (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)
    (a b : ℤ) (h : ρ ^ a * Q ^ b = 1) : a = 0 ∧ b = 0 := by
  have hx : ρ ^ a ∈ ℚ⟮ρ⟯ ⊓ ℚ⟮Q⟯ := by
    rw [IntermediateField.mem_inf]
    constructor
    · exact zpow_mem (IntermediateField.mem_adjoin_simple_self ℚ ρ) a
    · have hρQ : ρ ^ a = Q ^ (-b) := by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h
      rw [hρQ]
      exact zpow_mem (IntermediateField.mem_adjoin_simple_self ℚ Q) (-b)
  rw [adjoin_inf_eq_bot hρ hQ, IntermediateField.mem_bot] at hx
  obtain ⟨q, hq⟩ := hx
  have ha : a = 0 := by
    by_contra ha
    have hi := cubic_root_isIntegral hρ
    have hi' := cubic_root_inv_isIntegral hρ
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    · have hn : n ≠ 0 := by omega
      apply pow_ne_ratCast hρ1 hi hi' hn q
      rw [← eq_ratCast (algebraMap ℚ ℝ) q, hq, zpow_natCast]
    · have hn : n ≠ 0 := by omega
      apply pow_ne_ratCast hρ1 hi hi' hn q⁻¹
      rw [Rat.cast_inv, ← eq_ratCast (algebraMap ℚ ℝ) q, hq, zpow_neg, zpow_natCast, inv_inv]
  subst ha
  refine ⟨rfl, ?_⟩
  rw [zpow_zero, one_mul] at h
  exact zpow_right_injective₀ (by linarith) hQ1.ne' (h.trans (zpow_zero Q).symm)

end PDT
