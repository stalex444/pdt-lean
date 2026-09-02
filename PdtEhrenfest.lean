import Mathlib

/-!
# Ehrenfest's dimensionality argument (1917)

P. Ehrenfest, *In what way does it become manifest in the fundamental laws of physics that
space has three dimensions?*, KNAW Proc. 20 (1918) 200–209, §1 and Appendix I.

In `n` spatial dimensions the Newtonian (Laplace–Poisson) potential is
`V(r) = −k / ((n−2) r^(n−2))` for `n ≥ 3` and `k · log r` for `n = 2`.  A particle of mass `m`
and angular momentum `L` moves radially in the effective potential `U(r) = L²/(2 m r²) + V(r)`:
circular orbits are the critical points of `U`, stable circular orbits its local minima, and
bounded non-circular motion between two positive radii needs a local minimum of `U`.

Everything below is a statement about real functions of one real variable.  The exponent is a
real parameter `p` (`Real.rpow`); Newtonian `n` dimensions is `p = n − 2` (`pdim n`).

* `Ehrenfest.U a b p r = a r⁻² − b r⁻ᵖ`  (`a, b > 0`, `p > 0`; `a = L²/(2m)`, `b = k/(n−2)`).
* (A1) `critical_iff`: `deriv U r = 0 ↔ r^(2−p) = 2a/(bp)`  (for `p ≠ 2` the unique critical
  point is `rstar = (2a/(bp))^(1/(2−p))`: `deriv_U_rstar`, `critical_unique`).
* (A2) `deriv_deriv_U_rstar`: `U''(rstar) = 2a (2 − p) rstar⁻⁴`, the sign of `2 − p`.
* (A3) `isLocalMin_of_lt_two` (`p < 2`: stable), `isLocalMax_of_gt_two` (`p > 2`: unstable).
* (A4) `not_isLocalMin_of_gt_two`: for `p > 2` no local minimum on `(0,∞)` at all (no motion
  between two positive radii); `not_isLocalMin_two`, `not_isLocalMax_two`: for `p = 2`, `a ≠ b`,
  no local extremum (`U` is monotone).
* (A5) `stable_iff_three`: among `n ≥ 3` (with `a ≠ b`) a local minimum exists iff `n = 3`;
  `Ulog` (`n = 2`, logarithmic potential): unique critical point `rlog = √(2a/b)`, stable.
* (B) `freq_ratio_sq`: `U''(rstar) · rstar⁴ / (2a) = 2 − p` (`= 4 − n`; the square of the ratio
  of radial to angular frequency, since `2a/rstar⁴ = m ω_φ²` up to the mass); `= 1` for `n = 3`,
  `= 2` for the logarithmic `n = 2` case, and `√2` is irrational (not closed).
* (C) `radial_laplacian_zero`: `f = r^(2−n)` satisfies `f'' + (n−1)/r · f' = 0` for `r > 0`.
-/

open Filter Topology Set

noncomputable section

namespace Ehrenfest

/-! ## The effective potential with a real power exponent -/

/-- Effective radial potential `U(r) = a r⁻² − b r⁻ᵖ` (centrifugal barrier minus attraction). -/
def U (a b p : ℝ) (r : ℝ) : ℝ := a * r ^ (-2 : ℝ) - b * r ^ (-p)

/-- `U'(r) = −2a r⁻³ + b p r⁻ᵖ⁻¹`. -/
def U' (a b p : ℝ) (r : ℝ) : ℝ := -2 * a * r ^ (-3 : ℝ) + b * p * r ^ (-p - 1)

/-- `U''(r) = 6a r⁻⁴ − b p (p+1) r⁻ᵖ⁻²`. -/
def U'' (a b p : ℝ) (r : ℝ) : ℝ := 6 * a * r ^ (-4 : ℝ) - b * p * (p + 1) * r ^ (-p - 2)

theorem hasDerivAt_U (a b p : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (U a b p) (U' a b p r) r := by
  unfold U
  have h1 := Real.hasDerivAt_rpow_const (x := r) (p := (-2 : ℝ)) (Or.inl hr)
  have h2 := Real.hasDerivAt_rpow_const (x := r) (p := -p) (Or.inl hr)
  have h := (h1.const_mul a).sub (h2.const_mul b)
  refine h.congr_deriv ?_
  unfold U'
  have e : (-2 : ℝ) - 1 = -3 := by norm_num
  rw [e]
  ring

theorem hasDerivAt_U' (a b p : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (U' a b p) (U'' a b p r) r := by
  unfold U'
  have h1 := Real.hasDerivAt_rpow_const (x := r) (p := (-3 : ℝ)) (Or.inl hr)
  have h2 := Real.hasDerivAt_rpow_const (x := r) (p := -p - 1) (Or.inl hr)
  have h := (h1.const_mul (-2 * a)).add (h2.const_mul (b * p))
  refine h.congr_deriv ?_
  unfold U''
  have e1 : (-3 : ℝ) - 1 = -4 := by norm_num
  have e2 : -p - 1 - 1 = -p - 2 := by ring
  rw [e1, e2]
  ring

theorem deriv_U (a b p : ℝ) {r : ℝ} (hr : r ≠ 0) : deriv (U a b p) r = U' a b p r :=
  (hasDerivAt_U a b p hr).deriv

theorem deriv_U_eventuallyEq (a b p : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (U a b p) =ᶠ[𝓝 r] U' a b p := by
  filter_upwards [Ioi_mem_nhds hr] with x hx
  exact deriv_U a b p (Set.mem_Ioi.mp hx).ne'

theorem deriv_deriv_U (a b p : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (U a b p)) r = U'' a b p r := by
  rw [(deriv_U_eventuallyEq a b p hr).deriv_eq]
  exact (hasDerivAt_U' a b p hr.ne').deriv

/-- `U'(r) = r⁻³ (−2a + b p r^(2−p))`. -/
theorem U'_eq (a b p : ℝ) {r : ℝ} (hr : 0 < r) :
    U' a b p r = r ^ (-3 : ℝ) * (-2 * a + b * p * r ^ (2 - p)) := by
  unfold U'
  have : r ^ (-p - 1) = r ^ (-3 : ℝ) * r ^ (2 - p) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  rw [this]; ring

/-- `U''(r) = r⁻⁴ (6a − (p+1) · b p r^(2−p))`. -/
theorem U''_eq (a b p : ℝ) {r : ℝ} (hr : 0 < r) :
    U'' a b p r = r ^ (-4 : ℝ) * (6 * a - (p + 1) * (b * p * r ^ (2 - p))) := by
  unfold U''
  have : r ^ (-p - 2) = r ^ (-4 : ℝ) * r ^ (2 - p) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  rw [this]; ring

/-! ## (A1) Circular orbits: the critical points -/

/-- (A1) `U'(r) = 0 ↔ r^(2−p) = 2a/(bp)` on `(0, ∞)`. -/
theorem critical_iff {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) {r : ℝ} (hr : 0 < r) :
    deriv (U a b p) r = 0 ↔ r ^ (2 - p) = 2 * a / (b * p) := by
  rw [deriv_U a b p hr.ne', U'_eq a b p hr]
  have h3 : r ^ (-3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hb' : b ≠ 0 := hb.ne'
  have hp' : p ≠ 0 := hp.ne'
  have hbp : b * p ≠ 0 := mul_ne_zero hb' hp'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h3
    · rw [eq_div_iff hbp]; linarith
  · intro h
    rw [h]
    have : b * p * (2 * a / (b * p)) = 2 * a := by field_simp
    rw [this]; ring

/-- The circular-orbit radius `rstar = (2a/(bp))^(1/(2−p))` (for `p ≠ 2`). -/
def rstar (a b p : ℝ) : ℝ := (2 * a / (b * p)) ^ (2 - p)⁻¹

theorem rstar_pos {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) : 0 < rstar a b p :=
  Real.rpow_pos_of_pos (div_pos (by linarith) (mul_pos hb hp)) _

theorem rstar_rpow {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2) :
    rstar a b p ^ (2 - p) = 2 * a / (b * p) := by
  unfold rstar
  exact Real.rpow_inv_rpow (div_pos (by linarith) (mul_pos hb hp)).le (sub_ne_zero.mpr hp2.symm)

/-- `rstar` is a critical point of `U`. -/
theorem deriv_U_rstar {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2) :
    deriv (U a b p) (rstar a b p) = 0 :=
  (critical_iff ha hb hp (rstar_pos ha hb hp)).mpr (rstar_rpow ha hb hp hp2)

/-- (A1) For `p ≠ 2`, `rstar` is the ONLY critical point of `U` on `(0, ∞)`. -/
theorem critical_unique {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2)
    {r : ℝ} (hr : 0 < r) (h : deriv (U a b p) r = 0) : r = rstar a b p := by
  have h1 := (critical_iff ha hb hp hr).mp h
  have hne : (2 - p) ≠ 0 := sub_ne_zero.mpr hp2.symm
  calc r = (r ^ (2 - p)) ^ (2 - p)⁻¹ := (Real.rpow_rpow_inv hr.le hne).symm
    _ = (2 * a / (b * p)) ^ (2 - p)⁻¹ := by rw [h1]
    _ = rstar a b p := rfl

/-! ## (A2) The second derivative at the circular orbit -/

/-- At any critical point, `U''(r) = 2a (2 − p) r⁻⁴`. -/
theorem deriv_deriv_U_of_critical {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    {r : ℝ} (hr : 0 < r) (h : r ^ (2 - p) = 2 * a / (b * p)) :
    deriv (deriv (U a b p)) r = 2 * a * (2 - p) * r ^ (-4 : ℝ) := by
  rw [deriv_deriv_U a b p hr, U''_eq a b p hr, h]
  have hb' : b ≠ 0 := hb.ne'
  have hp' : p ≠ 0 := hp.ne'
  have : b * p * (2 * a / (b * p)) = 2 * a := by field_simp
  rw [this]; ring

/-- (A2) `U''(rstar) = 2a (2 − p) rstar⁻⁴`: its sign is the sign of `2 − p`. -/
theorem deriv_deriv_U_rstar {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2) :
    deriv (deriv (U a b p)) (rstar a b p) = 2 * a * (2 - p) * rstar a b p ^ (-4 : ℝ) :=
  deriv_deriv_U_of_critical ha hb hp (rstar_pos ha hb hp) (rstar_rpow ha hb hp hp2)

/-! ## (A3) Stability -/

/-- (A3) `p < 2`: the circular orbit is a local minimum of `U` (stable). -/
theorem isLocalMin_of_lt_two {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p < 2) :
    IsLocalMin (U a b p) (rstar a b p) := by
  apply isLocalMin_of_deriv_deriv_pos
  · rw [deriv_deriv_U_rstar ha hb hp hp2.ne]
    have h1 : 0 < rstar a b p ^ (-4 : ℝ) := Real.rpow_pos_of_pos (rstar_pos ha hb hp) _
    have h2 : 0 < 2 - p := by linarith
    exact mul_pos (mul_pos (mul_pos two_pos ha) h2) h1
  · exact deriv_U_rstar ha hb hp hp2.ne
  · exact (hasDerivAt_U a b p (rstar_pos ha hb hp).ne').continuousAt

/-- (A3) `p > 2`: the circular orbit is a local maximum of `U` (unstable). -/
theorem isLocalMax_of_gt_two {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : 2 < p) :
    IsLocalMax (U a b p) (rstar a b p) := by
  apply isLocalMax_of_deriv_deriv_neg
  · rw [deriv_deriv_U_rstar ha hb hp hp2.ne']
    have h1 : 0 < rstar a b p ^ (-4 : ℝ) := Real.rpow_pos_of_pos (rstar_pos ha hb hp) _
    have h2 : 2 - p < 0 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos two_pos ha) h2) h1
  · exact deriv_U_rstar ha hb hp hp2.ne'
  · exact (hasDerivAt_U a b p (rstar_pos ha hb hp).ne').continuousAt

/-! ## (A4) No bounded motion between two radii -/

/-- (A4) `p > 2`: `U` has NO local minimum anywhere on `(0, ∞)`. -/
theorem not_isLocalMin_of_gt_two {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hp2 : 2 < p) {r : ℝ} (hr : 0 < r) : ¬ IsLocalMin (U a b p) r := by
  intro hmin
  have hr' : r = rstar a b p := critical_unique ha hb hp hp2.ne' hr hmin.deriv_eq_zero
  rw [hr'] at hmin
  have hmax : IsLocalMax (U a b p) (rstar a b p) := isLocalMax_of_gt_two ha hb hp hp2
  have hmin' : ∀ᶠ y in 𝓝 (rstar a b p), U a b p (rstar a b p) ≤ U a b p y := hmin
  have hmax' : ∀ᶠ y in 𝓝 (rstar a b p), U a b p y ≤ U a b p (rstar a b p) := hmax
  have hconst : U a b p =ᶠ[𝓝 (rstar a b p)] fun _ => U a b p (rstar a b p) := by
    filter_upwards [hmin', hmax'] with y h1 h2
    exact le_antisymm h2 h1
  have h0 : deriv (deriv (U a b p)) (rstar a b p) = 0 := by
    rw [hconst.deriv.deriv_eq, deriv_const']
    simp
  have hneg : deriv (deriv (U a b p)) (rstar a b p) < 0 := by
    rw [deriv_deriv_U_rstar ha hb hp hp2.ne']
    have h1 : 0 < rstar a b p ^ (-4 : ℝ) := Real.rpow_pos_of_pos (rstar_pos ha hb hp) _
    have h2 : 2 - p < 0 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos two_pos ha) h2) h1
  linarith

/-- (A4) `p = 2` (`n = 4`), `a ≠ b`: `U = (a − b) r⁻²` has no critical point on `(0, ∞)`. -/
theorem deriv_U_two_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {r : ℝ}
    (hr : 0 < r) : deriv (U a b 2) r ≠ 0 := by
  intro h
  have h1 := (critical_iff ha hb two_pos hr).mp h
  rw [sub_self, Real.rpow_zero] at h1
  have hb' : b ≠ 0 := hb.ne'
  field_simp at h1
  exact hab (by linarith)

theorem not_isLocalMin_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {r : ℝ}
    (hr : 0 < r) : ¬ IsLocalMin (U a b 2) r :=
  fun h => deriv_U_two_ne_zero ha hb hab hr h.deriv_eq_zero

theorem not_isLocalMax_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {r : ℝ}
    (hr : 0 < r) : ¬ IsLocalMax (U a b 2) r :=
  fun h => deriv_U_two_ne_zero ha hb hab hr h.deriv_eq_zero

/-! ## (A5) Newtonian `n` dimensions: `p = n − 2` -/

/-- The Newtonian exponent in `n` spatial dimensions, `p = n − 2`. -/
def pdim (n : ℕ) : ℝ := (n : ℝ) - 2

/-- `n = 3`: stable circular orbit. -/
theorem stable_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsLocalMin (U a b (pdim 3)) (rstar a b (pdim 3)) :=
  isLocalMin_of_lt_two ha hb (by norm_num [pdim]) (by norm_num [pdim])

/-- `n ≥ 5`: the circular orbit is unstable. -/
theorem unstable_of_ge_five {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 5 ≤ n) :
    IsLocalMax (U a b (pdim n)) (rstar a b (pdim n)) := by
  have h5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  exact isLocalMax_of_gt_two ha hb (by unfold pdim; linarith) (by unfold pdim; linarith)

/-- `n ≥ 5`: no motion between two positive radii (no local minimum of `U`). -/
theorem no_bounded_of_ge_five {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 5 ≤ n)
    {r : ℝ} (hr : 0 < r) : ¬ IsLocalMin (U a b (pdim n)) r := by
  have h5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  exact not_isLocalMin_of_gt_two ha hb (by unfold pdim; linarith) (by unfold pdim; linarith) hr

/-- (A5) Ehrenfest's table: among `n ≥ 3` (with `a ≠ b`, excluding the degenerate `n = 4`
cancellation), `U` has a local minimum on `(0, ∞)` iff `n = 3`. -/
theorem stable_iff_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (n : ℕ)
    (hn : 3 ≤ n) : (∃ r, 0 < r ∧ IsLocalMin (U a b (pdim n)) r) ↔ n = 3 := by
  constructor
  · rintro ⟨r, hr, hmin⟩
    by_contra hne
    rcases Nat.lt_or_ge n 5 with h | h
    · have h4 : n = 4 := by omega
      subst h4
      have hp : pdim 4 = 2 := by norm_num [pdim]
      rw [hp] at hmin
      exact not_isLocalMin_two ha hb hab hr hmin
    · exact no_bounded_of_ge_five ha hb n h hr hmin
  · rintro rfl
    exact ⟨_, rstar_pos ha hb (by norm_num [pdim]), stable_three ha hb⟩

/-! ## (B) The closure corollary: radial vs angular frequency -/

/-- (B) `U''(rstar) · rstar⁴ / (2a) = 2 − p`.  Since `2a/rstar⁴ = m ω_φ²` up to the mass, this
is `(ω_r/ω_φ)²`, the square of the ratio of the radial small-oscillation frequency to the angular
frequency: the orbit closes iff it is rational. -/
theorem freq_ratio_sq {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2) :
    deriv (deriv (U a b p)) (rstar a b p) * rstar a b p ^ (4 : ℝ) / (2 * a) = 2 - p := by
  rw [deriv_deriv_U_rstar ha hb hp hp2]
  have h : rstar a b p ^ (-4 : ℝ) * rstar a b p ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (rstar_pos ha hb hp)]; norm_num
  have ha' : (2 * a) ≠ 0 := by positivity
  rw [div_eq_iff ha']
  linear_combination (2 * a * (2 - p)) * h

/-- The same with a natural-number power `rstar ^ 4`. -/
theorem freq_ratio_sq' {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hp2 : p ≠ 2) :
    deriv (deriv (U a b p)) (rstar a b p) * rstar a b p ^ 4 / (2 * a) = 2 - p := by
  have : rstar a b p ^ (4 : ℝ) = rstar a b p ^ (4 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (rstar a b p) 4
  rw [← this]; exact freq_ratio_sq ha hb hp hp2

/-- (B) In `n` dimensions (`n ≥ 3`, `n ≠ 4`) the frequency ratio squared is `4 − n`. -/
theorem freq_ratio_sq_dim {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 3 ≤ n)
    (hn4 : n ≠ 4) :
    deriv (deriv (U a b (pdim n))) (rstar a b (pdim n)) * rstar a b (pdim n) ^ (4 : ℝ) / (2 * a)
      = 4 - n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < pdim n := by unfold pdim; linarith
  have hp2 : pdim n ≠ 2 := by
    intro h
    apply hn4
    have : (n : ℝ) = 4 := by unfold pdim at h; linarith
    exact_mod_cast this
  rw [freq_ratio_sq ha hb hp hp2]; unfold pdim; ring

/-- `n = 3` (Kepler): ratio squared `= 1`, closed orbits. -/
theorem freq_ratio_sq_three {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (deriv (U a b (pdim 3))) (rstar a b (pdim 3)) * rstar a b (pdim 3) ^ (4 : ℝ) / (2 * a)
      = 1 := by
  rw [freq_ratio_sq_dim ha hb 3 (le_refl 3) (by norm_num)]; norm_num

/-! ## The logarithmic case `n = 2`: `U(r) = a r⁻² + b log r` -/

/-- Effective potential for the two-dimensional logarithmic attraction. -/
def Ulog (a b : ℝ) (r : ℝ) : ℝ := a * r ^ (-2 : ℝ) + b * Real.log r

def Ulog' (a b : ℝ) (r : ℝ) : ℝ := -2 * a * r ^ (-3 : ℝ) + b * r ^ (-1 : ℝ)

def Ulog'' (a b : ℝ) (r : ℝ) : ℝ := 6 * a * r ^ (-4 : ℝ) - b * r ^ (-2 : ℝ)

/-- The circular-orbit radius `√(2a/b)` in the logarithmic case. -/
def rlog (a b : ℝ) : ℝ := Real.sqrt (2 * a / b)

theorem hasDerivAt_Ulog (a b : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (Ulog a b) (Ulog' a b r) r := by
  unfold Ulog
  have h1 := Real.hasDerivAt_rpow_const (x := r) (p := (-2 : ℝ)) (Or.inl hr)
  have h2 := Real.hasDerivAt_log hr
  have h := (h1.const_mul a).add (h2.const_mul b)
  refine h.congr_deriv ?_
  unfold Ulog'
  have e : (-2 : ℝ) - 1 = -3 := by norm_num
  rw [e, Real.rpow_neg_one]
  ring

theorem hasDerivAt_Ulog' (a b : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (Ulog' a b) (Ulog'' a b r) r := by
  unfold Ulog'
  have h1 := Real.hasDerivAt_rpow_const (x := r) (p := (-3 : ℝ)) (Or.inl hr)
  have h2 := Real.hasDerivAt_rpow_const (x := r) (p := (-1 : ℝ)) (Or.inl hr)
  have h := (h1.const_mul (-2 * a)).add (h2.const_mul b)
  refine h.congr_deriv ?_
  unfold Ulog''
  have e1 : (-3 : ℝ) - 1 = -4 := by norm_num
  have e2 : (-1 : ℝ) - 1 = -2 := by norm_num
  rw [e1, e2]
  ring

theorem deriv_Ulog (a b : ℝ) {r : ℝ} (hr : r ≠ 0) : deriv (Ulog a b) r = Ulog' a b r :=
  (hasDerivAt_Ulog a b hr).deriv

theorem deriv_deriv_Ulog (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (Ulog a b)) r = Ulog'' a b r := by
  have hev : deriv (Ulog a b) =ᶠ[𝓝 r] Ulog' a b := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact deriv_Ulog a b (Set.mem_Ioi.mp hx).ne'
  rw [hev.deriv_eq]
  exact (hasDerivAt_Ulog' a b hr.ne').deriv

theorem Ulog'_eq (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    Ulog' a b r = r ^ (-3 : ℝ) * (-2 * a + b * r ^ (2 : ℝ)) := by
  unfold Ulog'
  have : r ^ (-1 : ℝ) = r ^ (-3 : ℝ) * r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr]; norm_num
  rw [this]; ring

theorem Ulog''_eq (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    Ulog'' a b r = r ^ (-4 : ℝ) * (6 * a - b * r ^ (2 : ℝ)) := by
  unfold Ulog''
  have : r ^ (-2 : ℝ) = r ^ (-4 : ℝ) * r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr]; norm_num
  rw [this]; ring

/-- `n = 2`: `U'(r) = 0 ↔ r² = 2a/b`. -/
theorem critical_iff_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r : ℝ} (hr : 0 < r) :
    deriv (Ulog a b) r = 0 ↔ r ^ (2 : ℝ) = 2 * a / b := by
  rw [deriv_Ulog a b hr.ne', Ulog'_eq a b hr]
  have h3 : r ^ (-3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hb' : b ≠ 0 := hb.ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h3
    · rw [eq_div_iff hb']; linarith
  · intro h
    rw [h]
    have : b * (2 * a / b) = 2 * a := by field_simp
    rw [this]; ring

theorem rlog_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < rlog a b :=
  Real.sqrt_pos.mpr (div_pos (by linarith) hb)

theorem rlog_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : rlog a b ^ (2 : ℝ) = 2 * a / b := by
  rw [Real.rpow_two]; exact Real.sq_sqrt (div_pos (by linarith) hb).le

theorem deriv_Ulog_rlog {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : deriv (Ulog a b) (rlog a b) = 0 :=
  (critical_iff_log ha hb (rlog_pos ha hb)).mpr (rlog_sq ha hb)

/-- `n = 2`: `rlog = √(2a/b)` is the unique critical point. -/
theorem critical_unique_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {r : ℝ} (hr : 0 < r)
    (h : deriv (Ulog a b) r = 0) : r = rlog a b := by
  have h1 := (critical_iff_log ha hb hr).mp h
  rw [Real.rpow_two] at h1
  unfold rlog
  rw [← h1]
  exact (Real.sqrt_sq hr.le).symm

/-- `n = 2`: `U''(rlog) = 4a rlog⁻⁴ > 0`. -/
theorem deriv_deriv_Ulog_rlog {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (deriv (Ulog a b)) (rlog a b) = 4 * a * rlog a b ^ (-4 : ℝ) := by
  rw [deriv_deriv_Ulog a b (rlog_pos ha hb), Ulog''_eq a b (rlog_pos ha hb), rlog_sq ha hb]
  have hb' : b ≠ 0 := hb.ne'
  have : b * (2 * a / b) = 2 * a := by field_simp
  rw [this]; ring

/-- (A5) `n = 2`: the circular orbit of the logarithmic potential is stable. -/
theorem isLocalMin_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IsLocalMin (Ulog a b) (rlog a b) := by
  apply isLocalMin_of_deriv_deriv_pos
  · rw [deriv_deriv_Ulog_rlog ha hb]
    have h1 : 0 < rlog a b ^ (-4 : ℝ) := Real.rpow_pos_of_pos (rlog_pos ha hb) _
    exact mul_pos (mul_pos (by norm_num) ha) h1
  · exact deriv_Ulog_rlog ha hb
  · exact (hasDerivAt_Ulog a b (rlog_pos ha hb).ne').continuousAt

/-- (B) `n = 2`: the frequency ratio squared is `2`. -/
theorem freq_ratio_sq_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (deriv (Ulog a b)) (rlog a b) * rlog a b ^ (4 : ℝ) / (2 * a) = 2 := by
  rw [deriv_deriv_Ulog_rlog ha hb]
  have h : rlog a b ^ (-4 : ℝ) * rlog a b ^ (4 : ℝ) = 1 := by
    rw [← Real.rpow_add (rlog_pos ha hb)]; norm_num
  have ha' : (2 * a) ≠ 0 := by positivity
  rw [div_eq_iff ha']
  linear_combination (4 * a) * h

/-- (B) `n = 2`: the frequency ratio `√2` is irrational — the orbits do not close. -/
theorem freq_ratio_log_irrational {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Irrational (Real.sqrt (deriv (deriv (Ulog a b)) (rlog a b) * rlog a b ^ (4 : ℝ) / (2 * a))) := by
  rw [freq_ratio_sq_log ha hb]; exact irrational_sqrt_two

/-! ## (C) The radial Laplace equation -/

/-- The radial profile `r ↦ r^(2−n)` of the `n`-dimensional Newtonian potential. -/
def radial (n : ℝ) (r : ℝ) : ℝ := r ^ (2 - n)

theorem hasDerivAt_radial (n : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radial n) ((2 - n) * r ^ (1 - n)) r := by
  unfold radial
  have h := Real.hasDerivAt_rpow_const (x := r) (p := 2 - n) (Or.inl hr)
  refine h.congr_deriv ?_
  have e : 2 - n - 1 = 1 - n := by ring
  rw [e]

theorem deriv_radial (n : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (radial n) r = (2 - n) * r ^ (1 - n) :=
  (hasDerivAt_radial n hr).deriv

theorem deriv_deriv_radial (n : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radial n)) r = (2 - n) * (1 - n) * r ^ (-n) := by
  have hev : deriv (radial n) =ᶠ[𝓝 r] fun x => (2 - n) * x ^ (1 - n) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact deriv_radial n (Set.mem_Ioi.mp hx).ne'
  rw [hev.deriv_eq]
  have h := (Real.hasDerivAt_rpow_const (x := r) (p := 1 - n) (Or.inl hr.ne')).const_mul (2 - n)
  rw [h.deriv]
  have e : 1 - n - 1 = -n := by ring
  rw [e]
  try ring1

/-- (C, radial form) `f(r) = r^(2−n)` satisfies `f'' + (n−1)/r · f' = 0` on `(0, ∞)`: the
radial Laplace equation in `n` dimensions, for every real `n`. -/
theorem radial_laplacian_zero (n : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radial n)) r + (n - 1) / r * deriv (radial n) r = 0 := by
  rw [deriv_deriv_radial n hr, deriv_radial n hr.ne']
  have h : r ^ (1 - n) = r ^ (1 : ℝ) * r ^ (-n) := by
    rw [← Real.rpow_add hr]; congr 1
    try ring1
  rw [h, Real.rpow_one, div_eq_mul_inv]
  have hr1 : r⁻¹ * r = 1 := inv_mul_cancel₀ hr.ne'
  linear_combination ((n - 1) * (2 - n) * r ^ (-n)) * hr1

/-! ## (C) The potential is harmonic: `Δ ‖x‖^(2−n) = 0` off the origin (Laplace–Poisson)

For a real inner product space `E` of finite dimension `n`, `Δ (g(‖y‖²)) = 2n g' + 4‖x‖² g''`
(computed over an orthonormal basis); hence `Δ ‖x‖^s = s (n + s − 2) ‖x‖^(s−2)`, which vanishes
exactly for `s = 2 − n`, and `Δ log ‖x‖ = (n − 2) ‖x‖⁻²`, which vanishes exactly for `n = 2`. -/

section Harmonic

open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The real inner product as an `ℝ`-bilinear continuous map `E →L[ℝ] E →L[ℝ] ℝ`. -/
def innerB (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : E →L[ℝ] E →L[ℝ] ℝ :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
theorem innerB_apply (x y : E) : innerB E x y = ⟪x, y⟫ := rfl

omit [FiniteDimensional ℝ E] in
/-- `fderiv` of `y ↦ g(‖y‖²)` at `x` is `2 g'(‖x‖²) ⟪x, ·⟫`. -/
theorem hasFDerivAt_comp_normSq {g g' : ℝ → ℝ} {x : E}
    (hg : HasDerivAt g (g' (‖x‖ ^ 2)) (‖x‖ ^ 2)) :
    HasFDerivAt (fun y : E => g (‖y‖ ^ 2)) ((2 * g' (‖x‖ ^ 2)) • innerB E x) x := by
  have hN : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := hg.comp_hasFDerivAt x hN
  refine h.congr_fderiv ?_
  ext v
  simp [two_smul, innerB_apply, innerSL_apply_apply]
  ring1

omit [FiniteDimensional ℝ E] in
/-- `fderiv` of `y ↦ 2 g'(‖y‖²) ⟪y, ·⟫`. -/
theorem hasFDerivAt_fderiv_comp_normSq {g' g'' : ℝ → ℝ} {x : E}
    (hg' : HasDerivAt g' (g'' (‖x‖ ^ 2)) (‖x‖ ^ 2)) :
    HasFDerivAt (fun y : E => (2 * g' (‖y‖ ^ 2)) • innerB E y)
      ((2 * g' (‖x‖ ^ 2)) • innerB E
        + ((2 * (2 * g'' (‖x‖ ^ 2))) • innerB E x).smulRight (innerB E x)) x := by
  have hφ : HasFDerivAt (fun y : E => 2 * g' (‖y‖ ^ 2))
      ((2 * (2 * g'' (‖x‖ ^ 2))) • innerB E x) x := by
    have h := (hasFDerivAt_comp_normSq (g := g') (g' := g'') hg').const_mul (2 : ℝ)
    refine h.congr_fderiv ?_
    rw [smul_smul]
  have hB : HasFDerivAt (fun y : E => innerB E y) (innerB E) x := (innerB E).hasFDerivAt
  exact hφ.smul hB

/-- The Laplacian of a radial function `g(‖y‖²)` over an orthonormal basis of cardinality `n`:
`Δ = 2n g'(‖x‖²) + 4‖x‖² g''(‖x‖²)`. -/
theorem laplacian_comp_normSq_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g g' g'' : ℝ → ℝ} (hg : ∀ t : ℝ, 0 < t → HasDerivAt g (g' t) t)
    (hg' : ∀ t : ℝ, 0 < t → HasDerivAt g' (g'' t) t) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E => g (‖y‖ ^ 2)) x
      = 2 * (Fintype.card ι : ℝ) * g' (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) := by
  have hev : fderiv ℝ (fun y : E => g (‖y‖ ^ 2)) =ᶠ[𝓝 x]
      fun y : E => (2 * g' (‖y‖ ^ 2)) • innerB E y := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasFDerivAt_comp_normSq (hg _ (pow_pos (norm_pos_iff.mpr hy) 2))).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (fun y : E => g (‖y‖ ^ 2))) x
      = (2 * g' (‖x‖ ^ 2)) • innerB E
        + ((2 * (2 * g'' (‖x‖ ^ 2))) • innerB E x).smulRight (innerB E x) := by
    rw [hev.fderiv_eq]
    exact (hasFDerivAt_fderiv_comp_normSq (hg' _ (pow_pos (norm_pos_iff.mpr hx) 2))).fderiv
  have hterm : ∀ i, fderiv ℝ (fderiv ℝ (fun y : E => g (‖y‖ ^ 2))) x (b i) (b i)
      = 2 * g' (‖x‖ ^ 2) + (2 * (2 * g'' (‖x‖ ^ 2))) * (⟪x, b i⟫ * ⟪x, b i⟫) := by
    intro i
    rw [h2]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, innerB_apply, b.inner_eq_one]
    ring
  have hsum : ∑ i, ⟪x, b i⟫ * ⟪x, b i⟫ = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq x, ← b.sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f := fun y : E => g (‖y‖ ^ 2)) b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hsum]
  ring

/-- `Δ (g(‖y‖²)) = 2n g'(‖x‖²) + 4‖x‖² g''(‖x‖²)`, `n = finrank ℝ E`. -/
theorem laplacian_comp_normSq {g g' g'' : ℝ → ℝ} (hg : ∀ t : ℝ, 0 < t → HasDerivAt g (g' t) t)
    (hg' : ∀ t : ℝ, 0 < t → HasDerivAt g' (g'' t) t) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E => g (‖y‖ ^ 2)) x
      = 2 * (Module.finrank ℝ E : ℝ) * g' (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) := by
  rw [laplacian_comp_normSq_basis (stdOrthonormalBasis ℝ E) hg hg' hx, Fintype.card_fin]

/-- (C) `Δ ‖x‖^s = s (n + s − 2) ‖x‖^(s−2)` for `x ≠ 0`, `n = finrank ℝ E`. -/
theorem laplacian_normPow (s : ℝ) {x : E} (hx : x ≠ 0) :
    Δ (fun y : E => ‖y‖ ^ s) x = s * ((Module.finrank ℝ E : ℝ) + s - 2) * ‖x‖ ^ (s - 2) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hfun : (fun y : E => ‖y‖ ^ s) = fun y : E => (‖y‖ ^ 2) ^ (s / 2) := by
    funext y
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
    congr 1; push_cast; ring
  have hg : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => t ^ (s / 2)) (s / 2 * t ^ (s / 2 - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hg' : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => s / 2 * t ^ (s / 2 - 1))
      (s / 2 * ((s / 2 - 1) * t ^ (s / 2 - 1 - 1))) t :=
    fun t ht => (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul (s / 2)
  rw [hfun, laplacian_comp_normSq (g := fun t : ℝ => t ^ (s / 2))
    (g' := fun t : ℝ => s / 2 * t ^ (s / 2 - 1))
    (g'' := fun t : ℝ => s / 2 * ((s / 2 - 1) * t ^ (s / 2 - 1 - 1))) hg hg' hx]
  have e1 : (‖x‖ ^ 2) ^ (s / 2 - 1) = ‖x‖ ^ (s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have e2 : (‖x‖ ^ 2) ^ (s / 2 - 1 - 1) = ‖x‖ ^ (s - 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have e3 : ‖x‖ ^ 2 * ‖x‖ ^ (s - 4) = ‖x‖ ^ (s - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast; ring
  rw [e1, e2]
  linear_combination (s * (s - 2)) * e3

/-- (C) `Δ log ‖x‖ = (n − 2) ‖x‖⁻²` for `x ≠ 0`, `n = finrank ℝ E`. -/
theorem laplacian_log_norm {x : E} (hx : x ≠ 0) :
    Δ (fun y : E => Real.log ‖y‖) x = ((Module.finrank ℝ E : ℝ) - 2) * (‖x‖ ^ 2)⁻¹ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hfun : (fun y : E => Real.log ‖y‖) = fun y : E => (1 / 2 : ℝ) * Real.log (‖y‖ ^ 2) := by
    funext y; rw [Real.log_pow]; push_cast; ring
  have hg : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log t) ((1 / 2 : ℝ) * t⁻¹) t :=
    fun t ht => (Real.hasDerivAt_log ht.ne').const_mul (1 / 2)
  have hg' : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t⁻¹) ((1 / 2 : ℝ) * (-(t ^ 2)⁻¹)) t :=
    fun t ht => (hasDerivAt_inv ht.ne').const_mul (1 / 2)
  rw [hfun, laplacian_comp_normSq (g := fun t : ℝ => (1 / 2 : ℝ) * Real.log t)
    (g' := fun t : ℝ => (1 / 2 : ℝ) * t⁻¹)
    (g'' := fun t : ℝ => (1 / 2 : ℝ) * (-(t ^ 2)⁻¹)) hg hg' hx]
  have hN : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hx0.ne'
  have hc : ‖x‖ ^ 2 * (‖x‖ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hN
  rw [sq (‖x‖ ^ 2), mul_inv]
  linear_combination (-2 * (‖x‖ ^ 2)⁻¹) * hc

/-- (C) `‖x‖^(2−n)` is harmonic on `E \ {0}` for every real inner product space `E` of finite
dimension `n` — the Newtonian potential solves Laplace's equation away from the source. -/
theorem harmonicOnNhd_normPow :
    HarmonicOnNhd (fun y : E => ‖y‖ ^ (2 - (Module.finrank ℝ E : ℝ))) {x : E | x ≠ 0} := by
  intro x hx
  have hx : x ≠ 0 := hx
  refine ⟨(contDiffAt_norm (𝕜 := ℝ) (n := 2) hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [Pi.zero_apply, laplacian_normPow _ hy]
  ring

/-- (C) `log ‖x‖` is harmonic on `E \ {0}` when `finrank ℝ E = 2`. -/
theorem harmonicOnNhd_log_norm (h2 : Module.finrank ℝ E = 2) :
    HarmonicOnNhd (fun y : E => Real.log ‖y‖) {x : E | x ≠ 0} := by
  intro x hx
  have hx : x ≠ 0 := hx
  refine ⟨(contDiffAt_norm (𝕜 := ℝ) (n := 2) hx).log (norm_ne_zero_iff.mpr hx), ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [Pi.zero_apply, laplacian_log_norm hy, h2]
  norm_num

/-- (C) Ehrenfest's `n`-dimensional Newtonian potential `‖x‖^(2−n)` on `ℝⁿ` is harmonic off
the origin. -/
theorem harmonicOnNhd_euclidean (n : ℕ) :
    HarmonicOnNhd (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ (2 - n : ℝ)) {x | x ≠ 0} := by
  have h := harmonicOnNhd_normPow (E := EuclideanSpace ℝ (Fin n))
  rwa [finrank_euclideanSpace_fin] at h

/-- (C) The two-dimensional logarithmic potential `log ‖x‖` on `ℝ²` is harmonic off the origin. -/
theorem harmonicOnNhd_euclidean_two :
    HarmonicOnNhd (fun x : EuclideanSpace ℝ (Fin 2) => Real.log ‖x‖) {x | x ≠ 0} :=
  harmonicOnNhd_log_norm finrank_euclideanSpace_fin

end Harmonic

end Ehrenfest

end

#print axioms Ehrenfest.hasDerivAt_U
#print axioms Ehrenfest.hasDerivAt_U'
#print axioms Ehrenfest.deriv_U
#print axioms Ehrenfest.deriv_U_eventuallyEq
#print axioms Ehrenfest.deriv_deriv_U
#print axioms Ehrenfest.U'_eq
#print axioms Ehrenfest.U''_eq
#print axioms Ehrenfest.critical_iff
#print axioms Ehrenfest.rstar_pos
#print axioms Ehrenfest.rstar_rpow
#print axioms Ehrenfest.deriv_U_rstar
#print axioms Ehrenfest.critical_unique
#print axioms Ehrenfest.deriv_deriv_U_of_critical
#print axioms Ehrenfest.deriv_deriv_U_rstar
#print axioms Ehrenfest.isLocalMin_of_lt_two
#print axioms Ehrenfest.isLocalMax_of_gt_two
#print axioms Ehrenfest.not_isLocalMin_of_gt_two
#print axioms Ehrenfest.deriv_U_two_ne_zero
#print axioms Ehrenfest.not_isLocalMin_two
#print axioms Ehrenfest.not_isLocalMax_two
#print axioms Ehrenfest.stable_three
#print axioms Ehrenfest.unstable_of_ge_five
#print axioms Ehrenfest.no_bounded_of_ge_five
#print axioms Ehrenfest.stable_iff_three
#print axioms Ehrenfest.freq_ratio_sq
#print axioms Ehrenfest.freq_ratio_sq'
#print axioms Ehrenfest.freq_ratio_sq_dim
#print axioms Ehrenfest.freq_ratio_sq_three
#print axioms Ehrenfest.hasDerivAt_Ulog
#print axioms Ehrenfest.hasDerivAt_Ulog'
#print axioms Ehrenfest.deriv_Ulog
#print axioms Ehrenfest.deriv_deriv_Ulog
#print axioms Ehrenfest.Ulog'_eq
#print axioms Ehrenfest.Ulog''_eq
#print axioms Ehrenfest.critical_iff_log
#print axioms Ehrenfest.rlog_pos
#print axioms Ehrenfest.rlog_sq
#print axioms Ehrenfest.deriv_Ulog_rlog
#print axioms Ehrenfest.critical_unique_log
#print axioms Ehrenfest.deriv_deriv_Ulog_rlog
#print axioms Ehrenfest.isLocalMin_log
#print axioms Ehrenfest.freq_ratio_sq_log
#print axioms Ehrenfest.freq_ratio_log_irrational
#print axioms Ehrenfest.hasDerivAt_radial
#print axioms Ehrenfest.deriv_radial
#print axioms Ehrenfest.deriv_deriv_radial
#print axioms Ehrenfest.radial_laplacian_zero
#print axioms Ehrenfest.innerB_apply
#print axioms Ehrenfest.hasFDerivAt_comp_normSq
#print axioms Ehrenfest.hasFDerivAt_fderiv_comp_normSq
#print axioms Ehrenfest.laplacian_comp_normSq_basis
#print axioms Ehrenfest.laplacian_comp_normSq
#print axioms Ehrenfest.laplacian_normPow
#print axioms Ehrenfest.laplacian_log_norm
#print axioms Ehrenfest.harmonicOnNhd_normPow
#print axioms Ehrenfest.harmonicOnNhd_log_norm
#print axioms Ehrenfest.harmonicOnNhd_euclidean
#print axioms Ehrenfest.harmonicOnNhd_euclidean_two
