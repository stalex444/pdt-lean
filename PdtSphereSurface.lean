import Mathlib

/-!
# Total surface measure of the unit sphere in Euclidean space

For a real normed space `E` carrying an additive Haar measure `μ`, Mathlib already
provides the *polar surface measure* `MeasureTheory.Measure.toSphere μ` on the unit
sphere `sphere (0 : E) 1`.  It is the measure that appears in the generalized polar
(spherical) coordinate change: up to `homeomorphUnitSphereProd`, `μ` is the product of
`μ.toSphere` and the Lebesgue measure on `(0, ∞)` weighted by `r ^ (n-1)`
(see `MeasureTheory.integral_fun_norm_addHaar`).  Its total mass is governed by

  `MeasureTheory.Measure.toSphere_apply_univ : μ.toSphere univ = n • μ (ball 0 1)`,

i.e. the surface area of `Sⁿ⁻¹` is `n` times the volume of the unit ball `Bⁿ` — the
classical relation `surface(Sⁿ⁻¹) = n · vol(Bⁿ)`, already in Mathlib.

What is *not* in Mathlib is the closed-form evaluation of this total mass for
`EuclideanSpace ℝ ι`, parallel to `EuclideanSpace.volume_ball`.  This file supplies it:

* `EuclideanSpace.volume_toSphere_univ` :
    `(volume).toSphere univ = ENNReal.ofReal (2 * √π ^ n / Γ (n / 2))`,  `n = card ι`.

  Equivalently `2 π^{n/2} / Γ(n/2)`, the standard surface area of the `(n-1)`-sphere.

* `EuclideanSpace.volume_toSphere_univ_fin_four` : the special case `n = 4`, giving the
  surface area of `S³ ⊆ ℝ⁴` as `2π²`.  Together with `EuclideanSpace.volume_ball`
  (`vol(B⁴) = π²/2`) and `Measure.toSphere_apply_univ`, this is the classical
  `surface(S³) = 4·vol(B⁴) = 2π²`; only the surface value is stated as a theorem below.

## Note on the surface measure used

`Measure.toSphere` is the rotation-invariant surface measure normalized so that the
polar decomposition holds exactly; it is the natural "surface area" for integration in
Euclidean space.  Mathlib does not (yet) prove that it agrees with the `(n-1)`-dimensional
Hausdorff measure of the sphere, but that identification is not needed for the value of
the total mass, which is pinned down by `toSphere_apply_univ` and `EuclideanSpace.volume_ball`.
-/

open Fintype MeasureTheory MeasureTheory.Measure Real Metric Set
open scoped ENNReal

noncomputable section

namespace EuclideanSpace

variable (ι : Type*) [Nonempty ι] [Fintype ι]

/-- The total mass of the polar surface measure `Measure.toSphere` on the unit sphere of
`EuclideanSpace ℝ ι` is `2 * √π ^ card ι / Γ (card ι / 2)`, the classical surface area
`2 π^{n/2} / Γ(n/2)` of `Sⁿ⁻¹`. -/
theorem volume_toSphere_univ :
    (volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ
      = ENNReal.ofReal (2 * Real.sqrt π ^ card ι / Real.Gamma (card ι / 2)) := by
  have hcpos : 0 < (card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc2 : (card ι : ℝ) / 2 ≠ 0 := by positivity
  have hg : Real.Gamma ((card ι : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [Measure.toSphere_apply_univ, finrank_euclideanSpace, EuclideanSpace.volume_ball,
    ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [Real.Gamma_add_one hc2]
  field_simp

/-- The surface area of `S³ ⊆ ℝ⁴` is `2 * π ^ 2`, the case `ι = Fin 4` of
`EuclideanSpace.volume_toSphere_univ`. -/
theorem volume_toSphere_univ_fin_four :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere Set.univ
      = ENNReal.ofReal (2 * π ^ 2) := by
  have hsq : Real.sqrt π ^ 4 = π ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [volume_toSphere_univ, Fintype.card_fin, hsq, show ((4 : ℕ) : ℝ) / 2 = 2 by norm_num,
    Real.Gamma_two, div_one]

end EuclideanSpace

end
