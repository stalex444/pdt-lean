/-
# The Mahler degree window: minimality at degrees 2, 3, 4

For d ∈ {2, 3, 4}, the polynomial `x^d − x − 1` attains the minimal Mahler
measure among monic irreducible integer polynomials of degree d with Mahler
measure above one. The minimizers' membership in the competitor class is
part of the compared surface (irreducibility below; measure above one is
the second conjunct of each exact-value theorem), and the three minimal
values are pinned exactly: the golden ratio (M² = M + 1), the plastic
ratio (M³ = M + 1), and the root of x⁴ − x³ − 1 above one (M⁴ = M³ + 1).
By Siegel's classical theorem (Duke Math. J. 11, 1944 — cited as
background, not formalized here) the latter two are the smallest and
second-smallest Pisot numbers.

The degree-4 twist: classically, x⁴ − x − 1 is not itself a Pisot
polynomial — three of its roots lie outside the unit circle (kernel-backed
in the ambient repository by `PDT.quartic_conj_norm_gt_one`, not part of
this compared surface) — yet its Mahler measure lands back on the Pisot
list, as the Pisot root of the reciprocal transform x⁴ − x³ − 1.

The Mahler measure is Mathlib's `Polynomial.mahlerMeasure`; integer
polynomials enter via `Polynomial.map (Int.castRingHom ℂ)`.
-/
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.NumberTheory.MahlerMeasure

namespace MahlerWindow

open Polynomial

/-- Degree 2 minimality: among monic irreducible integer quadratics with
Mahler measure above one, `x² − x − 1` attains the minimum. -/
theorem quadratic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 2)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := sorry

/-- Degree 2 exact value: the measure of `x² − x − 1` satisfies `M² = M + 1`
with `M > 1` — it is the golden ratio. -/
theorem quadratic_exact :
    ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 2
        = ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  sorry

/-- The degree-2 minimizer is in the competitor class: `x² − x − 1` is
irreducible over ℤ. -/
theorem quadratic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 2 - X - 1) :=
  sorry

/-- Degree 3 minimality: among monic irreducible integer cubics with Mahler
measure above one, `x³ − x − 1` attains the minimum. -/
theorem cubic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 3)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := sorry

/-- Degree 3 exact value: the measure of `x³ − x − 1` satisfies `M³ = M + 1`
with `M > 1` — it is the plastic ratio (by Siegel's classical theorem, the
smallest Pisot number; the ordering is cited, not formalized here). -/
theorem cubic_exact :
    ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 3
        = ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  sorry

/-- The degree-3 minimizer is in the competitor class: `x³ − x − 1` is
irreducible over ℤ. -/
theorem cubic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 3 - X - 1) :=
  sorry

/-- Degree 4 minimality: among monic irreducible integer quartics with
Mahler measure above one, `x⁴ − x − 1` attains the minimum. -/
theorem quartic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 4)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure := sorry

/-- Degree 4 exact value: the measure of `x⁴ − x − 1` satisfies `M⁴ = M³ + 1`
with `M > 1` — it is the root of `x⁴ − x³ − 1` above one (by Siegel's
classical theorem, the second-smallest Pisot number; the ordering is cited,
not formalized here — see the module docstring for the non-Pisot twist). -/
theorem quartic_exact :
    ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 4
        = ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 3
            + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure :=
  sorry

/-- The degree-4 minimizer is in the competitor class: `x⁴ − x − 1` is
irreducible over ℤ. -/
theorem quartic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 4 - X - 1) :=
  sorry

end MahlerWindow
