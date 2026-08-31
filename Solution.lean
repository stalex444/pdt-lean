/-
Solution module: proofs of the nine Challenge statements, backed by the
PdtMahler development (Graeffe-certificate architecture: coefficient-bound
box + per-element integer certificates, all kernel-decided without
native_decide).
-/
import PdtMahlerWindow

namespace MahlerWindow

open Polynomial PDT.Mahler

theorem quadratic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 2)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
  quadratic_mahler_min' p hm hd hi h1

theorem quadratic_exact :
    ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 2
        = ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 2 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq2_fam]
  exact mahler_quadratic_phi

theorem quadratic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 2 - X - 1) :=
  fam2_irreducible

theorem cubic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 3)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
  cubic_mahler_min' p hm hd hi h1

theorem cubic_exact :
    ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 3
        = ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 3 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq3_fam]
  exact mahler_cubic_rho

theorem cubic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 3 - X - 1) :=
  fam3_irreducible

theorem quartic_min (p : ℤ[X]) (hm : p.Monic) (hd : p.natDegree = 4)
    (hi : Irreducible p)
    (h1 : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure) :
    ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure
      ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
  quartic_mahler_min' p hm hd hi h1

theorem quartic_exact :
    ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 4
        = ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure ^ 3
            + 1
      ∧ 1 < ((((X : ℤ[X]) ^ 4 - X - 1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [← zq4_fam]
  exact mahler_fam_pisot

theorem quartic_min_irreducible : Irreducible ((X : ℤ[X]) ^ 4 - X - 1) :=
  fam4_irreducible

end MahlerWindow
