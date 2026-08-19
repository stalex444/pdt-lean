import PdtIrreducible
import PdtNorm
import PdtSignature
import PdtSignatureRho
import PdtSymplectic

/-!
# Solution: proved versions of the Challenge declarations

Each declaration matches its `Challenge.lean` counterpart exactly; proofs are
supplied by the project modules, whose definitions are definitionally equal to
the Challenge's (identical literals).
-/

namespace ComplexPlaceArithmetic

open Polynomial

theorem cubic_irreducible : Irreducible (X ^ 3 - X - 1 : ℚ[X]) :=
  PDT.cubicQ_irreducible

theorem quartic_irreducible : Irreducible (X ^ 4 - X - 1 : ℚ[X]) :=
  PDT.quarticQ_irreducible

noncomputable def fρ : ℚ[X] := X ^ 3 - X - 1

noncomputable def fQ : ℚ[X] := X ^ 4 - X - 1

theorem norm_cubic_root : Algebra.norm ℚ (AdjoinRoot.root fρ) = 1 := by
  have h := PDT.norm_ρ
  unfold PDT.fρ at h
  unfold fρ
  exact h

theorem norm_quartic_root : Algebra.norm ℚ (AdjoinRoot.root fQ) = -1 := by
  have h := PDT.norm_Q
  unfold PDT.fQ at h
  unfold fQ
  exact h

def M4 : Matrix (Fin 4) (Fin 4) ℚ := !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

def P4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, -3/4;
     0, 0, 1, 16/9;
     0, 1, -3/4, -4/3;
     0, 0, 0, 1]

def D4 : Matrix (Fin 4) (Fin 4) ℚ := !![4,0,0,0; 0,4,0,0; 0,0,-9/4,0; 0,0,0,283/36]

theorem quartic_congruence : P4.transpose * M4 * P4 = D4 := by
  have h := PDT.congruence
  unfold PDT.P PDT.M PDT.D at h
  unfold P4 M4 D4
  exact h

theorem quartic_gram_det : M4.det = -283 := by
  have h := PDT.det_M
  unfold PDT.M at h
  unfold M4
  exact h

theorem quartic_P_unimodular : P4.det = -1 := by
  have h := PDT.det_P
  unfold PDT.P at h
  unfold P4
  exact h

def M3 : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,2; 0,2,3; 2,3,2]

def P3 : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,-2/3; 0,1,-3/2; 0,0,1]

def D3 : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,0; 0,2,0; 0,0,-23/6]

theorem cubic_congruence : P3.transpose * M3 * P3 = D3 := by
  have h := PDT.congruenceρ
  unfold PDT.Pρ PDT.Mρ PDT.Dρ at h
  unfold P3 M3 D3
  exact h

theorem cubic_gram_det : M3.det = -23 := by
  have h := PDT.detMρ
  unfold PDT.Mρ at h
  unfold M3
  exact h

theorem cubic_P_unimodular : P3.det = 1 := by
  have h := PDT.detPρ
  unfold PDT.Pρ at h
  unfold P3
  exact h

def Gtr : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

def Gborn : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

def Jc : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

def Cnj : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

def omegaB : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]

theorem two_rulers :
    Gborn = Gtr * Cnj ∧
    Jc.transpose * Gborn * Jc = Gborn ∧
    Jc.transpose * Gtr * Jc = -Gtr ∧
    Jc.transpose * Gborn = omegaB ∧
    omegaB.transpose = -omegaB ∧
    omegaB.det = 1 ∧
    (Jc.transpose * Gtr).transpose = Jc.transpose * Gtr := by
  have h := PDT.faultA_symplectic
  unfold PDT.Gborn PDT.Gtr PDT.Cnj PDT.Jc PDT.omegaB at h
  unfold Gborn Gtr Cnj Jc omegaB
  exact h

end ComplexPlaceArithmetic
