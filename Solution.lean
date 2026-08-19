import PdtTsirelson
import PdtTsirelsonNorm
import PdtBellClassical

/-!
# Solution: proved versions of the Challenge declarations

Each declaration matches its `Challenge.lean` counterpart exactly; proofs are
supplied by the project modules `PdtTsirelson` and `PdtBellClassical`, whose
definitions are definitionally equal to the Challenge's.
-/

namespace TsirelsonTightness

open Matrix

theorem chsh_upper
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ (2 * Real.sqrt 2) • (1 : R) :=
  PDT.chsh_le_two_sqrt_two A₀ A₁ B₀ B₁ T

noncomputable def s : ℝ := (Real.sqrt 2)⁻¹

def A₀ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

def A₁ : Matrix (Fin 4) (Fin 4) ℝ := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

def B₀i : Matrix (Fin 4) (Fin 4) ℝ := !![1,1,0,0; 1,-1,0,0; 0,0,1,1; 0,0,1,-1]

def B₁i : Matrix (Fin 4) (Fin 4) ℝ := !![-1,1,0,0; 1,1,0,0; 0,0,-1,1; 0,0,1,1]

noncomputable def B₀ : Matrix (Fin 4) (Fin 4) ℝ := s • B₀i

noncomputable def B₁ : Matrix (Fin 4) (Fin 4) ℝ := s • B₁i

theorem tuple_isCHSH : IsCHSHTuple A₀ A₁ B₀ B₁ := by
  have h := PDT.isCHSH
  unfold PDT.A₀ PDT.A₁ PDT.B₀ PDT.B₁ PDT.B₀i PDT.B₁i PDT.s at h
  unfold A₀ A₁ B₀ B₁ B₀i B₁i s
  exact h

def vsat : Fin 4 → ℝ := ![1, 0, 0, 1]

theorem vsat_ne_zero : vsat ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vsat] at h0

theorem chsh_saturates :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁).mulVec vsat
      = (2 * Real.sqrt 2) • vsat := by
  have h := PDT.chsh_saturates
  unfold PDT.A₀ PDT.A₁ PDT.B₀ PDT.B₁ PDT.B₀i PDT.B₁i PDT.s PDT.vsat at h
  unfold A₀ A₁ B₀ B₁ B₀i B₁i s vsat
  exact h

theorem classical_le_two
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  PDT.chsh_comm_le_two A₀ A₁ B₀ B₁ T

theorem bell_gap : (2 : ℝ) < 2 * Real.sqrt 2 :=
  PDT.bell_gap

section OperatorNorm

open scoped Matrix.Norms.L2Operator

theorem chsh_opNorm :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ = 2 * Real.sqrt 2 := by
  have h := PDT.Pchsh_opNorm
  unfold PDT.Pchsh PDT.A₀ PDT.A₁ PDT.B₀ PDT.B₁ PDT.B₀i PDT.B₁i PDT.s at h
  unfold A₀ A₁ B₀ B₁ B₀i B₁i s
  exact h

theorem chsh_sq_ne :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      ≠ (8 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have h := PDT.Pchsh_sq_ne
  unfold PDT.Pchsh PDT.A₀ PDT.A₁ PDT.B₀ PDT.B₁ PDT.B₀i PDT.B₁i PDT.s at h
  unfold A₀ A₁ B₀ B₁ B₀i B₁i s
  exact h

end OperatorNorm

end TsirelsonTightness

-- Axiom audit (repo idiom): the new compared theorems must depend on at most
-- {propext, Classical.choice, Quot.sound}.
#print axioms TsirelsonTightness.chsh_opNorm
#print axioms TsirelsonTightness.chsh_sq_ne
