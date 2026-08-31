/-
Solution: proofs of the Busch-theorem challenge statements, transferred
from the PdtBusch development (PDT.Busch.busch and PDT.Busch.frame_smul).
-/
import PdtBusch

namespace BuschTheorem

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

private def toFrame {f : Matrix n n ℂ → ℝ}
    (h0 : ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef → 0 ≤ f a)
    (hadd : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
      (1 - (a + b)).PosSemidef → f (a + b) = f a + f b)
    (h1 : f 1 = 1) : PDT.Busch.IsFrameFunction f where
  nonneg a ha := h0 a ha.1 ha.2
  add := hadd
  norm_one := h1

theorem homogeneity_automatic (f : Matrix n n ℂ → ℝ)
    (h0 : ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef → 0 ≤ f a)
    (hadd : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
      (1 - (a + b)).PosSemidef → f (a + b) = f a + f b)
    (h1 : f 1 = 1)
    {a : Matrix n n ℂ} (ha : a.PosSemidef) (ha1 : (1 - a).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (t • a) = t * f a :=
  PDT.Busch.frame_smul (toFrame h0 hadd h1) ha ha1 ht0 ht1

theorem busch_representation [Nonempty n] (f : Matrix n n ℂ → ℝ)
    (h0 : ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef → 0 ≤ f a)
    (hadd : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
      (1 - (a + b)).PosSemidef → f (a + b) = f a + f b)
    (h1 : f 1 = 1) :
    ∃! ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef →
        (ρ * a).trace = (f a : ℂ) := by
  obtain ⟨ρ, ⟨hpsd, htr, hrep⟩, huniq⟩ :=
    PDT.Busch.busch f (toFrame h0 hadd h1)
  refine ⟨ρ, ⟨hpsd, htr, fun a ha ha1 => hrep a ⟨ha, ha1⟩⟩, ?_⟩
  intro ρ' ⟨hpsd', htr', hrep'⟩
  exact huniq ρ' ⟨hpsd', htr', fun a ha => hrep' a ha.1 ha.2⟩

end BuschTheorem
