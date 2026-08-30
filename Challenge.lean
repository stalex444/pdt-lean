/-
# Busch's theorem: Born-rule uniqueness on quantum effects (finite dimension)

Busch (2003): any generalized probability measure on the effects of a
finite-dimensional complex matrix algebra — a function that is nonnegative
on effects, additive whenever a sum of effects is again an effect, and
normalized at the identity — is represented by a unique density matrix.
This is the uniqueness of the Born rule in the POVM reading, and it holds
already at dimension 2, where Gleason's theorem (which requires dimension
at least 3) does not apply.

No continuity is assumed anywhere: additivity together with nonnegativity
forces real homogeneity on the effect interval (the monotone squeeze),
which is the analytic heart of the proof. `homogeneity_automatic` states
that step separately.

Effects are spelled in Mathlib vocabulary: `a.PosSemidef` together with
`(1 - a).PosSemidef`. Mathlib's order on matrices is the Loewner order,
provided as a scoped instance (`open scoped MatrixOrder`, in
`Mathlib.Analysis.Matrix.Order`, where `Matrix.nonneg_iff_posSemidef`
gives `0 ≤ A ↔ A.PosSemidef`); the statements here spell the effect
interval via `PosSemidef` directly, so they need no scoped order
instance.

Source: P. Busch, "Quantum states and generalized observables: a simple
proof of Gleason's theorem", Phys. Rev. Lett. 91, 120403 (2003);
quant-ph/9909073.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

namespace BuschTheorem

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Automatic homogeneity**: a nonnegative, additive, normalized
function on effects is automatically real-homogeneous on the effect
interval. No continuity hypothesis; monotonicity substitutes. -/
theorem homogeneity_automatic (f : Matrix n n ℂ → ℝ)
    (h0 : ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef → 0 ≤ f a)
    (hadd : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
      (1 - (a + b)).PosSemidef → f (a + b) = f a + f b)
    (h1 : f 1 = 1)
    {a : Matrix n n ℂ} (ha : a.PosSemidef) (ha1 : (1 - a).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (t • a) = t * f a := sorry

/-- **Busch's theorem**, finite dimension: every generalized probability
measure on the effects of `Matrix n n ℂ` is `a ↦ trace (ρ * a)` for a
unique density matrix `ρ` (positive semidefinite, trace one). Valid in
every finite dimension, in particular at dimension 2, where Gleason's
theorem does not apply. -/
theorem busch_representation [Nonempty n] (f : Matrix n n ℂ → ℝ)
    (h0 : ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef → 0 ≤ f a)
    (hadd : ∀ a b : Matrix n n ℂ, a.PosSemidef → b.PosSemidef →
      (1 - (a + b)).PosSemidef → f (a + b) = f a + f b)
    (h1 : f 1 = 1) :
    ∃! ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ a : Matrix n n ℂ, a.PosSemidef → (1 - a).PosSemidef →
        (ρ * a).trace = (f a : ℂ) := sorry

end BuschTheorem
