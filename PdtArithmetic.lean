import Mathlib

namespace PDT

/-!
# Extended golden arithmetic bedrock (kernel-checked integer/ℚ identities)

Doc-comments give the field-theoretic meaning; the theorems are the integer/ℚ identities.
-/

/-- `disc(x⁴−x−1) = −27p⁴ + 256q³` (depressed quartic `x⁴+px+q`, `p=q=−1`) `= −283`.
This equals `det` of the trace form (`PdtSignature.det_M`); since `283` is prime the
discriminant is squarefree, so `ℤ[Q]` is the full ring of integers and the FIELD
discriminant of `ℚ(Q)` is also `−283`. -/
theorem disc_quartic : (-27 * (-1:ℤ)^4 + 256 * (-1)^3) = -283 := by norm_num

theorem prime_23 : Nat.Prime 23 := by norm_num
theorem prime_283 : Nat.Prime 283 := by norm_num

/-- `N(2Q−1) = ∏ᵢ (2Qᵢ−1) = 2⁴·f(1/2)` with `f = x⁴−x−1`, `f(1/2) = −23/16`, so `= −23`.
This welds the "23" to `E₄`'s 2-torsion / the spin structure. -/
theorem norm_2Q_sub_one : ((2:ℚ)^4 * ((1/2)^4 - 1/2 - 1)) = -23 := by norm_num

/-- The **23-weld**: `disc(x³−x−1)` (formula `−4p³−27q²`, `p=q=−1`) equals `N(2Q−1)`, both `−23`. -/
theorem weld_23 : (-4*(-1:ℚ)^3 - 27*(-1)^2) = (2:ℚ)^4 * ((1/2)^4 - 1/2 - 1) := by norm_num

/-- `N_{K/ℚ}(ρQ) = −1` for `K = ℚ(ρ,Q)` (degree 12; ρ,Q linearly disjoint, `[K:ℚ(ρ)]=4`,
`[K:ℚ(Q)]=3`): by the norm tower `N(ρQ) = N(ρ)^4 · N(Q)^3 = 1^4 · (−1)^3 = −1`. The unit
norm `N(ρQ) = −1` is what forces the derivation exponents to be integers. -/
theorem unit_norm_rhoQ : ((1:ℤ)^4 * (-1)^3) = -1 := by norm_num

/-- `dim su(4) = 4²−1 = 15` — the α exponent `(ρQ)^15`, per "exponent = group dimension". -/
theorem dim_su4 : ((4^2 - 1 : ℤ)) = 15 := by norm_num

end PDT
