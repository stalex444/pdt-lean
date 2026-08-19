import Mathlib

/-!
# Challenge: the arithmetic of the Pisot-boundary fields and the two-rulers identity

This module is the small, trusted surface to audit. Results in three groups,
stated with `sorry`; proved versions are in `Solution.lean`.

**Group A — the fields.** The trinomials `x³ − x − 1` and `x⁴ − x − 1` are
irreducible over `ℚ`, and the genuine algebra norms of their adjoined roots
are `N(ρ) = 1` and `N(Q) = −1`: both roots are units of their fields, computed
through Mathlib's `Algebra.norm` on `AdjoinRoot`, not by hand-substituted
values.

**Group B — Sylvester congruence certificates.** For the trace-form Gram
matrices of the power bases (entries `Tr(xⁱ⁺ʲ)`, recorded here as explicit
rational matrices), explicit unimodular congruences diagonalise them:
`Pᵀ M P = D` with `det M = −283`, `det P = −1`, and diagonal
`(4, 4, −9/4, 283/36)` for the quartic — inertia `(3,1)`, one negative
direction — and `Pᵀ M P = D` with `det M = −23`, `det P = 1`, diagonal
`(3, 2, −23/6)` for the cubic — inertia `(2,1)`. Sylvester's law of inertia
then reads the signatures off the diagonals.

**Group C — the two rulers.** On the 2-dimensional rational model of a
complex place (basis `1, i`), the positive Born form is the indefinite trace
form composed with conjugation, `G_born = G_tr · C`; the rotation `J` is an
isometry of the Born form and an anti-isometry of the trace form; the Born
companion `Jᵀ G_born` is alternating with determinant one (a symplectic
form), while the trace companion is symmetric. One pairing, two readings,
differing by exactly the conjugation.
-/

namespace ComplexPlaceArithmetic

open Polynomial

/-! ## Group A — irreducibility and unit norms -/

/-- `x³ − x − 1` is irreducible over `ℚ`. -/
theorem cubic_irreducible : Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  sorry

/-- `x⁴ − x − 1` is irreducible over `ℚ`. -/
theorem quartic_irreducible : Irreducible (X ^ 4 - X - 1 : ℚ[X]) := by
  sorry

/-- The cubic `x³ − x − 1` as a rational polynomial. -/
noncomputable def fρ : ℚ[X] := X ^ 3 - X - 1

/-- The quartic `x⁴ − x − 1` as a rational polynomial. -/
noncomputable def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The genuine algebra norm of the cubic's root is `1`: `ρ` is a unit. -/
theorem norm_cubic_root : Algebra.norm ℚ (AdjoinRoot.root fρ) = 1 := by
  sorry

/-- The genuine algebra norm of the quartic's root is `−1`: `Q` is a unit. -/
theorem norm_quartic_root : Algebra.norm ℚ (AdjoinRoot.root fQ) = -1 := by
  sorry

/-! ## Group B — Sylvester congruence certificates for the trace forms -/

/-- Trace-form Gram matrix of the quartic's power basis: entries `Tr(xⁱ⁺ʲ)`. -/
def M4 : Matrix (Fin 4) (Fin 4) ℚ := !![4,0,0,3; 0,0,3,4; 0,3,4,0; 3,4,0,3]

/-- Explicit congruence matrix for the quartic certificate. -/
def P4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, -3/4;
     0, 0, 1, 16/9;
     0, 1, -3/4, -4/3;
     0, 0, 0, 1]

/-- The diagonalised quartic trace form: three positive entries, one negative —
inertia `(3, 1)`. -/
def D4 : Matrix (Fin 4) (Fin 4) ℚ := !![4,0,0,0; 0,4,0,0; 0,0,-9/4,0; 0,0,0,283/36]

/-- The quartic Sylvester congruence: `P4ᵀ · M4 · P4 = D4`. -/
theorem quartic_congruence : P4.transpose * M4 * P4 = D4 := by
  sorry

/-- `det M4 = −283`: the quartic's discriminant appears as the Gram determinant. -/
theorem quartic_gram_det : M4.det = -283 := by
  sorry

/-- `P4` is unimodular: `det P4 = −1`. -/
theorem quartic_P_unimodular : P4.det = -1 := by
  sorry

/-- Trace-form Gram matrix of the cubic's power basis. -/
def M3 : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,2; 0,2,3; 2,3,2]

/-- Explicit congruence matrix for the cubic certificate. -/
def P3 : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,-2/3; 0,1,-3/2; 0,0,1]

/-- The diagonalised cubic trace form: two positive entries, one negative —
inertia `(2, 1)`. -/
def D3 : Matrix (Fin 3) (Fin 3) ℚ := !![3,0,0; 0,2,0; 0,0,-23/6]

/-- The cubic Sylvester congruence: `P3ᵀ · M3 · P3 = D3`. -/
theorem cubic_congruence : P3.transpose * M3 * P3 = D3 := by
  sorry

/-- `det M3 = −23`: the cubic's discriminant as the Gram determinant. -/
theorem cubic_gram_det : M3.det = -23 := by
  sorry

/-- `P3` is unimodular: `det P3 = 1`. -/
theorem cubic_P_unimodular : P3.det = 1 := by
  sorry

/-! ## Group C — the two rulers on the rational model of a complex place -/

/-- The indefinite trace ruler on the model `(1, i)`: `diag(1, −1)`. -/
def Gtr : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- The positive Born ruler on the model: the identity form. -/
def Gborn : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- The rotation `J` (multiplication by `i` on the model). -/
def Jc : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

/-- Conjugation on the model: `diag(1, −1)`. -/
def Cnj : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- The Born companion form `Jᵀ · G_born` — the symplectic form of the place. -/
def omegaB : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]

/-- **The two-rulers identity, packaged.** The Born ruler is the trace ruler
composed with conjugation; the rotation `J` preserves the Born ruler and
anti-preserves the trace ruler; the Born companion is alternating with
determinant one (symplectic); the trace companion is symmetric. -/
theorem two_rulers :
    Gborn = Gtr * Cnj ∧
    Jc.transpose * Gborn * Jc = Gborn ∧
    Jc.transpose * Gtr * Jc = -Gtr ∧
    Jc.transpose * Gborn = omegaB ∧
    omegaB.transpose = -omegaB ∧
    omegaB.det = 1 ∧
    (Jc.transpose * Gtr).transpose = Jc.transpose * Gtr := by
  sorry

end ComplexPlaceArithmetic
