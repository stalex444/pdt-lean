import Mathlib
import PdtTraceForm
import PdtSignature
import PdtSignatureRho

/-!
# The signature-forcing step: a complex place forbids a positive-definite intrinsic metric

This module supplies the **implication** that sits between two facts established elsewhere in
this repository — that `K = ℚ[x]/(x⁴ − x − 1)` has one complex place, and that its trace form
has signature `(3,1)` (`PdtSignature.signature_3_1`, with the Gram-matrix identification in
`PdtTraceLink` and the basis-free invariants in `PdtTraceSignature`).

## The correction this module carries (binding; do not drop)

The sentence *"non-CM ⇒ no positive-definite intrinsic metric"* is **FALSE in both
directions** and must never be written:

* `ℚ(√2)` is **not** CM and its trace form `diag(2,4)` **is** positive definite;
* `ℚ(i)`, `ℚ(√−23)`, `ℚ(ζ₅)` **are** CM and their trace forms are indefinite —
  §4 below proves the `ℚ(ζ₅)` half, signature `(2,2)`.

The two counterexamples above settle it in both directions, so CM-ness is simply the wrong
criterion.  **The right one is `r₂ ≥ 1`**: the block of an associative form at a complex place
has determinant `−|λ_v|²`, hence negative index `≥ r₂`, instantiated at `r₂ = 1` for both
polynomials using `PdtTraceForm` and `PdtSignature`.  That is what is proved here.

## What is proved

**§1 — the general forcing lemma.** For a bilinear form `B` on a commutative `R`-algebra `A`
that is *associative* (`B (x*z) y = B x (z*y)` — the algebraic form of "intrinsic": built from
the algebra's own multiplication, no extra data), a square root of `-1` in `A` forces
`B j j = - B 1 1` (`assoc_sq_eq_neg_one`); over `ℝ` on a nontrivial algebra this rules out
positive-definiteness outright (`no_posDef_assoc_of_sq_neg_one`).

**§2 — the complex place, with Mathlib's genuine trace.** `Algebra.traceForm ℝ ℂ` has
`B 1 1 = 2`, `B I I = -2`: a hyperbolic `(1,1)` plane, never `(2,0)`. The **escape** is the
conjugation twist `H z w = Tr(z · conj w)`, which satisfies `H z z = 2‖z‖² > 0`
(`cmTwist_posDef`): positive-definiteness at a complex place needs a nontrivial involution.

**§2b — the block determinant, for EVERY twist `λ`.** The associative forms
at a complex place are `z, w ↦ Tr_{ℂ/ℝ}(λ·z·w)`; the Gram block in `{1, i}` is
`!![2a, -2b; -2b, -2a]` for `λ = a + bi`, with determinant `-4‖λ‖² < 0` for `λ ≠ 0`
(`lamForm_block_det`, `lamForm_block_det_neg`), and an explicit negative direction is produced
in every case (`lamForm_neg_direction`, `lamForm_not_posDef`). **Each complex place contributes
one negative direction whatever `λ` is: `negative index ≥ r₂`.**

**§3 / §3b — instantiation at `r₂ = 1` for BOTH PDT polynomials.**
*Quartic* `x⁴ − x − 1`: `x = 4·root − 3·root²` (in `ℤ[Q]`) has `Tr_{K/ℚ}(x²) = -36 < 0`
(`traceForm_tW`, from the genuine `Algebra.traceForm` via `PdtTraceForm`), so the intrinsic
metric is not positive definite; with `PdtSignature`'s congruence the signature is exactly
`(3,1)` — Lorentzian (`lorentzian_signature_of_pdt_quartic`).
*Cubic* `x³ − x − 1`: the genuine cubic trace form is built here (`PdtTraceForm` covers only
the quartic), shown equal to `PdtSignatureRho.Mρ` (`ctraceForm_eq_Mrho`), with timelike vector
`4 + 9ρ − 6ρ²`, `Tr(x²) = -138 < 0`, and signature `(2,1)`
(`lorentzian_signature_of_pdt_cubic`).

**§4 — the CM control, linear-algebra half.** For `ℚ(ζ₅)`, which IS CM: the untwisted
power-basis trace form `Mz` is `(2,2)` with its own timelike witness `1 + 4ζ`
(`Tr(x²) = -20`), while the conjugation-twisted form `Hz = 5·I − J` is positive definite
(`qform_Hz_pos`, via `5Σvᵢ² − (Σvᵢ)² = Σvᵢ² + Σ_{i<j}(vᵢ−vⱼ)²`). **The CM field parts company
with `ℚ(Q)` on the TWIST, not on the trace form.**

## What is NOT proved here (stated exactly, so nothing is overclaimed)

1. **`Aut(ℚ(Q)/ℚ) = 1` / `ℚ(Q)` is not CM** is NOT proved here. It is quoted from the
   splitting-field computation `Gal(x⁴ − x − 1) = S₄` (see `PdtGalois`), whose order 24 is not
   the generalized-dihedral order `2h = 8` a CM field would require, and it is used here only
   as commentary — no theorem below depends on it.
2. **The global quantifier over `λ`** — that for EVERY `λ ∈ K` the invariant form
   `T_λ(x,y) = Tr(λxy)` on `K` itself fails to be positive definite — is NOT proved here.
   §2b proves it at the complex place; transporting it to `K` needs
   `K ⊗_ℚ ℝ ≅ ℝ^{r₁} × ℂ^{r₂}` plus density of `K` in `K ⊗ ℝ`, neither of which is formalized
   in this repository. The case `λ = 1` is proved outright for both fields, by witness.
3. **The general signature theorem** "`(r₁+r₂, r₂)`, positive definite iff totally real" is NOT
   proved here, for the same missing decomposition. Both PDT instances are proved concretely.
4. **`r₁ = 2, r₂ = 1`** for `x⁴ − x − 1` (and `r₁ = 1, r₂ = 1` for `x³ − x − 1`) is NOT proved
   here; it is the standard real-root count of each polynomial, quoted.
5. That `Mz`, `Hz` **are** `ℚ(ζ₅)`'s power-basis Gram matrices is asserted, not proved here:
   they are the matrices `Mz i j = Tr(ζ^{i+j})` and `Hz i j = Tr(ζ^{i-j}) = 5·I − J`, with
   `Tr(ζ^k) = 4` when `5 ∣ k` and `−1` otherwise, which the reader can check directly. §4
   proves the linear algebra about them.
6. **SCOPE, and it is not small.** "No positive intrinsic metric" is a statement about
   ASSOCIATIVE forms on the `ℚ`-algebra. It is NOT true that `K ⊗ ℝ` carries no
   positive-definite form at all: the Minkowski form `Σ_v ‖σ_v(x)‖²` is positive definite for
   EVERY number field. Restricting attention to the associative forms on the bare `ℚ`-algebra
   is a MODELLING CHOICE, not a theorem — so nothing here licenses identifying the trace form
   with a spacetime metric, and no theorem below makes that identification.

No `sorry`, no `native_decide`.
-/
namespace PDT
namespace SignatureForcing

open LinearMap

/-! ## §1 — The general forcing lemma: a square root of `-1` flips the sign -/

/-- **A complex place flips the sign of an intrinsic form.**
If a bilinear form `B` on a commutative `R`-algebra `A` is *associative*
(`B (x*z) y = B x (z*y)` — the algebraic form of "built from the algebra's own
multiplication, no extra data") and `j ∈ A` satisfies `j² = -1`, then
`B j j = - B 1 1`. -/
theorem assoc_sq_eq_neg_one {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (B : LinearMap.BilinForm R A)
    (hassoc : ∀ x y z : A, B (x * z) y = B x (z * y))
    (j : A) (hj : j * j = -1) :
    B j j = - B 1 1 := by
  have h := hassoc j 1 j
  rw [hj, mul_one] at h
  rw [← h, map_neg, LinearMap.neg_apply]

/-- **No positive-definite intrinsic metric at a complex place.**
On a nontrivial real algebra containing a square root of `-1`, no associative bilinear
form is positive definite. This is the corrected forcing step: the obstruction is the
complex place, not non-CM-ness. -/
theorem no_posDef_assoc_of_sq_neg_one {A : Type*} [CommRing A] [Nontrivial A] [Algebra ℝ A]
    (B : LinearMap.BilinForm ℝ A)
    (hassoc : ∀ x y z : A, B (x * z) y = B x (z * y))
    (j : A) (hj : j * j = -1) :
    ¬ (∀ x : A, x ≠ 0 → 0 < B x x) := by
  intro hpos
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hj
    have h10 : (1 : A) = 0 := by linear_combination hj
    exact absurd h10 one_ne_zero
  have h1 : (0:ℝ) < B 1 1 := hpos 1 one_ne_zero
  have h2 : (0:ℝ) < B j j := hpos j hj0
  rw [assoc_sq_eq_neg_one B hassoc j hj] at h2
  linarith

/-- The trace form of any commutative algebra is associative: `Tr(xz·y) = Tr(x·zy)`.
This is what makes the trace form *intrinsic*. -/
theorem traceForm_assoc {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x y z : S) :
    Algebra.traceForm R S (x * z) y = Algebra.traceForm R S x (z * y) := by
  simp only [Algebra.traceForm_apply, mul_assoc]

/-! ## §2 — The complex place: `(1,1)` untwisted, `(2,0)` twisted -/

/-- The local trace form of a complex place on the unit: `Tr_{ℂ/ℝ}(1) = 2`. -/
theorem traceForm_C_one : Algebra.traceForm ℝ ℂ 1 1 = 2 := by
  simp [Algebra.traceForm_apply, Algebra.trace_complex_apply]

/-- The local trace form of a complex place on `i`: `Tr_{ℂ/ℝ}(i²) = -2`.
One positive and one negative direction: the complex place is a hyperbolic plane. -/
theorem traceForm_C_I : Algebra.traceForm ℝ ℂ Complex.I Complex.I = -2 := by
  simp [Algebra.traceForm_apply, Algebra.trace_complex_apply, Complex.I_mul_I]

/-- **The untwisted trace form of a complex place is NOT positive definite.** -/
theorem traceForm_C_not_posDef :
    ¬ (∀ z : ℂ, z ≠ 0 → 0 < Algebra.traceForm ℝ ℂ z z) :=
  no_posDef_assoc_of_sq_neg_one (Algebra.traceForm ℝ ℂ)
    (fun x y z => traceForm_assoc x y z) Complex.I Complex.I_mul_I

/-- The conjugation-twisted ("Born") form at a complex place, `H z w = Tr(z · conj w)`. -/
noncomputable def cmTwist (z w : ℂ) : ℝ := Algebra.traceForm ℝ ℂ z (starRingEnd ℂ w)

/-- `H z z = 2‖z‖²`. -/
theorem cmTwist_self (z : ℂ) : cmTwist z z = 2 * Complex.normSq z := by
  simp [cmTwist, Algebra.traceForm_apply, Algebra.trace_complex_apply, Complex.mul_conj]

/-- **The conjugation twist IS positive definite.** This is the escape route that a CM
field (or a totally real field, where the involution is the identity) possesses and a
field with trivial automorphism group does not. -/
theorem cmTwist_posDef (z : ℂ) (hz : z ≠ 0) : 0 < cmTwist z z := by
  rw [cmTwist_self]
  have : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  linarith

/-- **The dichotomy at a complex place, in one statement.** The untwisted intrinsic
(trace) form is indefinite; the conjugation-twisted form is positive definite. -/
theorem complex_place_dichotomy :
    Algebra.traceForm ℝ ℂ 1 1 = 2 ∧
    Algebra.traceForm ℝ ℂ Complex.I Complex.I = -2 ∧
    ¬ (∀ z : ℂ, z ≠ 0 → 0 < Algebra.traceForm ℝ ℂ z z) ∧
    (∀ z : ℂ, z ≠ 0 → 0 < cmTwist z z) :=
  ⟨traceForm_C_one, traceForm_C_I, traceForm_C_not_posDef, cmTwist_posDef⟩

/-! ## §2b — The complex-place BLOCK DETERMINANT, for EVERY twist `λ`

The goal is: the complex-place block determinant is `−|λ_v|²`, hence the negative index is
`≥ r₂`, instantiated at `r₂ = 1` for both polynomials. Here is the local half, in full
generality over `λ`.

The invariant (associative) forms on a number field are exactly `T_λ(x,y) = Tr(λxy)`. At a
complex place `v` the local algebra is `ℂ` and the form is `z, w ↦ Tr_{ℂ/ℝ}(λ·z·w)`. Its
Gram matrix in the real basis `{1, i}` is `!![2a, -2b; -2b, -2a]` for `λ = a + bi`, whose
determinant is `-4(a² + b²) = -4‖λ‖² < 0` for `λ ≠ 0`. A negative determinant on a `2×2`
symmetric real block forces one positive and one negative direction: **each complex place
contributes exactly one negative direction, for every λ.** Hence `negative index ≥ r₂`. -/

/-- The `λ`-twisted trace form at a complex place: `z, w ↦ Tr_{ℂ/ℝ}(λ·z·w)`. For `λ = 1`
this is the local trace form; these are exactly the associative forms on `ℂ` over `ℝ`. -/
noncomputable def lamForm (lam z w : ℂ) : ℝ := Algebra.traceForm ℝ ℂ (lam * z) w

/-- Every `lamForm` is associative, i.e. intrinsic to the algebra. -/
theorem lamForm_assoc (lam x y z : ℂ) : lamForm lam (x * z) y = lamForm lam x (z * y) := by
  simp only [lamForm, Algebra.traceForm_apply]
  ring_nf

/-- The diagonal of the `λ`-twisted form, expanded in real coordinates. -/
theorem lamForm_self (lam z : ℂ) :
    lamForm lam z z = 2 * (lam.re * (z.re ^ 2 - z.im ^ 2) - lam.im * (2 * z.re * z.im)) := by
  simp only [lamForm, Algebra.traceForm_apply, Algebra.trace_complex_apply, Complex.mul_re,
    Complex.mul_im]
  ring

theorem lamForm_one (lam : ℂ) : lamForm lam 1 1 = 2 * lam.re := by
  rw [lamForm_self]; simp

theorem lamForm_I (lam : ℂ) : lamForm lam Complex.I Complex.I = -2 * lam.re := by
  rw [lamForm_self]; simp

theorem lamForm_cross (lam : ℂ) : lamForm lam 1 Complex.I = -2 * lam.im := by
  simp only [lamForm, Algebra.traceForm_apply, Algebra.trace_complex_apply, Complex.mul_re,
    Complex.mul_im]
  simp

/-- **The complex-place block determinant is `-4‖λ‖²`.** (The factor `4` is the
`Tr_{ℂ/ℝ} = 2·Re` convention; the usual statement is `-|λ_v|²`, up to that normalisation.) -/
theorem lamForm_block_det (lam : ℂ) :
    lamForm lam 1 1 * lamForm lam Complex.I Complex.I - lamForm lam 1 Complex.I ^ 2
      = -4 * Complex.normSq lam := by
  rw [lamForm_one, lamForm_I, lamForm_cross, Complex.normSq_apply]
  ring

/-- The block determinant is strictly negative for every nonzero twist. -/
theorem lamForm_block_det_neg (lam : ℂ) (h : lam ≠ 0) :
    lamForm lam 1 1 * lamForm lam Complex.I Complex.I - lamForm lam 1 Complex.I ^ 2 < 0 := by
  rw [lamForm_block_det]
  have : 0 < Complex.normSq lam := Complex.normSq_pos.mpr h
  linarith

/-- **Every complex place contributes a negative direction, for every twist `λ ≠ 0`.**
This is the local half of "negative index ≥ r₂": one explicit timelike vector in the
`{1, i}` plane, produced from the sign of `Re λ` (or, when `Re λ = 0`, from `Im λ`). -/
theorem lamForm_neg_direction (lam : ℂ) (h : lam ≠ 0) :
    ∃ z : ℂ, z ≠ 0 ∧ lamForm lam z z < 0 := by
  rcases lt_trichotomy lam.re 0 with hr | hr | hr
  · exact ⟨1, one_ne_zero, by rw [lamForm_one]; linarith⟩
  · -- `Re λ = 0`, so `Im λ ≠ 0`; use `1 ± i`
    have him : lam.im ≠ 0 := by
      intro h0
      exact h (Complex.ext hr h0)
    rcases lt_or_gt_of_ne him with hi | hi
    · refine ⟨1 - Complex.I, ?_, ?_⟩
      · intro h0
        have := congrArg Complex.im h0
        simp at this
      · rw [lamForm_self]
        simp [hr]
        linarith
    · refine ⟨1 + Complex.I, ?_, ?_⟩
      · intro h0
        have := congrArg Complex.im h0
        simp at this
      · rw [lamForm_self]
        simp [hr]
        linarith
  · exact ⟨Complex.I, Complex.I_ne_zero, by rw [lamForm_I]; linarith⟩

/-- **No twist of the local trace form at a complex place is positive definite.**
Equivalently, at `r₂ = 1` the negative index is at least `1`: there is always a time
direction, whatever `λ` is chosen. -/
theorem lamForm_not_posDef (lam : ℂ) (h : lam ≠ 0) :
    ¬ (∀ z : ℂ, z ≠ 0 → 0 < lamForm lam z z) := by
  intro hpos
  obtain ⟨z, hz, hneg⟩ := lamForm_neg_direction lam h
  exact absurd (hpos z hz) (not_lt.mpr hneg.le)

/-! ## §3 — The instance: `K = ℚ[x]/(x⁴ − x − 1)`, the PDT quartic -/

/-- The timelike witness in `ℤ[Q] ⊂ K`: `x = 4·root − 3·root²`. -/
noncomputable def tW : AdjoinRoot f4 := 4 * r4 - 3 * r4 ^ 2

/-- **A timelike direction in the intrinsic metric of `ℚ(Q)`, exhibited.**
`Tr_{K/ℚ}(x²) = -36 < 0` for `x = 4·root − 3·root²`, computed from the genuine
`Algebra.traceForm ℚ (AdjoinRoot f4)` via the power sums `p₂ = 0, p₃ = 3, p₄ = 4`
of `PdtTraceForm`. -/
theorem traceForm_tW : Algebra.traceForm ℚ (AdjoinRoot f4) tW tW = -36 := by
  rw [Algebra.traceForm_apply]
  have hx : tW * tW
      = (16:ℚ) • r4 ^ 2 - (24:ℚ) • r4 ^ 3 + (9:ℚ) • r4 ^ 4 := by
    simp only [tW, Algebra.smul_def, map_ofNat]
    ring
  rw [hx, map_add, map_sub, map_smul, map_smul, map_smul,
    trace_r4_pow2, trace_r4_pow3, trace_r4_pow4]
  norm_num

/-- The witness is nonzero (it has nonzero trace-form self-pairing). -/
theorem tW_ne_zero : tW ≠ 0 := by
  intro h
  have h2 := traceForm_tW
  rw [h] at h2
  simp at h2

/-- **The intrinsic metric of `ℚ(Q)` is not positive definite** — the arithmetic content
of "no Euclidean intrinsic metric", proved by explicit witness rather than by any
CM-theoretic detour. -/
theorem traceForm_Q_not_posDef :
    ¬ (∀ x : AdjoinRoot f4, x ≠ 0 → 0 < Algebra.traceForm ℚ (AdjoinRoot f4) x x) := by
  intro hpos
  have := hpos tW tW_ne_zero
  rw [traceForm_tW] at this
  norm_num at this

/-- **The Lorentzian conclusion for the PDT quartic, bundled.**
(i) the genuine trace form of `K = ℚ[x]/(x⁴−x−1)` has an explicit timelike vector, so it
is not positive definite; (ii) its Gram matrix in the power basis is `PdtSignature.M`
(`PdtTraceForm.traceForm_eq_M4`); (iii) `M` is carried by an invertible rational
congruence to `diag(4, 4, -9/4, 283/36)` — three positive, one negative — and
`det M = -283 < 0`, so by Sylvester's law the signature is exactly `(3,1)`. -/
theorem lorentzian_signature_of_pdt_quartic :
    Algebra.traceForm ℚ (AdjoinRoot f4) tW tW = -36 ∧
    (∀ i j : Fin 4,
      Algebra.traceForm ℚ (AdjoinRoot f4) (pb4.basis (ι i)) (pb4.basis (ι j)) = M4 i j) ∧
    (PDT.P.transpose * PDT.M * PDT.P = PDT.D ∧ IsUnit PDT.P.det ∧ PDT.D.IsDiag ∧
      (0 < PDT.D 0 0 ∧ 0 < PDT.D 1 1 ∧ 0 < PDT.D 3 3) ∧ PDT.D 2 2 < 0 ∧ PDT.M.det = -283) :=
  ⟨traceForm_tW, traceForm_eq_M4,
    ⟨PDT.congruence, PDT.P_isUnit, PDT.D_isDiag,
      ⟨PDT.D00_pos, PDT.D11_pos, PDT.D33_pos⟩, PDT.D22_neg, PDT.det_M⟩⟩


/-! ## §3b — The same instance for the cubic `x³ − x − 1` (ρ's field, `r₂ = 1` also)

The instantiation at `r₂ = 1` is wanted for **both** polynomials. `PdtTraceForm`
covers only the quartic (its docstring claims `n = 3` too, but no cubic declaration exists),
so the genuine cubic trace form is built here, in the same style, and shown to equal the
matrix `PdtSignatureRho.Mρ` whose signature `(2,1)` is already kernel-verified. -/

noncomputable section CubicTrace

open Polynomial AdjoinRoot Algebra

/-- The cubic `X³ − X − 1`. -/
abbrev cf : ℚ[X] := X ^ 3 - X - 1

theorem cf_monic : (cf).Monic := by
  show ((X ^ 3 - X - 1 : ℚ[X])).Monic
  have : (X ^ 3 - X - 1 : ℚ[X]) = X ^ 3 + (- X - 1) := by ring
  rw [this]; apply monic_X_pow_add; compute_degree!

theorem cf_ne : cf ≠ 0 := cf_monic.ne_zero

theorem cf_deg : cf.natDegree = 3 := by
  show (X ^ 3 - X - 1 : ℚ[X]).natDegree = 3; compute_degree!

/-- The number field `ℚ(ρ)` with its power basis. -/
abbrev cpb := AdjoinRoot.powerBasis cf_ne
abbrev cr := root cf

theorem cpb_dim : cpb.dim = 3 := cf_deg

/-- The defining relation `ρ³ = ρ + 1`. -/
theorem cr_pow3 : cr ^ 3 = cr + 1 := by
  have h : aeval cr cf = 0 := by rw [aeval_eq, mk_self]
  show (root cf) ^ 3 = root cf + 1
  simp only [cf, map_sub, map_pow, map_one, aeval_X] at h
  linear_combination h

theorem cr_pow4 : cr ^ 4 = cr ^ 2 + cr := by linear_combination (cr) * cr_pow3
theorem cr_pow5 : cr ^ 5 = cr ^ 2 + cr + 1 := by
  linear_combination (cr ^ 2 + 1) * cr_pow3
theorem cr_pow6 : cr ^ 6 = cr ^ 2 + 2 * cr + 1 := by
  linear_combination (cr ^ 3 + cr + 1) * cr_pow3

/-- cast `Fin 3 → Fin cpb.dim`. -/
abbrev cι (i : Fin 3) : Fin cpb.dim := Fin.cast cpb_dim.symm i

theorem cbasis_val (i : Fin 3) : cpb.basis (cι i) = cr ^ (i : ℕ) := by
  rw [PowerBasis.coe_basis]; rfl

theorem cbasis_val0 : cpb.basis (cι 0) = cr ^ (0 : ℕ) := by rw [cbasis_val]; norm_num
theorem cbasis_val1 : cpb.basis (cι 1) = cr ^ (1 : ℕ) := by rw [cbasis_val]; norm_num
theorem cbasis_val2 : cpb.basis (cι 2) = cr ^ (2 : ℕ) := by rw [cbasis_val]; norm_num

theorem crepr_comb (a b c : ℚ) (j : Fin 3) :
    cpb.basis.repr (a • cr ^ (0 : ℕ) + b • cr ^ (1 : ℕ) + c • cr ^ (2 : ℕ)) (cι j)
      = ![a, b, c] j := by
  rw [← cbasis_val0, ← cbasis_val1, ← cbasis_val2]
  simp only [map_add, map_smul, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  fin_cases j <;> simp [cι, Fin.ext_iff]

theorem crepr0 (j : Fin 3) : cpb.basis.repr (cr ^ (0 : ℕ)) (cι j) = ![1,0,0] j := by
  have := crepr_comb 1 0 0 j; simpa using this
theorem crepr1 (j : Fin 3) : cpb.basis.repr (cr ^ (1 : ℕ)) (cι j) = ![0,1,0] j := by
  have := crepr_comb 0 1 0 j; simpa using this
theorem crepr2 (j : Fin 3) : cpb.basis.repr (cr ^ (2 : ℕ)) (cι j) = ![0,0,1] j := by
  have := crepr_comb 0 0 1 j; simpa using this
theorem crepr3 (j : Fin 3) : cpb.basis.repr (cr ^ (3 : ℕ)) (cι j) = ![1,1,0] j := by
  have h := crepr_comb 1 1 0 j
  rw [cr_pow3]
  rw [show (cr + 1 : AdjoinRoot cf)
        = (1:ℚ) • cr ^ (0:ℕ) + (1:ℚ) • cr ^ (1:ℕ) + (0:ℚ) • cr ^ (2:ℕ) by
        simp only [Algebra.smul_def, map_one, map_zero]; ring]
  exact h
theorem crepr4 (j : Fin 3) : cpb.basis.repr (cr ^ (4 : ℕ)) (cι j) = ![0,1,1] j := by
  have h := crepr_comb 0 1 1 j
  rw [cr_pow4]
  rw [show (cr ^ 2 + cr : AdjoinRoot cf)
        = (0:ℚ) • cr ^ (0:ℕ) + (1:ℚ) • cr ^ (1:ℕ) + (1:ℚ) • cr ^ (2:ℕ) by
        simp only [Algebra.smul_def, map_one, map_zero]; ring]
  exact h
theorem crepr5 (j : Fin 3) : cpb.basis.repr (cr ^ (5 : ℕ)) (cι j) = ![1,1,1] j := by
  have h := crepr_comb 1 1 1 j
  rw [cr_pow5]
  rw [show (cr ^ 2 + cr + 1 : AdjoinRoot cf)
        = (1:ℚ) • cr ^ (0:ℕ) + (1:ℚ) • cr ^ (1:ℕ) + (1:ℚ) • cr ^ (2:ℕ) by
        simp only [Algebra.smul_def, map_one]; ring]
  exact h
theorem crepr6 (j : Fin 3) : cpb.basis.repr (cr ^ (6 : ℕ)) (cι j) = ![1,2,1] j := by
  have h := crepr_comb 1 2 1 j
  rw [cr_pow6]
  rw [show (cr ^ 2 + 2 * cr + 1 : AdjoinRoot cf)
        = (1:ℚ) • cr ^ (0:ℕ) + (2:ℚ) • cr ^ (1:ℕ) + (1:ℚ) • cr ^ (2:ℕ) by
        simp only [Algebra.smul_def, map_ofNat, map_one]; ring]
  exact h

/-- `Algebra.trace` as the explicit `Fin 3` sum of `repr (ρ^{k+j})_j`. -/
theorem ctrace_eq_sum (k : ℕ) :
    Algebra.trace ℚ (AdjoinRoot cf) (cr ^ k)
      = ∑ j : Fin 3, cpb.basis.repr (cr ^ (k + (j : ℕ))) (cι j) := by
  rw [Algebra.trace_eq_matrix_trace cpb.basis, Matrix.trace]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  refine Fintype.sum_equiv (finCongr cpb_dim.symm)
        (fun j => cpb.basis.repr (cr ^ (k + (j : ℕ))) (cι j))
        (fun j => cpb.basis.repr (cr ^ k * cpb.basis j) j) (fun j => ?_) |>.symm
  have hb : cpb.basis (cι j) = cr ^ (j : ℕ) := cbasis_val j
  show cpb.basis.repr (cr ^ (k + (j : ℕ))) (cι j)
      = cpb.basis.repr (cr ^ k * cpb.basis (cι j)) (cι j)
  rw [hb, ← pow_add]

theorem ctrace_pow0 : Algebra.trace ℚ (AdjoinRoot cf) (cr ^ 0) = 3 := by
  rw [ctrace_eq_sum, Fin.sum_univ_three]
  rw [show (0:ℕ)+((0:Fin 3):ℕ) = 0 by rfl, show (0:ℕ)+((1:Fin 3):ℕ) = 1 by rfl,
      show (0:ℕ)+((2:Fin 3):ℕ) = 2 by rfl, crepr0, crepr1, crepr2]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

theorem ctrace_pow1 : Algebra.trace ℚ (AdjoinRoot cf) (cr ^ 1) = 0 := by
  rw [ctrace_eq_sum, Fin.sum_univ_three]
  rw [show (1:ℕ)+((0:Fin 3):ℕ) = 1 by rfl, show (1:ℕ)+((1:Fin 3):ℕ) = 2 by rfl,
      show (1:ℕ)+((2:Fin 3):ℕ) = 3 by rfl, crepr1, crepr2, crepr3]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

theorem ctrace_pow2 : Algebra.trace ℚ (AdjoinRoot cf) (cr ^ 2) = 2 := by
  rw [ctrace_eq_sum, Fin.sum_univ_three]
  rw [show (2:ℕ)+((0:Fin 3):ℕ) = 2 by rfl, show (2:ℕ)+((1:Fin 3):ℕ) = 3 by rfl,
      show (2:ℕ)+((2:Fin 3):ℕ) = 4 by rfl, crepr2, crepr3, crepr4]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

theorem ctrace_pow3 : Algebra.trace ℚ (AdjoinRoot cf) (cr ^ 3) = 3 := by
  rw [ctrace_eq_sum, Fin.sum_univ_three]
  rw [show (3:ℕ)+((0:Fin 3):ℕ) = 3 by rfl, show (3:ℕ)+((1:Fin 3):ℕ) = 4 by rfl,
      show (3:ℕ)+((2:Fin 3):ℕ) = 5 by rfl, crepr3, crepr4, crepr5]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

theorem ctrace_pow4 : Algebra.trace ℚ (AdjoinRoot cf) (cr ^ 4) = 2 := by
  rw [ctrace_eq_sum, Fin.sum_univ_three]
  rw [show (4:ℕ)+((0:Fin 3):ℕ) = 4 by rfl, show (4:ℕ)+((1:Fin 3):ℕ) = 5 by rfl,
      show (4:ℕ)+((2:Fin 3):ℕ) = 6 by rfl, crepr4, crepr5, crepr6]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val]

/-- **The genuine cubic trace form is `PdtSignatureRho.Mρ`.** -/
theorem ctraceForm_eq_Mrho (i j : Fin 3) :
    Algebra.traceForm ℚ (AdjoinRoot cf) (cpb.basis (cι i)) (cpb.basis (cι j)) = PDT.Mρ i j := by
  rw [Algebra.traceForm_apply, cbasis_val i, cbasis_val j, ← pow_add]
  have e0 := ctrace_pow0; have e1 := ctrace_pow1; have e2 := ctrace_pow2
  have e3 := ctrace_pow3; have e4 := ctrace_pow4
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.reduceAdd, e0, e1, e2, e3, e4] <;>
    rfl

/-- The timelike witness in `ℤ[ρ]`: `x = 4 + 9ρ − 6ρ²` has `Tr_{K/ℚ}(x²) = -138 < 0`. -/
noncomputable def tWrho : AdjoinRoot cf := 4 + 9 * cr - 6 * cr ^ 2

/-- **A timelike direction in the intrinsic metric of `ℚ(ρ)`, exhibited.** -/
theorem ctraceForm_tWrho : Algebra.traceForm ℚ (AdjoinRoot cf) tWrho tWrho = -138 := by
  rw [Algebra.traceForm_apply]
  have hx : tWrho * tWrho
      = (16:ℚ) • cr ^ 0 + (72:ℚ) • cr ^ 1 + (33:ℚ) • cr ^ 2 - (108:ℚ) • cr ^ 3
        + (36:ℚ) • cr ^ 4 := by
    simp only [tWrho, Algebra.smul_def, map_ofNat]
    ring
  rw [hx, map_add, map_sub, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_smul,
    ctrace_pow0, ctrace_pow1, ctrace_pow2, ctrace_pow3, ctrace_pow4]
  norm_num

theorem tWrho_ne_zero : tWrho ≠ 0 := by
  intro h
  have h2 := ctraceForm_tWrho
  rw [h] at h2
  simp at h2

/-- **The intrinsic metric of `ℚ(ρ)` is not positive definite either.** -/
theorem ctraceForm_rho_not_posDef :
    ¬ (∀ x : AdjoinRoot cf, x ≠ 0 → 0 < Algebra.traceForm ℚ (AdjoinRoot cf) x x) := by
  intro hpos
  have := hpos tWrho tWrho_ne_zero
  rw [ctraceForm_tWrho] at this
  norm_num at this

/-- **`r₂ = 1` instantiated for the CUBIC, the second PDT polynomial.** The genuine trace
form of `ℚ[x]/(x³−x−1)` is `Mρ`, it has the explicit timelike vector `4 + 9ρ − 6ρ²`
(`Tr(x²) = -138`), and `PdtSignatureRho`'s congruence pins its signature at `(2,1)`. -/
theorem lorentzian_signature_of_pdt_cubic :
    Algebra.traceForm ℚ (AdjoinRoot cf) tWrho tWrho = -138 ∧
    (∀ i j : Fin 3,
      Algebra.traceForm ℚ (AdjoinRoot cf) (cpb.basis (cι i)) (cpb.basis (cι j)) = PDT.Mρ i j) ∧
    (PDT.Pρ.transpose * PDT.Mρ * PDT.Pρ = PDT.Dρ ∧ IsUnit PDT.Pρ.det ∧ PDT.Dρ.IsDiag ∧
      (0 < PDT.Dρ 0 0 ∧ 0 < PDT.Dρ 1 1) ∧ PDT.Dρ 2 2 < 0 ∧ PDT.Mρ.det = -23) :=
  ⟨ctraceForm_tWrho, ctraceForm_eq_Mrho,
    ⟨PDT.congruenceρ, PDT.Pρ_isUnit, PDT.Dρ_isDiag,
      ⟨PDT.Dρ00_pos, PDT.Dρ11_pos⟩, PDT.Dρ22_neg, PDT.detMρ⟩⟩

end CubicTrace

/-! ## §4 — The CM control: `ℚ(ζ₅)` escapes on the TWIST, not on the trace form

`ℚ(ζ₅)` **is** a CM field (`r₁ = 0`, `r₂ = 2`, `Gal` cyclic of order 4). The matrices
below are its power-basis (`{1, ζ, ζ², ζ³}`) Gram matrices:

* `Mz i j = Tr(ζ^{i+j})` — the untwisted trace form, `p_k = 4` if `5 ∣ k` else `-1`;
* `Hz i j = Tr(ζ^i · conj(ζ^j)) = Tr(ζ^{i-j})` — the conjugation-twisted form, `= 5·I - J`.

The identification of these matrices with `ℚ(ζ₅)`'s forms is asserted, not proved here — they
are `Mz i j = Tr(ζ^{i+j})` and `Hz i j = Tr(ζ^{i-j})`, with `Tr(ζ^k) = 4` when `5 ∣ k` and `−1`
otherwise. What is proved HERE is the linear algebra:
`Mz` is `(2,2)` and has the explicit timelike vector `(1,4,0,0)` (the field element
`1 + 4ζ`, `Tr(x²) = -20`), while `Hz` is positive definite. -/

section CMControl

open Matrix

/-- The untwisted trace-form Gram matrix of `ℚ(ζ₅)` in the power basis. -/
def Mz : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,-1,-1,-1; -1,-1,-1,-1; -1,-1,-1,4; -1,-1,4,-1]

/-- The rational congruence diagonalising `Mz`. -/
def Pz : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 1/4, 0, 0; 0, 1, -2, 0; 0, 0, 1, -1/2; 0, 0, 1, 1/2]

/-- `Dz = Pzᵀ Mz Pz = diag(4, -5/4, 10, -5/2)`: two positive, two negative. -/
def Dz : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,0,0,0; 0,-5/4,0,0; 0,0,10,0; 0,0,0,-5/2]

/-- The conjugation-twisted Gram matrix of `ℚ(ζ₅)`: `Hz = 5·I - J`. -/
def Hz : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4,-1,-1,-1; -1,4,-1,-1; -1,-1,4,-1; -1,-1,-1,4]

/-- The quadratic form attached to a `4×4` Gram matrix. -/
def qform (G : Matrix (Fin 4) (Fin 4) ℚ) (v : Fin 4 → ℚ) : ℚ := ∑ i, ∑ j, v i * G i j * v j

theorem Mz_symm : Mz.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mz, Matrix.transpose_apply]

/-- `det Mz = 125 = disc ℚ(ζ₅)` (positive: an even number of negative eigenvalues). -/
theorem det_Mz : Mz.det = 125 := by
  simp only [Mz, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ]
  decide +kernel

theorem congruence_Mz : Pz.transpose * Mz * Pz = Dz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pz, Mz, Dz, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> norm_num

theorem det_Pz : Pz.det = 1 := by
  simp only [Pz, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc_zero,
    Fin.val_zero, Fin.val_succ]
  decide +kernel

theorem Pz_isUnit : IsUnit Pz.det := by rw [det_Pz]; exact isUnit_one

theorem Dz_isDiag : Dz.IsDiag := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Dz]

theorem Dz00_pos : (0:ℚ) < Dz 0 0 := by show (0:ℚ) < 4; norm_num
theorem Dz11_neg : Dz 1 1 < (0:ℚ) := by show (-5/4:ℚ) < 0; norm_num
theorem Dz22_pos : (0:ℚ) < Dz 2 2 := by show (0:ℚ) < 10; norm_num
theorem Dz33_neg : Dz 3 3 < (0:ℚ) := by show (-5/2:ℚ) < 0; norm_num

/-- **The CM field's UNTWISTED trace form has signature `(2,2)`** — an explicit invertible
rational congruence to `diag(4, -5/4, 10, -5/2)`. A CM field does NOT escape by having a
positive-definite trace form. -/
theorem signature_2_2_cyclotomic :
    Mz.IsSymm ∧ Pz.transpose * Mz * Pz = Dz ∧ IsUnit Pz.det ∧ Dz.IsDiag ∧
    (0 < Dz 0 0 ∧ 0 < Dz 2 2) ∧ (Dz 1 1 < 0 ∧ Dz 3 3 < 0) ∧ Mz.det = 125 :=
  ⟨Mz_symm, congruence_Mz, Pz_isUnit, Dz_isDiag, ⟨Dz00_pos, Dz22_pos⟩,
    ⟨Dz11_neg, Dz33_neg⟩, det_Mz⟩

/-- The timelike witness for the CM field's untwisted trace form: `x = 1 + 4ζ`,
`Tr(x²) = 4 + 8·(-1) + 16·(-1) = -20 < 0`. -/
theorem qform_Mz_witness : qform Mz ![1,4,0,0] = -20 := by
  simp [qform, Mz, Fin.sum_univ_four]
  norm_num

/-- The same computation for the PDT quartic's trace form (`PdtSignature.M`), matching the
field-level statement `traceForm_tW`: `x = 4·root - 3·root²`, `Tr(x²) = -36 < 0`. -/
theorem qform_M_witness : qform PDT.M ![0,4,-3,0] = -36 := by
  simp [qform, PDT.M, Fin.sum_univ_four]
  norm_num

/-- The sum-of-squares identity behind positive-definiteness of `Hz = 5·I - J`:
`5·Σvᵢ² - (Σvᵢ)² = Σvᵢ² + Σ_{i<j}(vᵢ-vⱼ)²`. -/
theorem qform_Hz_eq (a b c d : ℚ) :
    qform Hz ![a,b,c,d] = (a^2+b^2+c^2+d^2)
      + ((a-b)^2+(a-c)^2+(a-d)^2+(b-c)^2+(b-d)^2+(c-d)^2) := by
  simp [qform, Hz, Fin.sum_univ_four]
  ring

/-- **The CM field's CONJUGATION-TWISTED form IS positive definite.** This is the escape:
`ℚ(ζ₅)` has a nontrivial involution (complex conjugation `ζ ↦ ζ⁻¹`) and the twisted form
`Tr(x · x̄)` is Euclidean, while its untwisted trace form is `(2,2)`. -/
theorem qform_Hz_pos {a b c d : ℚ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < qform Hz ![a,b,c,d] := by
  have key : ∀ x : ℚ, x ≠ 0 → 0 < x ^ 2 :=
    fun x hx => lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  rw [qform_Hz_eq]
  rcases h with h | h | h | h
  · linarith [key a h, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg (a-b), sq_nonneg (a-c),
      sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]
  · linarith [key b h, sq_nonneg a, sq_nonneg c, sq_nonneg d, sq_nonneg (a-b), sq_nonneg (a-c),
      sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]
  · linarith [key c h, sq_nonneg a, sq_nonneg b, sq_nonneg d, sq_nonneg (a-b), sq_nonneg (a-c),
      sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]
  · linarith [key d h, sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a-b), sq_nonneg (a-c),
      sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

/-- **The control, in one statement.** On the UNTWISTED intrinsic (trace) form both fields
behave alike — each has an explicit timelike direction, so neither is Euclidean. They part
company on the TWIST: the CM field's conjugation-twisted form is positive definite. §2b rules
out every MULTIPLICATIVE twist `Tr(λ·z·w)` at a complex place, for any field; the conjugation
twist is not of that form (`cmTwist_posDef`), which is exactly how a CM field escapes. So the
contrast here is about which fields possess a conjugation to twist by at all. -/
theorem cm_control_contrast :
    qform PDT.M ![0,4,-3,0] = -36 ∧
    qform Mz ![1,4,0,0] = -20 ∧
    (∀ a b c d : ℚ, a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 → 0 < qform Hz ![a,b,c,d]) :=
  ⟨qform_M_witness, qform_Mz_witness, fun _ _ _ _ h => qform_Hz_pos h⟩

end CMControl

end SignatureForcing
end PDT

/-! ### Axiom audit -/

#print axioms PDT.SignatureForcing.assoc_sq_eq_neg_one
#print axioms PDT.SignatureForcing.no_posDef_assoc_of_sq_neg_one
#print axioms PDT.SignatureForcing.traceForm_assoc
#print axioms PDT.SignatureForcing.traceForm_C_one
#print axioms PDT.SignatureForcing.traceForm_C_I
#print axioms PDT.SignatureForcing.traceForm_C_not_posDef
#print axioms PDT.SignatureForcing.cmTwist_self
#print axioms PDT.SignatureForcing.cmTwist_posDef
#print axioms PDT.SignatureForcing.complex_place_dichotomy
#print axioms PDT.SignatureForcing.traceForm_tW
#print axioms PDT.SignatureForcing.tW_ne_zero
#print axioms PDT.SignatureForcing.traceForm_Q_not_posDef
#print axioms PDT.SignatureForcing.lorentzian_signature_of_pdt_quartic
#print axioms PDT.SignatureForcing.Mz_symm
#print axioms PDT.SignatureForcing.det_Mz
#print axioms PDT.SignatureForcing.congruence_Mz
#print axioms PDT.SignatureForcing.det_Pz
#print axioms PDT.SignatureForcing.Pz_isUnit
#print axioms PDT.SignatureForcing.Dz_isDiag
#print axioms PDT.SignatureForcing.Dz00_pos
#print axioms PDT.SignatureForcing.Dz11_neg
#print axioms PDT.SignatureForcing.Dz22_pos
#print axioms PDT.SignatureForcing.Dz33_neg
#print axioms PDT.SignatureForcing.signature_2_2_cyclotomic
#print axioms PDT.SignatureForcing.qform_Mz_witness
#print axioms PDT.SignatureForcing.qform_M_witness
#print axioms PDT.SignatureForcing.qform_Hz_eq
#print axioms PDT.SignatureForcing.qform_Hz_pos
#print axioms PDT.SignatureForcing.cm_control_contrast
#print axioms PDT.SignatureForcing.lamForm_assoc
#print axioms PDT.SignatureForcing.lamForm_self
#print axioms PDT.SignatureForcing.lamForm_one
#print axioms PDT.SignatureForcing.lamForm_I
#print axioms PDT.SignatureForcing.lamForm_cross
#print axioms PDT.SignatureForcing.lamForm_block_det
#print axioms PDT.SignatureForcing.lamForm_block_det_neg
#print axioms PDT.SignatureForcing.lamForm_neg_direction
#print axioms PDT.SignatureForcing.lamForm_not_posDef
#print axioms PDT.SignatureForcing.cf_monic
#print axioms PDT.SignatureForcing.cf_deg
#print axioms PDT.SignatureForcing.cr_pow3
#print axioms PDT.SignatureForcing.cr_pow4
#print axioms PDT.SignatureForcing.cr_pow5
#print axioms PDT.SignatureForcing.cr_pow6
#print axioms PDT.SignatureForcing.cbasis_val
#print axioms PDT.SignatureForcing.crepr_comb
#print axioms PDT.SignatureForcing.crepr0
#print axioms PDT.SignatureForcing.crepr1
#print axioms PDT.SignatureForcing.crepr2
#print axioms PDT.SignatureForcing.crepr3
#print axioms PDT.SignatureForcing.crepr4
#print axioms PDT.SignatureForcing.crepr5
#print axioms PDT.SignatureForcing.crepr6
#print axioms PDT.SignatureForcing.ctrace_eq_sum
#print axioms PDT.SignatureForcing.ctrace_pow0
#print axioms PDT.SignatureForcing.ctrace_pow1
#print axioms PDT.SignatureForcing.ctrace_pow2
#print axioms PDT.SignatureForcing.ctrace_pow3
#print axioms PDT.SignatureForcing.ctrace_pow4
#print axioms PDT.SignatureForcing.ctraceForm_eq_Mrho
#print axioms PDT.SignatureForcing.ctraceForm_tWrho
#print axioms PDT.SignatureForcing.tWrho_ne_zero
#print axioms PDT.SignatureForcing.ctraceForm_rho_not_posDef
#print axioms PDT.SignatureForcing.lorentzian_signature_of_pdt_cubic
#print axioms PDT.SignatureForcing.cf_ne
#print axioms PDT.SignatureForcing.cpb_dim
#print axioms PDT.SignatureForcing.cbasis_val0
#print axioms PDT.SignatureForcing.cbasis_val1
#print axioms PDT.SignatureForcing.cbasis_val2
