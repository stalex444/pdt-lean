import Mathlib

/-!
# The complex place: the dagger, the two forms, and the symplectic form

On the single complex place `K_v ≅ ℂ` of `K = ℚ[x]/(x⁴ − x − 1)`, realized as `ℝ²`
in the basis `{1, i}`, four canonical objects appear:

  `Gtr`  = `!![1,0; 0,-1]`   the trace form  `Re(z·w)`   (signature `(1,1)`),
  `Gborn`= `!![1,0; 0,1]`    the Born form   `Re(z̄·w)`  (positive-definite),
  `Jc`   = `!![0,-1; 1,0]`   the complex structure `J` (multiplication by `i`),
  `Cnj`  = `!![1,0; 0,-1]`   complex conjugation `σ` (the dagger).

We prove, all kernel-checked over `ℚ`:

* `born_eq_trace_comp_conj` : `Gborn = Gtr * Cnj` — the **dagger identity**: the Born
  form is the trace form precomposed with conjugation, `G_Born(x,y) = G_trace(x, σ y)`.
* `J_born_isometry`      : `Jᵀ Gborn J = Gborn`  — `J` is a Born isometry (the unitary phase).
* `J_trace_antiisometry` : `Jᵀ Gtr J = -Gtr`     — `J` is a trace anti-isometry (the Lorentzian
  time-rotation).
* `omega_born_skew`      : `ωᵀ = -ω` for `ω := Jᵀ Gborn` — the companion form of the Born
  metric is **alternating** (a symplectic form); it is `Im(z̄·w)`, the imaginary part of
  the Born rule; and `omega_born_nondegenerate` : `det ω = 1`.
* `omega_trace_symm`     : the companion `Jᵀ Gtr` of the (J-anti-invariant) trace form is
  **symmetric**, not alternating — so the symplectic structure lives on the Born reading,
  not the spacetime (trace) reading.

This is the linear-algebra core of the "Fault Line A" result (Proposition 1 of the
companion paper *The Arithmetic of a Complex Place*): `g(J·,·)` is alternating iff `g`
is `J`-invariant, and it is the Born metric — not the trace form — that is `J`-invariant.

The axiom set of every theorem below is exactly `{propext, Classical.choice, Quot.sound}`.
-/

namespace PDT

open Matrix

/-- Trace form on the complex place, `Re(z·w)`; signature `(1,1)`. -/
def Gtr : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- Born (Hermitian) form on the complex place, `Re(z̄·w)`; positive-definite. -/
def Gborn : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- The complex structure `J` = multiplication by `i`. -/
def Jc : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

/-- Complex conjugation `σ` at the place (the dagger). -/
def Cnj : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- The companion form of the Born metric, `ω = Jᵀ Gborn` (i.e. `ω(x,y) = g(Jx,y)`). -/
def omegaB : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]

/-- **The dagger identity.** The Born form is the trace form precomposed with the
conjugation: `Gborn = Gtr * Cnj`, i.e. `G_Born(x,y) = G_trace(x, σ y)`. -/
theorem born_eq_trace_comp_conj : Gborn = Gtr * Cnj := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Gborn, Gtr, Cnj, Matrix.mul_apply, Fin.sum_univ_two]

/-- **`J` is a Born isometry** (the unitary quantum phase): `Jᵀ Gborn J = Gborn`. -/
theorem J_born_isometry : Jc.transpose * Gborn * Jc = Gborn := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jc, Gborn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- **`J` is a trace anti-isometry** (the Lorentzian time-rotation): `Jᵀ Gtr J = -Gtr`. -/
theorem J_trace_antiisometry : Jc.transpose * Gtr * Jc = -Gtr := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jc, Gtr, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.neg_apply]

/-- The companion `Jᵀ Gborn` of the Born metric equals the explicit form `ω`. -/
theorem omegaB_eq : Jc.transpose * Gborn = omegaB := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [omegaB, Jc, Gborn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- **The symplectic form is alternating.** `ω = Jᵀ Gborn` is skew-symmetric,
`ωᵀ = -ω`. This is `Im(z̄·w)`, the imaginary part of the Born rule. -/
theorem omega_born_skew : omegaB.transpose = -omegaB := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [omegaB, Matrix.transpose_apply, Matrix.neg_apply]

/-- The symplectic form is nondegenerate: `det ω = 1 ≠ 0`. -/
theorem omega_born_nondegenerate : omegaB.det = 1 := by
  simp [omegaB, Matrix.det_fin_two]

/-- **The trace form's companion is NOT alternating** — it is symmetric:
`(Jᵀ Gtr)ᵀ = Jᵀ Gtr`. So the symplectic structure lives on the Born reading, not the
spacetime (trace) reading. -/
theorem omega_trace_symm : (Jc.transpose * Gtr).transpose = Jc.transpose * Gtr := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jc, Gtr, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- **Bundled statement (Fault Line A / Proposition 1).**
On the complex place: the Born form is the trace form twisted by the dagger; the same
`J` is a Born isometry and a trace anti-isometry; the Born companion form is alternating
and nondegenerate (a symplectic form), while the trace companion is symmetric. -/
theorem faultA_symplectic :
    Gborn = Gtr * Cnj ∧
    Jc.transpose * Gborn * Jc = Gborn ∧
    Jc.transpose * Gtr * Jc = -Gtr ∧
    Jc.transpose * Gborn = omegaB ∧
    omegaB.transpose = -omegaB ∧
    omegaB.det = 1 ∧
    (Jc.transpose * Gtr).transpose = Jc.transpose * Gtr :=
  ⟨born_eq_trace_comp_conj, J_born_isometry, J_trace_antiisometry,
   omegaB_eq, omega_born_skew, omega_born_nondegenerate, omega_trace_symm⟩

end PDT
