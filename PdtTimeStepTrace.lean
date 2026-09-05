import PdtSignatureForcing

/-!
# Multiplication by the quartic root and the trace timelike set

This file tests one proposed transport of the arithmetic clock into trace geometry:
using multiplication by the quartic root as a timelike-vector update. The existing
witness `tW = 4*r4 - 3*r4^2` has trace-square -36, whereas `r4*tW` has trace-square 91.
Consequently this update does not preserve the timelike set of the genuine trace form.

This is a statement about a specific linear action and a specific quadratic form.
It does not address the combinatorial word models of the companion `arithmetic-of-time`
repository, the interpretation of physical time, or transports using a different event
map. No physical identification is assumed.
-/

namespace PDT
namespace TimeStepTrace

open SignatureForcing

/-- Multiplying the existing timelike witness by the quartic root gives positive
trace-square. This uses the genuine field trace, not an unlinked matrix. -/
theorem traceForm_mul_tW :
    Algebra.traceForm ℚ (AdjoinRoot f4) (r4 * tW) (r4 * tW) = 91 := by
  rw [Algebra.traceForm_apply]
  have hx : (r4 * tW) * (r4 * tW) =
      (16 : ℚ) • r4 ^ 4 - (24 : ℚ) • r4 ^ 5 + (9 : ℚ) • r4 ^ 6 := by
    simp only [tW, Algebra.smul_def, map_ofNat]
    ring
  rw [hx, map_add, map_sub, map_smul, map_smul, map_smul,
    trace_r4_pow4, trace_r4_pow5, trace_r4_pow6]
  norm_num

/-- An exact timelike-to-spacelike witness for quartic-root multiplication. -/
theorem timelike_to_spacelike :
    Algebra.traceForm ℚ (AdjoinRoot f4) tW tW < 0 ∧
    0 < Algebra.traceForm ℚ (AdjoinRoot f4) (r4 * tW) (r4 * tW) := by
  rw [traceForm_tW, traceForm_mul_tW]
  norm_num

/-- Quartic-root multiplication does not preserve the full timelike set. -/
theorem not_preserves_timelike :
    ¬ (∀ x : AdjoinRoot f4,
      Algebra.traceForm ℚ (AdjoinRoot f4) x x < 0 →
      Algebra.traceForm ℚ (AdjoinRoot f4) (r4 * x) (r4 * x) < 0) := by
  intro h
  have hneg := h tW timelike_to_spacelike.1
  exact (not_lt_of_gt timelike_to_spacelike.2) hneg

end TimeStepTrace
end PDT

#print axioms PDT.TimeStepTrace.traceForm_mul_tW
#print axioms PDT.TimeStepTrace.timelike_to_spacelike
#print axioms PDT.TimeStepTrace.not_preserves_timelike
