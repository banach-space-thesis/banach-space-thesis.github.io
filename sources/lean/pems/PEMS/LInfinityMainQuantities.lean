import PEMS.ContinuousMapFourQuantities
import ThesisCommon.Analysis.FiniteLInfinityStoneRepresentation

/-! The full source Theorem 1.14 on the actual Lebesgue L-infinity space.
The compact extremally disconnected Stone models are constructed from
the fragments of the constant-one element of real L1. -/
noncomputable section
open ThesisCommon MeasureTheory Set
namespace PEMS

theorem theorem_1_14_real
    (T : LInfinityUnitInterval ℝ →L[ℝ] LInfinityUnitInterval ℝ) : Theorem_1_14 T := by
  exact four_quantities_of_real_extremallyDisconnected_model
    (realStoneLInfinityEquiv (volume.restrict (Icc (0 : ℝ) 1))).symm T

theorem theorem_1_14_complex
    (T : LInfinityUnitInterval ℂ →L[ℂ] LInfinityUnitInterval ℂ) : Theorem_1_14 T := by
  exact four_quantities_of_complex_extremallyDisconnected_model
    (complexStoneLInfinityEquiv (volume.restrict (Icc (0 : ℝ) 1))).symm T

end PEMS
