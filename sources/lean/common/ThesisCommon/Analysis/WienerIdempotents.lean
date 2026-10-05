import ThesisCommon.Analysis.WienerFourierSeries
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Absolutely summable convolution sequences have only the two trivial
idempotents. Their continuous Fourier series take values in {0,1};
connectedness makes the series constant, and checked coefficient recovery
identifies the sequence. This is the scalar-algebra step of the prime-space
application, independent of the still-open operator quotient theorem. -/
noncomputable section
namespace ThesisCommon

theorem wienerConvolution_idempotent_iff (a : WienerSequences ℂ) :
    wienerConvolution a a = a ↔ a = 0 ∨ a = lp.single 1 0 1 := by
  constructor
  · intro ha
    have hs : wienerFourierSeries a * wienerFourierSeries a = wienerFourierSeries a := by
      rw [← wienerFourierSeries_convolution, ha]
    have hv (z : AddCircle (1 : ℝ)) :
        wienerFourierSeries a z = 0 ∨ wienerFourierSeries a z = 1 := by
      have he := congrArg (fun f : C(AddCircle (1 : ℝ), ℂ) => f z) hs
      change wienerFourierSeries a z * wienerFourierSeries a z = wienerFourierSeries a z at he
      have hz : wienerFourierSeries a z * (wienerFourierSeries a z - 1) = 0 := by
        linear_combination he
      simpa only [sub_eq_zero] using mul_eq_zero.mp hz
    have hc (z : AddCircle (1 : ℝ)) :
        wienerFourierSeries a z = wienerFourierSeries a 0 := by
      apply isPreconnected_univ.constant_of_mapsTo
        (T := ({0, 1} : Set ℂ)) (wienerFourierSeries a).continuous.continuousOn
        (fun x _ => ?_) (Set.mem_univ z) (Set.mem_univ 0)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv x
    rcases hv 0 with h0 | h1
    · left
      apply wienerFourierSeries_injective
      ext z
      simpa only [map_zero, ContinuousMap.zero_apply, h0] using hc z
    · right
      apply wienerFourierSeries_injective
      ext z
      simpa only [wienerFourierSeries_single, fourier_zero, h1] using hc z
  · rintro (rfl | rfl)
    · ext n
      simp [wienerConvolution_apply]
    · exact wienerConvolution_unit_left _

end ThesisCommon
