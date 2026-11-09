import SurveyStatements.P5BiTreeStabilizationMeans

/-! Normalize rectangle slices by the positive mass of their fixed
coordinate. Their bounds remain M, so one simultaneous signed split can
control actual normalized rectangle means together with past slices. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def DyadicBiTrace.normalizedLeftSlice {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (Q : LpHaarFiniteParent) : DyadicTrace 𝕜 M where
  value P := a.value P Q.index /
    ((volume.restrict (Icc (0 : ℝ) 1)).real Q.set : 𝕜)
  norm_le P := by
    rw [norm_div, RCLike.norm_ofReal, abs_of_pos Q.mass_pos]
    apply (div_le_iff₀ Q.mass_pos).mpr
    exact a.norm_le P Q.index
  congr P R hPR := by rw [a.congr_left P R Q.index hPR]
  additive P R S hdis hunion := by
    rw [a.additive_left P R S Q.index hdis hunion, add_div]

def DyadicBiTrace.normalizedRightSlice {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P : LpHaarFiniteParent) : DyadicTrace 𝕜 M :=
  a.flip.normalizedLeftSlice P

theorem parentTrace_normalizedLeftSlice {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P Q : LpHaarFiniteParent) :
    lpHaarParentTrace (a.normalizedLeftSlice Q).value P = rectangleMean a P Q := by
  simp only [lpHaarParentTrace, DyadicBiTrace.normalizedLeftSlice,
    rectangleMean, div_div, mul_comm]

theorem parentTrace_normalizedRightSlice {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P Q : LpHaarFiniteParent) :
    lpHaarParentTrace (a.normalizedRightSlice P).value Q = rectangleMean a P Q := by
  simp only [lpHaarParentTrace, DyadicBiTrace.normalizedRightSlice,
    DyadicBiTrace.normalizedLeftSlice, DyadicBiTrace.flip, rectangleMean, div_div]

theorem rectangleMean_congr_left {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P R Q : LpHaarFiniteParent) (hPR : P.set = R.set) :
    rectangleMean a P Q = rectangleMean a R Q := by
  unfold rectangleMean
  rw [hPR, a.congr_left P.index R.index Q.index hPR]

theorem rectangleMean_congr_right {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P Q R : LpHaarFiniteParent) (hQR : Q.set = R.set) :
    rectangleMean a P Q = rectangleMean a P R := by
  unfold rectangleMean
  rw [hQR, a.congr_right P.index Q.index R.index hQR]

end SurveyStatements.P5.BiTree
