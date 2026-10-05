import ThesisCommon.Analysis.LpMeanZeroRetracts
import ThesisCommon.Analysis.SchauderKernelTail

/-! The normalized nonconstant Haar system is a genuine Schauder basis
of the actual mean-zero interval Lp subspace, with coordinate bound six. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators
namespace ThesisCommon

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem intervalLpHaarBasis_coord_zero :
    (intervalLpHaarBasis 𝕜 p hp).coord 0 =
      lpHaarIntegral (𝕜 := 𝕜) (p := p.val) (μ := volume.restrict (Icc (0 : ℝ) 1)) := by
  change ((‖Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)‖ : ℝ) : 𝕜) •
    lpHaarIntegral = lpHaarIntegral
  have hn : ‖Lp.const p.val (volume.restrict (Icc (0 : ℝ) 1)) (1 : 𝕜)‖ = 1 := by
    rw [Lp.norm_const' _ _ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one p.property)) hp]
    simp
  rw [hn]
  simp

def intervalLpMeanZeroHaarBasis : NormalizedSchauderBasis 𝕜 (IntervalLpMeanZero 𝕜 p) where
  vector n := ⟨(intervalLpHaarBasis 𝕜 p hp).vector (n + 1), by
    change lpHaarIntegral ((intervalLpHaarBasis 𝕜 p hp).vector (n + 1)) = 0
    rw [← intervalLpHaarBasis_coord_zero 𝕜 p hp,
      (intervalLpHaarBasis 𝕜 p hp).biorthogonal, if_neg (by omega)]⟩
  coord n := ((intervalLpHaarBasis 𝕜 p hp).coord (n + 1)).comp
    (intervalLpMeanZeroSubmodule 𝕜 p).subtypeL
  biorthogonal i j := by
    change (intervalLpHaarBasis 𝕜 p hp).coord (i + 1)
      ((intervalLpHaarBasis 𝕜 p hp).vector (j + 1)) = if i = j then 1 else 0
    rw [(intervalLpHaarBasis 𝕜 p hp).biorthogonal]
    simp
  norm_vector n := (intervalLpHaarBasis 𝕜 p hp).norm_vector (n + 1)
  expansion x := by
    apply tendsto_subtype_rng.mpr
    have hx : (intervalLpHaarBasis 𝕜 p hp).coord 0 x.val = 0 := by
      rw [intervalLpHaarBasis_coord_zero]
      exact x.property
    have h := ((intervalLpHaarBasis 𝕜 p hp).expansion x.val).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext N
    simp [Function.comp_apply, Finset.sum_range_succ', hx]

theorem intervalLpMeanZeroHaarBasis_prefix_norm_le (N : ℕ) (x : IntervalLpMeanZero 𝕜 p) :
    ‖∑ i ∈ Finset.range N, (intervalLpMeanZeroHaarBasis 𝕜 p hp).coord i x •
      (intervalLpMeanZeroHaarBasis 𝕜 p hp).vector i‖ ≤ 3 * ‖x‖ := by
  have hx : (intervalLpHaarBasis 𝕜 p hp).coord 0 x.val = 0 := by
    rw [intervalLpHaarBasis_coord_zero]
    exact x.property
  have hh := intervalLpHaarBasis_prefix_norm_le 𝕜 p hp (N + 1) x.val
  rw [Finset.sum_range_succ', hx, zero_smul, add_zero] at hh
  have heq :
      ((∑ i ∈ Finset.range N, (intervalLpMeanZeroHaarBasis 𝕜 p hp).coord i x •
        (intervalLpMeanZeroHaarBasis 𝕜 p hp).vector i : IntervalLpMeanZero 𝕜 p) : IntervalLp 𝕜 p) =
      ∑ i ∈ Finset.range N, (intervalLpHaarBasis 𝕜 p hp).coord (i + 1) x.val •
        (intervalLpHaarBasis 𝕜 p hp).vector (i + 1) := by
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  change ‖((∑ i ∈ Finset.range N, (intervalLpMeanZeroHaarBasis 𝕜 p hp).coord i x •
    (intervalLpMeanZeroHaarBasis 𝕜 p hp).vector i : IntervalLpMeanZero 𝕜 p) : IntervalLp 𝕜 p)‖ ≤
      3 * ‖x.val‖
  rw [heq]
  exact hh

theorem intervalLpMeanZeroHaarBasis_coord_norm_le (n : ℕ) :
    ‖(intervalLpMeanZeroHaarBasis 𝕜 p hp).coord n‖ ≤ 6 := by
  convert (intervalLpMeanZeroHaarBasis 𝕜 p hp).coord_norm_le_of_prefix_bound
    (by norm_num : (0 : ℝ) ≤ 3) (intervalLpMeanZeroHaarBasis_prefix_norm_le 𝕜 p hp) n
    using 1 <;> norm_num

end ThesisCommon
