import ThesisCommon.Analysis.WienerConvolutionLaws
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Seminorm

/-! Continuous bilinear convolution on the literal Wiener sequence space,
and a norm-density principle for continuous seminorm kernels. -/
noncomputable section
open Filter
open scoped BigOperators ENNReal
namespace ThesisCommon
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜]

def wienerConvolutionBilinear :
    WienerSequences 𝕜 →L[𝕜] WienerSequences 𝕜 →L[𝕜] WienerSequences 𝕜 :=
  (LinearMap.mk₂ 𝕜 wienerConvolution wienerConvolution_add_left
    wienerConvolution_smul_left wienerConvolution_add_right
    wienerConvolution_smul_right).mkContinuous₂ 1
      (fun a b => by simpa only [one_mul] using norm_wienerConvolution_le a b)

theorem wienerConvolutionBilinear_apply (a b : WienerSequences 𝕜) :
    wienerConvolutionBilinear a b = wienerConvolution a b := rfl

theorem wienerConvolution_single_single (i j : ℤ) (a b : 𝕜) :
    wienerConvolution (lp.single 1 i a) (lp.single 1 j b) =
      lp.single 1 (i+j) (a*b) := by
  ext n
  rw [wienerConvolution_apply, tsum_eq_single i]
  · by_cases hn : n = i+j
    · subst n
      simp
    · have hni : n-i ≠ j := by omega
      simp [lp.single_apply, hn, hni]
  · intro k hk
    simp [lp.single_apply, hk]

theorem wiener_map_seminorm_zero_of_single
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : Seminorm 𝕜 E) (hp : Continuous p) (F : WienerSequences 𝕜 →L[𝕜] E)
    (h : ∀ i : ℤ, ∀ c : 𝕜, p (F (lp.single 1 i c)) = 0)
    (a : WienerSequences 𝕜) : p (F a) = 0 := by
  classical
  have hc : IsClosed {b : WienerSequences 𝕜 | p (F b) = 0} :=
    isClosed_eq (hp.comp F.continuous) continuous_const
  apply hc.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a)
  apply Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    change p (F (∑ j ∈ insert i s, lp.single 1 j (a j))) = 0
    rw [Finset.sum_insert hi, map_add]
    apply le_antisymm _ (apply_nonneg _ _)
    exact (map_add_le_add p _ _).trans_eq (by rw [h, hs, zero_add])

end ThesisCommon
