import ThesisCommon.Analysis.JamesMonotoneComposition
import ThesisCommon.Analysis.JamesStepIndex
import ThesisCommon.Analysis.PrimaryDirectSum

/-! Sampling a strictly increasing coordinate sequence has a contractive
right inverse obtained by step repetition. The resulting genuine bounded
decomposition splits James space into a copy of itself and the closed kernel
of sampling. The kernel is the space of sequences vanishing at the endpoints. -/
noncomputable section
open Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (σ : ℕ → ℕ) (hσ : StrictMono σ)

def jamesSample : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  jamesMonotoneCompose p hp σ hσ.monotone hσ.tendsto_atTop

def jamesRepeat : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  jamesMonotoneCompose p hp (jamesStepIndex σ)
    (jamesStepIndex_monotone σ) (jamesStepIndex_tendsto σ hσ)

@[simp] theorem jamesSample_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesSample (𝕜 := 𝕜) p hp σ hσ x n = x (σ n) :=
  jamesMonotoneCompose_apply p hp _ _ _ x n

@[simp] theorem jamesRepeat_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesRepeat (𝕜 := 𝕜) p hp σ hσ x n = x (jamesStepIndex σ n) :=
  jamesMonotoneCompose_apply p hp _ _ _ x n

theorem jamesSample_norm_le : ‖jamesSample (𝕜 := 𝕜) p hp σ hσ‖ ≤ 1 :=
  jamesMonotoneCompose_norm_le p hp _ _ _

theorem jamesRepeat_norm_le : ‖jamesRepeat (𝕜 := 𝕜) p hp σ hσ‖ ≤ 1 :=
  jamesMonotoneCompose_norm_le p hp _ _ _

theorem jamesSample_repeat :
    (jamesSample (𝕜 := 𝕜) p hp σ hσ).comp (jamesRepeat p hp σ hσ) =
      ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, jamesSample_apply, jamesRepeat_apply,
    jamesStepIndex_at_endpoint σ hσ, ContinuousLinearMap.id_apply]

theorem jamesRepeat_norm (x : JamesSequenceSpace 𝕜 p) :
    ‖jamesRepeat (𝕜 := 𝕜) p hp σ hσ x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((jamesRepeat (𝕜 := 𝕜) p hp σ hσ).le_opNorm x).trans
      ((mul_le_mul_of_nonneg_right (jamesRepeat_norm_le p hp σ hσ) (norm_nonneg x)).trans_eq
        (one_mul _))
  · have he := DFunLike.congr_fun (jamesSample_repeat (𝕜 := 𝕜) p hp σ hσ) x
    calc
      ‖x‖ = ‖jamesSample (𝕜 := 𝕜) p hp σ hσ (jamesRepeat (𝕜 := 𝕜) p hp σ hσ x)‖ :=
        congrArg norm he.symm
      _ ≤ ‖jamesSample (𝕜 := 𝕜) p hp σ hσ‖ * ‖jamesRepeat (𝕜 := 𝕜) p hp σ hσ x‖ :=
        (jamesSample (𝕜 := 𝕜) p hp σ hσ).le_opNorm _
      _ ≤ ‖jamesRepeat (𝕜 := 𝕜) p hp σ hσ x‖ := by
        exact (mul_le_mul_of_nonneg_right (jamesSample_norm_le p hp σ hσ)
          (norm_nonneg _)).trans_eq (one_mul _)

def jamesStepProjection : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p :=
  (jamesRepeat (𝕜 := 𝕜) p hp σ hσ).comp (jamesSample p hp σ hσ)

@[simp] theorem jamesStepProjection_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    jamesStepProjection (𝕜 := 𝕜) p hp σ hσ x n = x (σ (jamesStepIndex σ n)) := by
  simp only [jamesStepProjection, ContinuousLinearMap.comp_apply, jamesRepeat_apply,
    jamesSample_apply]

theorem jamesStepProjection_idempotent :
    (jamesStepProjection (𝕜 := 𝕜) p hp σ hσ).comp (jamesStepProjection p hp σ hσ) =
      jamesStepProjection p hp σ hσ := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply, jamesStepProjection_apply,
    jamesStepIndex_at_endpoint σ hσ]

theorem jamesStepProjection_norm_le : ‖jamesStepProjection (𝕜 := 𝕜) p hp σ hσ‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (jamesRepeat_norm_le p hp σ hσ) (jamesSample_norm_le p hp σ hσ)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

def jamesStepDecomposition : JamesSequenceSpace 𝕜 p ≃L[𝕜]
    JamesSequenceSpace 𝕜 p × LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp σ hσ).toLinearMap :=
  ContinuousLinearEquiv.equivOfRightInverse (jamesSample (𝕜 := 𝕜) p hp σ hσ)
    (jamesRepeat (𝕜 := 𝕜) p hp σ hσ)
    (fun x => DFunLike.congr_fun (jamesSample_repeat (𝕜 := 𝕜) p hp σ hσ) x)

theorem jamesSample_mem_ker_iff (x : JamesSequenceSpace 𝕜 p) :
    x ∈ LinearMap.ker (jamesSample (𝕜 := 𝕜) p hp σ hσ).toLinearMap ↔ ∀ n, x (σ n) = 0 := by
  change jamesSample (𝕜 := 𝕜) p hp σ hσ x = 0 ↔ _
  constructor
  · intro h n
    have he := congrArg (fun y : JamesSequenceSpace 𝕜 p => y n) h
    simpa only [jamesSample_apply, JamesSequenceSpace.zero_apply] using he
  · intro h
    ext n
    simpa only [jamesSample_apply, JamesSequenceSpace.zero_apply] using h n

end ThesisCommon
