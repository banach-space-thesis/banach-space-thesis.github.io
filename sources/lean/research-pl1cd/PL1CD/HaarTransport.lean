import PL1CD.ProjectionFamily
import PL1CD.Variation
import PL1.ResolventNorms

noncomputable section
open scoped NNReal ENNReal

namespace PL1CD

open Variation
variable (𝕜 : Type) [RCLike 𝕜]

def haarEmbedding : HaarL1 𝕜 →L[𝕜] PL1.IntervalL1 𝕜 :=
  (PL1.IntervalWalsh.walshSumEmbedding 𝕜).toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => HaarL1 𝕜) 1 0)

def haarRetraction : PL1.IntervalL1 𝕜 →L[𝕜] HaarL1 𝕜 :=
  (lp.evalCLM 𝕜 (fun _ : ℕ => HaarL1 𝕜) 1 0).comp
    (PL1.IntervalWalsh.walshSumRetraction 𝕜)

@[simp] theorem haarRetraction_embedding (x : HaarL1 𝕜) :
    haarRetraction 𝕜 (haarEmbedding 𝕜 x) = x := by
  change (PL1.IntervalWalsh.walshSumRetraction 𝕜
    (PL1.IntervalWalsh.walshSumEmbedding 𝕜 (lp.single 1 0 x))) 0 = x
  simp

theorem norm_haarEmbedding_apply (x : HaarL1 𝕜) : ‖haarEmbedding 𝕜 x‖ = ‖x‖ := by
  change ‖PL1.IntervalWalsh.walshSumEmbedding 𝕜 (lp.single 1 0 x)‖ = ‖x‖
  rw [LinearIsometry.norm_map, lp.norm_single (by norm_num)]

theorem norm_haarEmbedding_le : ‖haarEmbedding 𝕜‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp [norm_haarEmbedding_apply]

theorem norm_haarRetraction_apply_le (x : PL1.IntervalL1 𝕜) :
    ‖haarRetraction 𝕜 x‖ ≤ ‖x‖ := by
  change ‖PL1.IntervalWalsh.walshSumRetraction 𝕜 x 0‖ ≤ ‖x‖
  calc
    _ ≤ ‖PL1.IntervalWalsh.walshSumRetraction 𝕜 x‖ :=
      lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖PL1.IntervalWalsh.walshSumRetraction 𝕜‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖x‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (PL1.IntervalWalsh.norm_walshSumRetraction_le 𝕜) (norm_nonneg x)

theorem norm_haarRetraction_le : ‖haarRetraction 𝕜‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  simpa only [one_mul] using norm_haarRetraction_apply_le 𝕜

def haarLift (T : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) : L1Operator 𝕜 :=
  (haarEmbedding 𝕜).comp (T.comp (haarRetraction 𝕜))

def haarExtract : L1Operator 𝕜 →L[𝕜] (HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) :=
  (ContinuousLinearMap.compL 𝕜 (HaarL1 𝕜) (PL1.IntervalL1 𝕜) (HaarL1 𝕜)
    (haarRetraction 𝕜)).comp
    ((ContinuousLinearMap.compL 𝕜 (HaarL1 𝕜) (PL1.IntervalL1 𝕜)
      (PL1.IntervalL1 𝕜)).flip (haarEmbedding 𝕜))

@[simp] theorem haarExtract_apply (T : L1Operator 𝕜) :
    haarExtract 𝕜 T = (haarRetraction 𝕜).comp (T.comp (haarEmbedding 𝕜)) := rfl

@[simp] theorem haarExtract_lift (T : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) :
    haarExtract 𝕜 (haarLift 𝕜 T) = T := by
  ext x
  simp [haarLift]

theorem norm_haarExtract_apply_le (T : L1Operator 𝕜) : ‖haarExtract 𝕜 T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  calc
    _ ≤ ‖T (haarEmbedding 𝕜 x)‖ := norm_haarRetraction_apply_le 𝕜 _
    _ ≤ ‖T‖ * ‖haarEmbedding 𝕜 x‖ := T.le_opNorm _
    _ = _ := by rw [norm_haarEmbedding_apply]

theorem norm_haarLift_le (T : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) : ‖haarLift 𝕜 T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖haarEmbedding 𝕜 (T (haarRetraction 𝕜 x))‖ ≤ _
  rw [norm_haarEmbedding_apply]
  exact (T.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_haarRetraction_apply_le 𝕜 x) (norm_nonneg T))

theorem norm_haarLift (T : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜) : ‖haarLift 𝕜 T‖ = ‖T‖ := by
  apply le_antisymm (norm_haarLift_le 𝕜 T)
  simpa only [haarExtract_lift] using norm_haarExtract_apply_le 𝕜 (haarLift 𝕜 T)

def unitResolvent (rates : ℕ → ℝ≥0) : HaarL1 𝕜 →L[𝕜] HaarL1 𝕜 :=
  PL1.Noise.resolventL1 𝕜 rates (PL1.Noise.dyadicTime 0)

theorem norm_unitResolvent (rates : ℕ → ℝ≥0) : ‖unitResolvent 𝕜 rates‖ = 1 :=
  PL1.Noise.norm_resolventL1_eq_one 𝕜 rates _

theorem haarRetraction_projection_embedding (rates : ℕ → ℝ≥0) (x : HaarL1 𝕜) :
    haarRetraction 𝕜 (intervalProjection 𝕜 rates (haarEmbedding 𝕜 x)) =
      unitResolvent 𝕜 rates x := by
  change (PL1.IntervalWalsh.walshSumRetraction 𝕜
    (PL1.IntervalWalsh.walshSumEmbedding 𝕜
      (PL1.Noise.projection 𝕜 rates
        (PL1.IntervalWalsh.walshSumRetraction 𝕜
          (PL1.IntervalWalsh.walshSumEmbedding 𝕜 (lp.single 1 0 x)))))) 0 = _
  rw [PL1.IntervalWalsh.walshSumRetraction_embedding,
    PL1.IntervalWalsh.walshSumRetraction_embedding]
  exact (PL1.Noise.dyadicSystem 𝕜 rates).projection_zero_zero x

def rangeWitness (rates : ℕ → ℝ≥0) :
    HaarL1 𝕜 →L[𝕜] (intervalProjection 𝕜 rates).range :=
  (intervalProjection 𝕜 rates).rangeRestrict.comp (haarEmbedding 𝕜)

def rangeEvaluation (rates : ℕ → ℝ≥0) :
    (intervalProjection 𝕜 rates).range →L[𝕜] HaarL1 𝕜 :=
  (haarRetraction 𝕜).comp (intervalProjection 𝕜 rates).range.subtypeL

theorem norm_rangeEvaluation_le (rates : ℕ → ℝ≥0) : ‖rangeEvaluation 𝕜 rates‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖haarRetraction 𝕜 (x : PL1.IntervalL1 𝕜)‖ ≤ 1 * ‖(x : PL1.IntervalL1 𝕜)‖
  simpa only [one_mul] using norm_haarRetraction_apply_le 𝕜 (x : PL1.IntervalL1 𝕜)

theorem rangeEvaluation_comp_witness (rates : ℕ → ℝ≥0) :
    (rangeEvaluation 𝕜 rates).comp (rangeWitness 𝕜 rates) = unitResolvent 𝕜 rates := by
  apply ContinuousLinearMap.ext
  intro x
  exact haarRetraction_projection_embedding 𝕜 rates x

theorem lift_resolvent_factors (rates : ℕ → ℝ≥0) :
    haarLift 𝕜 (unitResolvent 𝕜 rates) =
      (haarLift 𝕜 (ContinuousLinearMap.id 𝕜 (HaarL1 𝕜))).comp
        ((intervalProjection 𝕜 rates).comp
          (haarLift 𝕜 (ContinuousLinearMap.id 𝕜 (HaarL1 𝕜)))) := by
  ext x
  simp only [haarLift, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [haarRetraction_projection_embedding]

end PL1CD
