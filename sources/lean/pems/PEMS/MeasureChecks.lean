import PEMS.MeasureDefinitions
import ThesisCommon.LpCut

/-! Representation checks for the localization definitions. These verify the
meaning of the objects in the targets; they do not prove the paper's theorems. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- The expanded supremum really is the norm of the bounded cutoff operator. -/
theorem cutOperatorNorm_eq (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (A : Set Y) (hA : MeasurableSet A) :
    cutOperatorNorm T A = ‖(lpCutL A hA).comp T‖ := by
  rw [cutOperatorNorm, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image, Metric.mem_closedBall,
    dist_zero_right]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f, hf, ?_⟩
    change ‖lpCut A hA (T f)‖ = _
    rw [lpCut, Lp.norm_toLp]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f, hf, ?_⟩
    change ‖lpCut A hA (T f)‖ = _
    rw [lpCut, Lp.norm_toLp]

theorem cutOperatorNorm_nonneg (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (A : Set Y) (hA : MeasurableSet A) : 0 ≤ cutOperatorNorm T A := by
  rw [cutOperatorNorm_eq T A hA]
  exact norm_nonneg _

theorem cutOperatorNorm_le_norm (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (A : Set Y) (hA : MeasurableSet A) : cutOperatorNorm T A ≤ ‖T‖ := by
  rw [cutOperatorNorm_eq T A hA]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
    (mul_le_mul_of_nonneg_right (norm_lpCutL_le A hA) (norm_nonneg T)).trans_eq (one_mul _)

theorem smallSetSup_bounds (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ smallSetSup T Θ δ ∧ smallSetSup T Θ δ ≤ ‖T‖ := by
  let S := {q : ℝ | ∃ B : Set Y, MeasurableSet B ∧ B ⊆ Θ ∧
    ν B < ENNReal.ofReal δ ∧ q = cutOperatorNorm T (Θᶜ ∪ B)}
  have hempty : cutOperatorNorm T (Θᶜ ∪ ∅) ∈ S :=
    ⟨∅, MeasurableSet.empty, empty_subset _, by simpa using ENNReal.ofReal_pos.mpr hδ, rfl⟩
  have hbound : ∀ q ∈ S, q ≤ ‖T‖ := by
    rintro q ⟨B, hB, _, _, rfl⟩
    exact cutOperatorNorm_le_norm T _ (hΘ.compl.union hB)
  exact ⟨(cutOperatorNorm_nonneg T _ (hΘ.compl.union MeasurableSet.empty)).trans
    (le_csSup ⟨‖T‖, hbound⟩ hempty), csSup_le ⟨_, hempty⟩ hbound⟩

theorem alphaTheta_bounds (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    0 ≤ alphaTheta T Θ ∧ alphaTheta T Θ ≤ ‖T‖ := by
  have hnonempty : {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ δ}.Nonempty :=
    ⟨_, 1, zero_lt_one, rfl⟩
  have hlo : ∀ r ∈ {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ δ}, 0 ≤ r := by
    rintro r ⟨δ, hδ, rfl⟩
    exact (smallSetSup_bounds T Θ hΘ δ hδ).1
  refine ⟨le_csInf hnonempty hlo, ?_⟩
  exact (csInf_le ⟨0, hlo⟩ (show smallSetSup T Θ 1 ∈
    {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ δ} from ⟨1, zero_lt_one, rfl⟩)).trans
    (smallSetSup_bounds T Θ hΘ 1 zero_lt_one).2

theorem localizedWeakNoncompactness_bounds (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    0 ≤ localizedWeakNoncompactness T ∧ localizedWeakNoncompactness T ≤ ‖T‖ := by
  have hempty : alphaTheta T ∅ ∈ {r : ℝ | ∃ Θ : Set Y,
      MeasurableSet Θ ∧ ν Θ < ⊤ ∧ r = alphaTheta T Θ} :=
    ⟨∅, MeasurableSet.empty, by simp, rfl⟩
  have hlo : ∀ r ∈ {r : ℝ | ∃ Θ : Set Y,
      MeasurableSet Θ ∧ ν Θ < ⊤ ∧ r = alphaTheta T Θ}, 0 ≤ r := by
    rintro r ⟨Θ, hΘ, _, rfl⟩
    exact (alphaTheta_bounds T Θ hΘ).1
  exact ⟨le_csInf ⟨_, hempty⟩ hlo,
    (csInf_le ⟨0, hlo⟩ hempty).trans (alphaTheta_bounds T ∅ MeasurableSet.empty).2⟩

end PEMS
