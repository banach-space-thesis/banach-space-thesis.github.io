import ThesisCommon.Analysis.UniformPrimariness
import Mathlib.Data.ENNReal.Real

/-! The multiplicative Banach–Mazur infimum over actual bounded linear
equivalences. Its value is infinity when there is no equivalence. We retain
the literal product of operator norms, which is zero for two zero spaces.
No endpoint attainment is built into the definition or any theorem below.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The extended nonnegative infimum of actual equivalence distortions.
The argument of `ofReal` is nonnegative, so no truncation changes it. -/
def banachMazurDistance : ℝ≥0∞ :=
  ⨅ e : X ≃L[𝕜] Y,
    ENNReal.ofReal (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖)

theorem banachMazurDistance_le_distortion (e : X ≃L[𝕜] Y) :
    banachMazurDistance 𝕜 X Y ≤
      ENNReal.ofReal (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) :=
  iInf_le _ e

/-- An attained bound always bounds the infimum, including at the endpoint. -/
theorem IsomorphicWithBound.banachMazurDistance_le {C : ℝ}
    (h : IsomorphicWithBound 𝕜 X Y C) :
    banachMazurDistance 𝕜 X Y ≤ ENNReal.ofReal C := by
  obtain ⟨e, he⟩ := h
  exact (banachMazurDistance_le_distortion 𝕜 X Y e).trans
    (ENNReal.ofReal_le_ofReal he)

/-- A strict upper bound on the infimum has a strict actual witness.
The strict inequality is essential; this asserts no endpoint attainment. -/
theorem banachMazurDistance_lt_iff {C : ℝ} :
    banachMazurDistance 𝕜 X Y < ENNReal.ofReal C ↔
      ∃ e : X ≃L[𝕜] Y,
        ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ < C := by
  unfold banachMazurDistance
  rw [iInf_lt_iff]
  exact exists_congr fun e => ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem isomorphicWithBound_of_banachMazurDistance_lt {C : ℝ}
    (h : banachMazurDistance 𝕜 X Y < ENNReal.ofReal C) :
    IsomorphicWithBound 𝕜 X Y C := by
  obtain ⟨e, he⟩ := (banachMazurDistance_lt_iff 𝕜 X Y).mp h
  exact ⟨e, he.le⟩

/-- The infimum is infinite exactly when the spaces are not isomorphic. -/
theorem banachMazurDistance_eq_top_iff :
    banachMazurDistance 𝕜 X Y = ∞ ↔ ¬ Nonempty (X ≃L[𝕜] Y) := by
  unfold banachMazurDistance
  rw [iInf_eq_top]
  constructor
  · intro h ⟨e⟩
    exact ENNReal.ofReal_ne_top (h e)
  · intro h e
    exact (h ⟨e⟩).elim

/-- Literal source convention: the distance between zero spaces is zero. -/
theorem banachMazurDistance_eq_zero_of_subsingleton
    [Subsingleton X] [Subsingleton Y] : banachMazurDistance 𝕜 X Y = 0 := by
  let e : X ≃L[𝕜] Y :=
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := by intros; simp
      map_smul' := by intros; simp
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  apply le_antisymm _ (zero_le _)
  simpa only [ContinuousLinearMap.opNorm_subsingleton, zero_mul, ENNReal.ofReal_zero]
    using banachMazurDistance_le_distortion 𝕜 X Y e

end ThesisCommon
