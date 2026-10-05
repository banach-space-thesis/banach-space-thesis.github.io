import ThesisCommon.WeakCalkin

/-! Norm and operator-ideal properties of the distance to weakly compact operators.
These statements do not require completeness. -/

noncomputable section
set_option synthInstance.maxSize 1024

namespace ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The infimum in the definition is the usual distance to the operator ideal. -/
theorem weakEssentialNorm_eq_infDist (T : E →L[𝕜] F) :
    weakEssentialNorm T =
      Metric.infDist T (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F)) := by
  apply le_antisymm
  · apply (Metric.le_infDist ⟨0, weaklyCompact_zero⟩).2
    intro W hW
    simpa only [dist_eq_norm] using weakEssentialNorm_le T hW
  · apply le_csInf
    · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
    · rintro r ⟨W, hW, rfl⟩
      simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem
        (x := T) (s := (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F))) hW

/-- The weak essential norm is exactly the existing quotient seminorm. -/
theorem weakEssentialNorm_eq_quotient_norm (T : E →L[𝕜] F) :
    weakEssentialNorm T =
      ‖(Submodule.Quotient.mk T : (E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F)‖ := by
  rw [weakEssentialNorm_eq_infDist]
  exact (QuotientAddGroup.norm_mk (S := (weaklyCompactSubmodule 𝕜 E F).toAddSubgroup) T).symm

/-- Weakly compact approximants attain the distance to within every positive error. -/
theorem exists_weaklyCompact_norm_sub_lt (T : E →L[𝕜] F) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : E →L[𝕜] F, IsWeaklyCompactOperator W ∧
      ‖T - W‖ < weakEssentialNorm T + ε := by
  have h := (Metric.infDist_lt_iff
    (s := (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F))) ⟨0, weaklyCompact_zero⟩).1
    (show Metric.infDist T (weaklyCompactSubmodule 𝕜 E F : Set (E →L[𝕜] F)) <
      weakEssentialNorm T + ε by rw [← weakEssentialNorm_eq_infDist]; linarith)
  simpa only [dist_eq_norm] using h

@[simp] theorem weakEssentialNorm_zero :
    weakEssentialNorm (0 : E →L[𝕜] F) = 0 :=
  weaklyCompact_zero.weakEssentialNorm_eq_zero

theorem weakEssentialNorm_add_le (S T : E →L[𝕜] F) :
    weakEssentialNorm (S + T) ≤ weakEssentialNorm S + weakEssentialNorm T := by
  simp only [weakEssentialNorm_eq_quotient_norm, Submodule.Quotient.mk_add]
  exact norm_add_le
    (Submodule.Quotient.mk S : (E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F)
    (Submodule.Quotient.mk T)

@[simp] theorem weakEssentialNorm_smul (a : 𝕜) (T : E →L[𝕜] F) :
    weakEssentialNorm (a • T) = ‖a‖ * weakEssentialNorm T := by
  letI : NormSMulClass 𝕜 ((E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F) :=
    NormedSpace.toNormSMulClass (𝕜 := 𝕜)
      (E := (E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F)
  simp only [weakEssentialNorm_eq_quotient_norm, Submodule.Quotient.mk_smul]
  exact norm_smul a
    (Submodule.Quotient.mk T : (E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F)

@[simp] theorem weakEssentialNorm_neg (T : E →L[𝕜] F) :
    weakEssentialNorm (-T) = weakEssentialNorm T := by
  simp only [weakEssentialNorm_eq_quotient_norm, Submodule.Quotient.mk_neg]
  exact norm_neg
    (Submodule.Quotient.mk T : (E →L[𝕜] F) ⧸ weaklyCompactSubmodule 𝕜 E F)

theorem weakEssentialNorm_sub_le (S T : E →L[𝕜] F) :
    weakEssentialNorm (S - T) ≤ weakEssentialNorm S + weakEssentialNorm T := by
  simpa only [sub_eq_add_neg, weakEssentialNorm_neg] using weakEssentialNorm_add_le S (-T)

/-- Changing a representative by a weakly compact operator preserves its distance. -/
theorem weakEssentialNorm_eq_of_sub_weaklyCompact {S T : E →L[𝕜] F}
    (h : IsWeaklyCompactOperator (S - T)) : weakEssentialNorm S = weakEssentialNorm T := by
  rw [weakEssentialNorm_eq_quotient_norm, weakEssentialNorm_eq_quotient_norm]
  exact congrArg norm ((Submodule.Quotient.eq (weaklyCompactSubmodule 𝕜 E F)).2 h)

theorem weakEssentialNorm_add_weaklyCompact (T : E →L[𝕜] F) {W : E →L[𝕜] F}
    (hW : IsWeaklyCompactOperator W) : weakEssentialNorm (T + W) = weakEssentialNorm T := by
  apply weakEssentialNorm_eq_of_sub_weaklyCompact
  simpa only [add_sub_cancel_left] using hW

theorem weakEssentialNorm_sub_weaklyCompact (T : E →L[𝕜] F) {W : E →L[𝕜] F}
    (hW : IsWeaklyCompactOperator W) : weakEssentialNorm (T - W) = weakEssentialNorm T := by
  apply weakEssentialNorm_eq_of_sub_weaklyCompact
  have hneg : IsWeaklyCompactOperator (-W) := (weaklyCompactSubmodule 𝕜 E F).neg_mem hW
  simpa only [sub_sub_cancel_left] using hneg

/-- A nonnegative scalar can be taken through the defining distance infimum. -/
theorem le_mul_weakEssentialNorm {a c : ℝ} (hc : 0 ≤ c) (T : E →L[𝕜] F)
    (h : ∀ W : E →L[𝕜] F, IsWeaklyCompactOperator W → a ≤ c * ‖T - W‖) :
    a ≤ c * weakEssentialNorm T := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [zero_mul] using h 0 weaklyCompact_zero
  · rw [mul_comm, ← div_le_iff₀ hc]
    apply le_csInf
    · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
    · rintro r ⟨W, hW, rfl⟩
      exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using h W hW)

/-- Left composition is bounded by the ordinary norm of the left factor. -/
theorem weakEssentialNorm_comp_left_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    weakEssentialNorm (S.comp T) ≤ ‖S‖ * weakEssentialNorm T := by
  apply le_mul_weakEssentialNorm (norm_nonneg S) T
  intro W hW
  calc
    weakEssentialNorm (S.comp T) ≤ ‖S.comp T - S.comp W‖ :=
      weakEssentialNorm_le _ (hW.comp_left S)
    _ = ‖S.comp (T - W)‖ := by rw [ContinuousLinearMap.comp_sub]
    _ ≤ ‖S‖ * ‖T - W‖ := ContinuousLinearMap.opNorm_comp_le _ _

/-- Right composition is bounded by the ordinary norm of the right factor. -/
theorem weakEssentialNorm_comp_right_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    weakEssentialNorm (S.comp T) ≤ weakEssentialNorm S * ‖T‖ := by
  rw [mul_comm]
  apply le_mul_weakEssentialNorm (norm_nonneg T) S
  intro W hW
  calc
    weakEssentialNorm (S.comp T) ≤ ‖S.comp T - W.comp T‖ :=
      weakEssentialNorm_le _ (hW.comp_right T)
    _ = ‖(S - W).comp T‖ := by rw [ContinuousLinearMap.sub_comp]
    _ ≤ ‖S - W‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖T‖ * ‖S - W‖ := mul_comm _ _

/-- The weak essential norm is submultiplicative for composition. -/
theorem weakEssentialNorm_comp_le (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    weakEssentialNorm (S.comp T) ≤ weakEssentialNorm S * weakEssentialNorm T := by
  rw [mul_comm]
  apply le_mul_weakEssentialNorm (weakEssentialNorm_nonneg T) S
  intro W hW
  calc
    weakEssentialNorm (S.comp T) = weakEssentialNorm ((S - W).comp T) := by
      rw [ContinuousLinearMap.sub_comp, weakEssentialNorm_sub_weaklyCompact _ (hW.comp_right T)]
    _ ≤ ‖S - W‖ * weakEssentialNorm T := weakEssentialNorm_comp_left_le _ _
    _ = weakEssentialNorm T * ‖S - W‖ := mul_comm _ _

/-- In particular the distance is a continuous, indeed one-Lipschitz, function. -/
theorem weakEssentialNorm_lipschitz :
    LipschitzWith 1 (weakEssentialNorm : (E →L[𝕜] F) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro S T
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := (weakEssentialNorm_add_le S (T - S)).trans
      (add_le_add_left (weakEssentialNorm_le_norm (T - S)) _)
    rw [add_sub_cancel, norm_sub_rev] at h
    linarith
  · have h := (weakEssentialNorm_add_le T (S - T)).trans
      (add_le_add_left (weakEssentialNorm_le_norm (S - T)) _)
    rw [add_sub_cancel] at h
    linarith

theorem continuous_weakEssentialNorm :
    Continuous (weakEssentialNorm : (E →L[𝕜] F) → ℝ) :=
  weakEssentialNorm_lipschitz.continuous

end ThesisCommon
