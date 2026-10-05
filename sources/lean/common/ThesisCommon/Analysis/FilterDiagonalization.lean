import ThesisCommon.Analysis.FilterCoordinateCopy
import ThesisCommon.Analysis.FilterFactorization
import ThesisCommon.Analysis.FilterFunctionalResidual
import ThesisCommon.Analysis.FilterRosenthal

/-! Actual diagonalisation from large-set self-similarity. Hahn-Banach row
extensions give bounded charges; full-cardinality Rosenthal selection makes
their residual variations small. The tolerance is halved before taking the
coordinate supremum, preserving the strict operator-norm conclusion. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 Γ : Type*} [RCLike 𝕜] (F : Filter Γ)

theorem filterCoordinateCopyEquiv_symm_apply (C : Set Γ) (θ : Γ ≃ C)
    (h : IsFilterCoordinateCopy F C θ)
    (y : FilterSupportedSpace (𝕜 := 𝕜) F C) (γ : Γ) :
    (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h).symm y γ = y.val (θ γ).val := by
  let e := filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h
  have hh := filterCoordinateCopyEquiv_apply_image F C θ h (e.symm y) γ
  change (e (e.symm y)).val (θ γ).val = e.symm y γ at hh
  rw [e.apply_symm_apply] at hh
  exact hh.symm

theorem filterCoordinateCopy_compression_apply (C : Set Γ) (θ : Γ ≃ C)
    (h : IsFilterCoordinateCopy F C θ)
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F)
    (x : FilterNullSpace 𝕜 F) (γ : Γ) :
    filterCompression (𝕜 := 𝕜) F C
      (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h).toContinuousLinearEquiv T x γ =
      T (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h x).val (θ γ).val := by
  simp only [filterCompression, ContinuousLinearMap.comp_apply]
  change (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h).symm
    (filterProjectionTo (𝕜 := 𝕜) F C
      (T (filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h x).val)) γ = _
  rw [filterCoordinateCopyEquiv_symm_apply]
  change (if (θ γ).val ∈ C then _ else 0) = _
  rw [if_pos (θ γ).property]

theorem norm_filterCoordinateAtom_le
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (α : Γ) :
    ‖functionalCharge (filterCoordinateExtension F T α) {α}‖ ≤ ‖T‖ := by
  change ‖filterCoordinateExtension F T α (infinityIndicator {α})‖ ≤ ‖T‖
  calc
    _ ≤ ‖filterCoordinateExtension F T α‖ * ‖infinityIndicator (𝕜 := 𝕜) {α}‖ :=
      (filterCoordinateExtension F T α).le_opNorm _
    _ ≤ ‖filterCoordinateExtension F T α‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_infinityIndicator_le _) (norm_nonneg _)
    _ ≤ ‖T‖ := by simpa only [mul_one] using norm_filterCoordinateExtension_le F T α

def filterCopyDiagonal
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F) (C : Set Γ) (θ : Γ ≃ C) :
    lp (fun _ : Γ => 𝕜) ∞ :=
  ⟨fun γ => functionalCharge (filterCoordinateExtension F T (θ γ).val) {(θ γ).val},
    memℓp_infty ⟨‖T‖, by
      rintro _ ⟨γ, rfl⟩
      exact norm_filterCoordinateAtom_le F T (θ γ).val⟩⟩

@[simp] theorem filterCopyDiagonal_apply
    (T : FilterNullSpace 𝕜 F →L[𝕜] FilterNullSpace 𝕜 F)
    (C : Set Γ) (θ : Γ ≃ C) (γ : Γ) :
    filterCopyDiagonal F T C θ γ =
      functionalCharge (filterCoordinateExtension F T (θ γ).val) {(θ γ).val} := rfl

theorem filterCoordinateCopy_distortion_le (C : Set Γ) (θ : Γ ≃ C)
    (h : IsFilterCoordinateCopy F C θ) :
    ‖(filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h).toContinuousLinearEquiv.toContinuousLinearMap‖ *
      ‖(filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h).toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
  let e := filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ h
  have h1 : ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using (e.norm_map x).le
  have h2 : ‖e.toContinuousLinearEquiv.symm.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using (e.symm.norm_map x).le
  simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one

theorem IsLargeSetSelfSimilarFilter.diagonalisable [Infinite Γ]
    (hF : IsLargeSetSelfSimilarFilter F) : IsFilterDiagonalisable (𝕜 := 𝕜) F 1 := by
  refine ⟨le_rfl, ?_⟩
  intro T η hη
  obtain ⟨A, hA, hsmall⟩ := rosenthal_charge_selection
    (fun α => functionalCharge (filterCoordinateResidual F T α))
    (filterCoordinateResidual_uniformlyBounded F T)
    (filterCoordinateResidual_diagonal_zero F T) (η / 2) (half_pos hη)
  obtain ⟨C, hCA, θ, hθ⟩ := hF A hA
  let e := filterCoordinateCopyEquiv (𝕜 := 𝕜) F C θ hθ
  let a := filterCopyDiagonal F T C θ
  refine ⟨C, e.toContinuousLinearEquiv,
    filterCoordinateCopy_distortion_le F C θ hθ, a, ?_⟩
  have hnorm : ‖filterCompression F C e.toContinuousLinearEquiv T -
      filterMultiplier F a‖ ≤ η / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hη).le
    intro x
    apply FilterNullSpace.norm_le (mul_nonneg (half_pos hη).le (norm_nonneg x))
    intro γ
    change ‖filterCompression F C e.toContinuousLinearEquiv T x γ -
      filterMultiplier F a x γ‖ ≤ (η / 2) * ‖x‖
    rw [filterCoordinateCopy_compression_apply, filterMultiplier_apply]
    have hb := filterCoordinateResidual_support_bound F T (θ γ).val (e x).val
      (A := A) (fun β hβ => (e x).property β (fun hC => hβ (hCA hC)))
    have he : ‖(e x).val‖ = ‖x‖ := e.norm_map x
    have hi : (e x).val (θ γ).val = x γ :=
      filterCoordinateCopyEquiv_apply_image F C θ hθ x γ
    change ‖T (e x).val (θ γ).val -
      functionalCharge (filterCoordinateExtension F T (θ γ).val) {(θ γ).val} * x γ‖ ≤ _
    rw [hi, he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (hsmall _ (hCA (θ γ).property)).le (norm_nonneg x))
  exact hnorm.trans_lt (half_lt_self hη)

theorem IsLargeSetSelfSimilarFilter.primaryForFactorisation [Infinite Γ]
    (hF : IsLargeSetSelfSimilarFilter F) :
    IsFilterPrimaryForFactorisation (𝕜 := 𝕜) F 1 1 :=
  ⟨hF.primaryUnderSums, hF.diagonalisable F⟩

theorem IsLargeSetSelfSimilarFilter.hasCPlusPFP_two [Infinite Γ]
    (hF : IsLargeSetSelfSimilarFilter F) : HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 F) 2 := by
  simpa using filter_hasCPlusPFP F (hF.primaryForFactorisation F (𝕜 := 𝕜))

end ThesisCommon
