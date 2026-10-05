import ThesisCommon.Analysis.FilterConvergenceSpace

/-! The actual coordinate decomposition of a filter-null space into the
subspaces supported on a set and its complement, with the product maximum
norm. No infinitude, proper-filter, or nonzero-space hypothesis is needed. -/
noncomputable section
open Set
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type*} (F : Filter Γ) (A : Set Γ)

theorem filterCoordinateProjection_add_compl (x : FilterNullSpace 𝕜 F) :
    filterCoordinateProjection F A x + filterCoordinateProjection F Aᶜ x = x := by
  apply FilterNullSpace.ext
  intro γ
  by_cases h : γ ∈ A <;> simp [h]

theorem filterCoordinateProjection_norm_apply_le (x : FilterNullSpace 𝕜 F) :
    ‖filterCoordinateProjection F A x‖ ≤ ‖x‖ := by
  apply FilterNullSpace.norm_le (norm_nonneg x)
  intro γ
  by_cases h : γ ∈ A
  · simpa only [filterCoordinateProjection_apply, if_pos h] using x.norm_apply_le γ
  · simp only [filterCoordinateProjection_apply, if_neg h, norm_zero]
    exact norm_nonneg x

theorem filterProjectionTo_of_supported (x : FilterSupportedSpace (𝕜 := 𝕜) F A) :
    filterProjectionTo F A x.val = x := by
  apply Subtype.ext
  apply FilterNullSpace.ext
  intro γ
  by_cases h : γ ∈ A
  · simp [h]
  · simp [h, x.property γ h]

theorem filterProjectionTo_of_compl
    (x : FilterSupportedSpace (𝕜 := 𝕜) F Aᶜ) :
    filterProjectionTo F A x.val = 0 := by
  apply Subtype.ext
  apply FilterNullSpace.ext
  intro γ
  by_cases h : γ ∈ A
  · simp [h, x.property γ (by simpa using h)]
  · simp [h]

theorem filterCoordinateSplit_norm (x : FilterNullSpace 𝕜 F) :
    ‖(filterProjectionTo F A x, filterProjectionTo F Aᶜ x)‖ = ‖x‖ := by
  rw [Prod.norm_def]
  apply le_antisymm
  · exact max_le (filterCoordinateProjection_norm_apply_le F A x)
      (filterCoordinateProjection_norm_apply_le F Aᶜ x)
  · apply FilterNullSpace.norm_le (le_trans (norm_nonneg _) (le_max_left _ _))
    intro γ
    by_cases h : γ ∈ A
    · have hγ : ‖x γ‖ ≤ ‖filterProjectionTo F A x‖ := by
        simpa only [filterCoordinateProjection_apply, if_pos h] using
          (filterCoordinateProjection F A x).norm_apply_le γ
      exact hγ.trans (le_max_left _ _)
    · have hγ : ‖x γ‖ ≤ ‖filterProjectionTo F Aᶜ x‖ := by
        simpa only [filterCoordinateProjection_apply, Set.mem_compl_iff, if_pos h] using
          (filterCoordinateProjection F Aᶜ x).norm_apply_le γ
      exact hγ.trans (le_max_right _ _)

set_option maxHeartbeats 800000 in
/-- Restriction to complementary coordinate sets is a surjective linear
isometry for the maximum product norm; its inverse adds the two inclusions. -/
def filterCoordinateSplitEquiv :
    FilterNullSpace 𝕜 F ≃ₗᵢ[𝕜]
      (FilterSupportedSpace (𝕜 := 𝕜) F A × FilterSupportedSpace (𝕜 := 𝕜) F Aᶜ) where
  toFun x := (filterProjectionTo F A x, filterProjectionTo F Aᶜ x)
  invFun y := y.1.val + y.2.val
  left_inv x := filterCoordinateProjection_add_compl F A x
  right_inv y := by
    apply Prod.ext
    · change filterProjectionTo F A (y.1.val + y.2.val) = y.1
      rw [map_add, filterProjectionTo_of_supported, filterProjectionTo_of_compl, add_zero]
    · change filterProjectionTo F Aᶜ (y.1.val + y.2.val) = y.2
      rw [map_add, filterProjectionTo_of_supported]
      have h : filterProjectionTo F Aᶜ y.1.val = 0 := by
        apply Subtype.ext
        apply FilterNullSpace.ext
        intro γ
        by_cases hγ : γ ∈ A
        · simp [hγ]
        · simp [hγ, y.1.property γ hγ]
      rw [h, zero_add]
  map_add' x y := Prod.ext (map_add _ x y) (map_add _ x y)
  map_smul' c x := Prod.ext (map_smul _ c x) (map_smul _ c x)
  norm_map' := filterCoordinateSplit_norm F A

@[simp] theorem filterCoordinateSplitEquiv_fst (x : FilterNullSpace 𝕜 F) :
    (filterCoordinateSplitEquiv (𝕜 := 𝕜) F A x).1 = filterProjectionTo F A x := rfl

@[simp] theorem filterCoordinateSplitEquiv_snd (x : FilterNullSpace 𝕜 F) :
    (filterCoordinateSplitEquiv (𝕜 := 𝕜) F A x).2 = filterProjectionTo F Aᶜ x := rfl

@[simp] theorem filterCoordinateSplitEquiv_symm_apply
    (y : FilterSupportedSpace (𝕜 := 𝕜) F A × FilterSupportedSpace (𝕜 := 𝕜) F Aᶜ) :
    (filterCoordinateSplitEquiv (𝕜 := 𝕜) F A).symm y = y.1.val + y.2.val := rfl

@[simp] theorem filterCoordinateSplitEquiv_symm_apply_apply
    (y : FilterSupportedSpace (𝕜 := 𝕜) F A × FilterSupportedSpace (𝕜 := 𝕜) F Aᶜ)
    (γ : Γ) : (filterCoordinateSplitEquiv (𝕜 := 𝕜) F A).symm y γ =
      y.1.val γ + y.2.val γ := rfl

end ThesisCommon
