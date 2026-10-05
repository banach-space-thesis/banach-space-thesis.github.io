import ThesisCommon.Analysis.FilterConvergenceCriteria
import ThesisCommon.Analysis.SharpCompressionBound

/-! The abstract primary factorisation criterion for genuine filter-null
spaces. Copying isomorphisms retain their norm products; no contractive
normalisation or nonzero-space assumption is imposed. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜] {Γ : Type*} (F : Filter Γ)

theorem norm_filterProjectionTo_le (A : Set Γ) :
    ‖filterProjectionTo (𝕜 := 𝕜) F A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖filterCoordinateProjection F A x‖ ≤ 1 * ‖x‖
  apply FilterNullSpace.norm_le (by positivity)
  intro γ
  by_cases hγ : γ ∈ A
  · simpa only [filterCoordinateProjection_apply, if_pos hγ, one_mul] using x.norm_apply_le γ
  · simp only [filterCoordinateProjection_apply, if_neg hγ, norm_zero, one_mul]
    exact norm_nonneg x

theorem filterProjectionTo_subtype (A : Set Γ)
    (x : FilterSupportedSpace (𝕜 := 𝕜) F A) : filterProjectionTo (𝕜 := 𝕜) F A x.val = x := by
  apply Subtype.ext
  apply FilterNullSpace.ext
  intro γ
  change (if γ ∈ A then x.val γ else 0) = x.val γ
  by_cases hγ : γ ∈ A
  · simp only [if_pos hγ]
  · rw [if_neg hγ, x.property γ hγ]

theorem filter_reciprocal_bound {a : lp (fun _ : Γ => 𝕜) ∞} {C : Set Γ}
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖) (γ : Γ) :
    ‖if γ ∈ C then (a γ)⁻¹ else 0‖ ≤ (2 : ℝ) := by
  classical
  by_cases hγ : γ ∈ C
  · rw [if_pos hγ, norm_inv, inv_eq_one_div]
    have hp : 0 < ‖a γ‖ := by have := ha γ hγ; linarith
    apply (div_le_iff₀ hp).mpr
    have := ha γ hγ
    linarith
  · simp only [if_neg hγ, norm_zero]
    norm_num

def filterReciprocal (a : lp (fun _ : Γ => 𝕜) ∞) (C : Set Γ)
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖) : lp (fun _ : Γ => 𝕜) ∞ := by
  classical
  exact ⟨fun γ => if γ ∈ C then (a γ)⁻¹ else 0,
    memℓp_infty ⟨2, by rintro _ ⟨γ, rfl⟩; exact filter_reciprocal_bound ha γ⟩⟩

/-- Reciprocal multiplication, extended by zero, with its true supported
range. Its operator norm is at most two on every filter-null space. -/
def filterInverseTo (a : lp (fun _ : Γ => 𝕜) ∞) (C : Set Γ)
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖) :
    FilterNullSpace 𝕜 F →L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F C := by
  classical
  refine (filterMultiplier F (filterReciprocal a C ha)).codRestrict
    (filterSupportedSubmodule (𝕜 := 𝕜) F C) ?_
  intro x γ hγ
  change (if γ ∈ C then (a γ)⁻¹ else 0) * x γ = 0
  simp only [if_neg hγ, zero_mul]

theorem norm_filterInverseTo_le (a : lp (fun _ : Γ => 𝕜) ∞) (C : Set Γ)
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖) : ‖filterInverseTo F a C ha‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖filterMultiplier F (filterReciprocal a C ha) x‖ ≤ 2 * ‖x‖
  apply FilterNullSpace.norm_le (by positivity)
  intro γ
  rw [filterMultiplier_apply, norm_mul]
  exact mul_le_mul (filter_reciprocal_bound ha γ) (x.norm_apply_le γ)
    (norm_nonneg _) (by norm_num)

theorem filterInverseTo_multiplier (a : lp (fun _ : Γ => 𝕜) ∞) (C : Set Γ)
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖)
    (x : FilterSupportedSpace (𝕜 := 𝕜) F C) :
    filterInverseTo F a C ha (filterMultiplier F a x.val) = x := by
  classical
  apply Subtype.ext
  apply FilterNullSpace.ext
  intro γ
  change (if γ ∈ C then (a γ)⁻¹ else 0) * (a γ * x.val γ) = x.val γ
  by_cases hγ : γ ∈ C
  · have hp : 0 < ‖a γ‖ := by have := ha γ hγ; linarith
    rw [if_pos hγ, ← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.mp hp), one_mul]
  · rw [if_neg hγ, zero_mul, x.property γ hγ]

theorem filter_multiplier_factors_of_copying
    (a : lp (fun _ : Γ => 𝕜) ∞) {K : ℝ} {C : Set Γ}
    (hC : IsFilterCopyingSet (𝕜 := 𝕜) F K C)
    (ha : ∀ γ ∈ C, 1 / 2 ≤ ‖a γ‖) :
    FactorsIdentityWith (filterMultiplier F a) (FilterNullSpace 𝕜 F) (2 * K) := by
  obtain ⟨L, hL⟩ := hC.2
  have hlocal : FactorsIdentityWith (filterMultiplier F a)
      (FilterSupportedSpace (𝕜 := 𝕜) F C) 2 := by
    refine ⟨filterInverseTo F a C ha, (filterSupportedSubmodule (𝕜 := 𝕜) F C).subtypeL, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro x
      exact filterInverseTo_multiplier F a C ha x
    · exact (mul_le_mul (norm_filterInverseTo_le F a C ha)
        (Submodule.norm_subtypeL_le (filterSupportedSubmodule (𝕜 := 𝕜) F C))
        (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)
  apply (hlocal.target_equiv L.symm).mono
  have hL' : ‖L.symm.toContinuousLinearMap‖ * ‖L.toContinuousLinearMap‖ ≤ K := by
    simpa only [mul_comm] using hL
  simpa only [ContinuousLinearEquiv.symm_symm] using mul_le_mul_of_nonneg_left hL' (by norm_num : (0 : ℝ) ≤ 2)

theorem filterMultiplier_complement (a : lp (fun _ : Γ => 𝕜) ∞) :
    filterMultiplier F (1 - a) = ContinuousLinearMap.id 𝕜 (FilterNullSpace 𝕜 F) -
      filterMultiplier F a := by
  ext x γ
  change (1 - a γ) * x γ = x γ - a γ * x γ
  ring

theorem filter_multiplier_dichotomy {K : ℝ}
    (hK : IsFilterPrimaryUnderSums (𝕜 := 𝕜) F K)
    (a : lp (fun _ : Γ => 𝕜) ∞) :
    FactorsIdentityWith (filterMultiplier F a) (FilterNullSpace 𝕜 F) (2 * K) ∨
    FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (FilterNullSpace 𝕜 F) -
      filterMultiplier F a) (FilterNullSpace 𝕜 F) (2 * K) := by
  rcases hK.2 {γ | 1 / 2 ≤ ‖a γ‖} with ⟨C, hC, hc⟩ | ⟨C, hC, hc⟩
  · exact Or.inl (filter_multiplier_factors_of_copying F a hc (fun γ hγ => hC hγ))
  · right
    rw [← filterMultiplier_complement]
    apply filter_multiplier_factors_of_copying F (1 - a) hc
    intro γ hγ
    have hsmall : ¬1 / 2 ≤ ‖a γ‖ := hC hγ
    have ht := norm_add_le (a γ) (1 - a γ)
    rw [add_sub_cancel, norm_one] at ht
    change 1 / 2 ≤ ‖1 - a γ‖
    linarith

theorem filter_compression_left_inverse (A : Set Γ)
    (J : FilterNullSpace 𝕜 F ≃L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F A) :
    (J.symm.toContinuousLinearMap.comp (filterProjectionTo (𝕜 := 𝕜) F A)).comp
      ((filterSupportedSubmodule (𝕜 := 𝕜) F A).subtypeL.comp J.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 (FilterNullSpace 𝕜 F) := by
  apply ContinuousLinearMap.ext
  intro x
  change J.symm (filterProjectionTo (𝕜 := 𝕜) F A (J x).val) = x
  rw [filterProjectionTo_subtype, J.symm_apply_apply]

theorem filter_compression_product_bound (A : Set Γ)
    (J : FilterNullSpace 𝕜 F ≃L[𝕜] FilterSupportedSpace (𝕜 := 𝕜) F A) :
    ‖J.symm.toContinuousLinearMap.comp (filterProjectionTo (𝕜 := 𝕜) F A)‖ *
      ‖(filterSupportedSubmodule (𝕜 := 𝕜) F A).subtypeL.comp J.toContinuousLinearMap‖ ≤
        ‖J.toContinuousLinearMap‖ * ‖J.symm.toContinuousLinearMap‖ := by
  have hleft : ‖J.symm.toContinuousLinearMap.comp (filterProjectionTo (𝕜 := 𝕜) F A)‖ ≤
      ‖J.symm.toContinuousLinearMap‖ := by
    calc
      _ ≤ ‖J.symm.toContinuousLinearMap‖ * ‖filterProjectionTo (𝕜 := 𝕜) F A‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J.symm.toContinuousLinearMap‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_filterProjectionTo_le (𝕜 := 𝕜) F A) (norm_nonneg _)
      _ = _ := mul_one _
  have hright : ‖(filterSupportedSubmodule (𝕜 := 𝕜) F A).subtypeL.comp J.toContinuousLinearMap‖ ≤
      ‖J.toContinuousLinearMap‖ := by
    calc
      _ ≤ ‖(filterSupportedSubmodule (𝕜 := 𝕜) F A).subtypeL‖ * ‖J.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖J.toContinuousLinearMap‖ :=
        mul_le_mul_of_nonneg_right
          (Submodule.norm_subtypeL_le (filterSupportedSubmodule (𝕜 := 𝕜) F A)) (norm_nonneg _)
      _ = _ := one_mul _
  exact (mul_le_mul hleft hright (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Theorem 6.5's exact limiting factorisation constant. This theorem even
allows an improper filter or finite index set; the source's hypotheses are
retained on the public paper target. -/
theorem filter_hasCPlusPFP {K D : ℝ}
    (h : IsFilterPrimaryForFactorisation (𝕜 := 𝕜) F K D) :
    HasCPlusPFP 𝕜 (FilterNullSpace 𝕜 F) (2 * K * D) := by
  have hK : 0 < 2 * K := mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one h.1.1)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one h.2.1
  apply hasCPlusPFP_of_bounded_approximate_compressions hK hD
    (fun M => ∃ a : lp (fun _ : Γ => 𝕜) ∞, M = filterMultiplier F a)
  · rintro M ⟨a, rfl⟩
    exact filter_multiplier_dichotomy F h.1 a
  · intro T η hη
    obtain ⟨A, J, hJ, a, he⟩ := h.2.2 T η hη
    refine ⟨J.symm.toContinuousLinearMap.comp (filterProjectionTo (𝕜 := 𝕜) F A),
      (filterSupportedSubmodule (𝕜 := 𝕜) F A).subtypeL.comp J.toContinuousLinearMap,
      filterMultiplier F a, filter_compression_left_inverse F A J,
      (filter_compression_product_bound F A J).trans hJ, ⟨a, rfl⟩, ?_⟩
    simpa only [filterCompression, ContinuousLinearMap.comp_assoc] using he

theorem filter_hasUPFP {K D : ℝ}
    (h : IsFilterPrimaryForFactorisation (𝕜 := 𝕜) F K D) :
    HasUPFP 𝕜 (FilterNullSpace 𝕜 F) := by
  apply (filter_hasCPlusPFP F h).hasUPFP
  have hK : 1 ≤ K := h.1.1
  have hD : 1 ≤ D := h.2.1
  have hKD : 1 ≤ K * D := by nlinarith [mul_le_mul hK hD (by norm_num) (by linarith)]
  nlinarith

end ThesisCommon

