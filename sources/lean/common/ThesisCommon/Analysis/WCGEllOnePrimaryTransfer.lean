import ThesisCommon.Analysis.WCGEllOnePrimaryCoordinates
import ThesisCommon.Analysis.LpProjectionFactorSelection
import ThesisCommon.Analysis.QuantitativeProjectionDecomposition
import ThesisCommon.Analysis.PrimaryIsometry

/-! The WCG ℓ1 primariness transfer. The control function is fixed before
the projection is chosen and is evaluated at max(1,norm P), including P=0.
The qualitative branch needs uncountable cofinality only when making the
coordinate factorization bounds uniform on a full-cardinality subset. -/
noncomputable section
open scoped ENNReal Cardinal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem operatorTransport_complement (E : X ≃ₗᵢ[𝕜] X) (P : X →L[𝕜] X) :
    operatorTransport E E (ContinuousLinearMap.id 𝕜 X - P) =
      ContinuousLinearMap.id 𝕜 X - operatorTransport E E P := by
  ext x
  simp only [operatorTransport_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub, LinearIsometryEquiv.apply_symm_apply]

theorem IsWeaklyCompactlyGenerated.iterated_ellOne_isUniformlyPrimary
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hprimary : IsUniformlyPrimary 𝕜 (lp (fun _ : ℕ => X) 1)) :
    IsUniformlyPrimary 𝕜 (lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1) := by
  classical
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  obtain ⟨C, hmono, hC, hprimary⟩ := hprimary
  let D (t : ℝ) := projectionFactorDecompositionBound (1 + t) (C t * (1 + t))
  have hDmono : MonotoneOn D (Set.Ici 1) := by
    intro s hs t ht hst
    change (1 : ℝ) ≤ s at hs
    change (1 : ℝ) ≤ t at ht
    apply projectionFactorDecompositionBound_mono
      (by linarith : 0 ≤ 1 + s)
      (mul_nonneg (zero_le_one.trans (hC s hs)) (by linarith)) (by linarith)
    exact mul_le_mul (hmono hs ht hst) (by linarith)
      (by linarith) (zero_le_one.trans (hC t ht))
  refine ⟨D, hDmono, fun t ht => one_le_projectionFactorDecompositionBound
    (by linarith) (mul_nonneg (zero_le_one.trans (hC t ht)) (by linarith)), ?_⟩
  intro P hP
  obtain ⟨E, hentry, Λ, hΛ, hdiag⟩ := hX.iterated_ellOne_primary_coordinates hΓ P hP
  let t := max 1 ‖P‖
  have ht : 1 ≤ t := le_max_left _ _
  have hPt : ‖P‖ ≤ t := le_max_right _ _
  have hCt : 0 ≤ C t := zero_le_one.trans (hC t ht)
  have hK : 0 ≤ C t * (1 + t) := mul_nonneg hCt (by linarith)
  have hf := lp_uniform_primary_coordinate_factor_selection 1 (by norm_num)
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le) (operatorTransport E E P)
    hentry Λ hΛ hdiag C hmono hC hprimary ht (by rwa [norm_operatorTransport])
  let eS := lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜)
    (X := lp (fun _ : ℕ => X) 1) (Γ := Γ) 1 (by norm_num)
  rcases hf with hf | hf
  · exact Or.inl ((hf.of_operatorTransport_self E hK).projection_range_isomorphic_of_lp_isometry
      1 eS hP (by linarith : 0 ≤ 1 + t) hK (hPt.trans (by linarith)))
  · rw [← operatorTransport_complement E P] at hf
    have hPc : ‖ContinuousLinearMap.id 𝕜 _ - P‖ ≤ 1 + t :=
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hPt)
    exact Or.inr ((hf.of_operatorTransport_self E hK).projection_range_isomorphic_of_lp_isometry
      1 eS (complementary_projection hP) (by linarith : 0 ≤ 1 + t) hK hPc)

theorem IsWeaklyCompactlyGenerated.iterated_ellOne_isPrimary_of_uncountable_cofinality
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (hprimary : IsPrimary 𝕜 (lp (fun _ : ℕ => X) 1)) :
    IsPrimary 𝕜 (lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1) := by
  classical
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  intro P hP
  obtain ⟨E, hentry, Λ, hΛ, hdiag⟩ := hX.iterated_ellOne_primary_coordinates hΓ P hP
  obtain ⟨K, hK, hf⟩ := lp_primary_coordinate_factor_selection 1 (by norm_num)
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le) hcof hprimary
    (operatorTransport E E P) hentry Λ hΛ hdiag
  let eS := lpArbitrarySequenceSelfIsometry (𝕜 := 𝕜)
    (X := lp (fun _ : ℕ => X) 1) (Γ := Γ) 1 (by norm_num)
  rcases hf with hf | hf
  · obtain ⟨e, _⟩ := (hf.of_operatorTransport_self E (zero_le_one.trans hK)).projection_range_isomorphic_of_lp_isometry
      1 eS hP (norm_nonneg P) (zero_le_one.trans hK) le_rfl
    exact Or.inl ⟨e⟩
  · rw [← operatorTransport_complement E P] at hf
    obtain ⟨e, _⟩ := (hf.of_operatorTransport_self E (zero_le_one.trans hK)).projection_range_isomorphic_of_lp_isometry
      1 eS (complementary_projection hP) (norm_nonneg _) (zero_le_one.trans hK) le_rfl
    exact Or.inr ⟨e⟩

theorem IsWeaklyCompactlyGenerated.ellOne_isUniformlyPrimary_of_countable_model
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hprimary : IsUniformlyPrimary 𝕜 (lp (fun _ : ℕ => X) 1)) :
    IsUniformlyPrimary 𝕜 (lp (fun _ : Γ => X) 1) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  exact (hX.iterated_ellOne_isUniformlyPrimary hΓ hprimary).of_isometry
    (lpArbitraryAbsorbCountableIsometry 1 (by norm_num))

theorem IsWeaklyCompactlyGenerated.ellOne_isPrimary_of_countable_model
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof)
    (hprimary : IsPrimary 𝕜 (lp (fun _ : ℕ => X) 1)) :
    IsPrimary 𝕜 (lp (fun _ : Γ => X) 1) := by
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
  exact (hX.iterated_ellOne_isPrimary_of_uncountable_cofinality hΓ hcof hprimary).of_equiv
    (lpArbitraryAbsorbCountableIsometry 1 (by norm_num)).toContinuousLinearEquiv

end ThesisCommon
