import ThesisCommon.Analysis.CZeroProjectionFactorSelection
import ThesisCommon.Analysis.QuantitativeCZeroProjectionDecomposition
import ThesisCommon.Analysis.CZeroArbitraryProducts
import ThesisCommon.Analysis.PrimaryIsometry
import ThesisCommon.Analysis.WCGEllOnePrimaryTransfer

/-! Common final assembly once actual isometric primary coordinates have
been constructed. The structural premise below is proved independently for
each concrete sum before this assembly is applied. -/
noncomputable section
open scoped Cardinal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]


def HasPrimaryCZeroCoordinates : Prop :=
  ∀ (P : C₀(Γ, X) →L[𝕜] C₀(Γ, X)), P.comp P = P →
    ∃ E : C₀(Γ, X) ≃ₗᵢ[𝕜] C₀(Γ, X),
      (∀ γ, (cZeroCoordinateEntry (operatorTransport E E P) γ γ).comp
        (cZeroCoordinateEntry (operatorTransport E E P) γ γ) =
          cZeroCoordinateEntry (operatorTransport E E P) γ γ) ∧
      ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
          ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp (operatorTransport E E P)).comp
            (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0

theorem HasPrimaryCZeroCoordinates.isUniformlyPrimary
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcoords : HasPrimaryCZeroCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := X))
    (hprimary : IsUniformlyPrimary 𝕜 X) : IsUniformlyPrimary 𝕜 (C₀(Γ, X)) := by
  classical
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ
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
  obtain ⟨E, hentry, Λ, hΛ, hdiag⟩ := hcoords P hP
  let t := max 1 ‖P‖
  have ht : 1 ≤ t := le_max_left _ _
  have hPt : ‖P‖ ≤ t := le_max_right _ _
  have hK : 0 ≤ C t * (1 + t) := mul_nonneg (zero_le_one.trans (hC t ht)) (by linarith)
  have hf := cZero_uniform_primary_coordinate_factor_selection hΓ
    (operatorTransport E E P) hentry Λ hΛ hdiag C hmono hC hprimary ht
    (by rwa [norm_operatorTransport])
  let eS := cZeroArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (X := X) (Γ := Γ)
  rcases hf with hf | hf
  · exact Or.inl ((hf.of_operatorTransport_self E hK).projection_range_isomorphic_of_cZero_isometry
      eS hP (by linarith : 0 ≤ 1 + t) hK (hPt.trans (by linarith)))
  · rw [← operatorTransport_complement E P] at hf
    have hPc : ‖ContinuousLinearMap.id 𝕜 _ - P‖ ≤ 1 + t :=
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hPt)
    exact Or.inr ((hf.of_operatorTransport_self E hK).projection_range_isomorphic_of_cZero_isometry
      eS (complementary_projection hP) (by linarith : 0 ≤ 1 + t) hK hPc)

theorem HasPrimaryCZeroCoordinates.isPrimary
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcoords : HasPrimaryCZeroCoordinates (𝕜 := 𝕜) (Γ := Γ) (X := X))
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hprimary : IsPrimary 𝕜 X) :
    IsPrimary 𝕜 (C₀(Γ, X)) := by
  classical
  letI : Infinite Γ := Cardinal.aleph0_le_mk_iff.mp hΓ
  intro P hP
  obtain ⟨E, hentry, Λ, hΛ, hdiag⟩ := hcoords P hP
  obtain ⟨K, hK, hf⟩ := cZero_primary_coordinate_factor_selection hΓ hcof hprimary
    (operatorTransport E E P) hentry Λ hΛ hdiag
  let eS := cZeroArbitrarySequenceSelfIsometry (𝕜 := 𝕜) (X := X) (Γ := Γ)
  rcases hf with hf | hf
  · obtain ⟨e, _⟩ := (hf.of_operatorTransport_self E (zero_le_one.trans hK)).projection_range_isomorphic_of_cZero_isometry
      eS hP (norm_nonneg P) (zero_le_one.trans hK) le_rfl
    exact Or.inl ⟨e⟩
  · rw [← operatorTransport_complement E P] at hf
    obtain ⟨e, _⟩ := (hf.of_operatorTransport_self E (zero_le_one.trans hK)).projection_range_isomorphic_of_cZero_isometry
      eS (complementary_projection hP) (norm_nonneg _) (zero_le_one.trans hK) le_rfl
    exact Or.inr ⟨e⟩

end ThesisCommon

