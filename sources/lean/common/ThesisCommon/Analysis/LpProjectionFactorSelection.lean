import ThesisCommon.Analysis.WCGEllOneFactorizationTransfer
import ThesisCommon.Analysis.PrimaryProjectionFactors
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Primary model fibres give actual factorizations through a projection
after its diagonal entries have been proved idempotent. The quantitative
estimate respects the control-function argument max(1, norm P). -/
noncomputable section
open scoped ENNReal Cardinal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_lpCoordinateEntry_le (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (α β : Γ) :
    ‖lpCoordinateEntry p T β α‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
    (T (lp.single p α x)) β).trans (by
      simpa only [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using
        T.le_opNorm (lp.single p α x))

theorem FactorsIdentityWith.of_operatorTransport_self
    {T : X →L[𝕜] X} (E : X ≃ₗᵢ[𝕜] X) {C : ℝ} (hC : 0 ≤ C)
    (h : FactorsIdentityWith (operatorTransport E E T) X C) :
    FactorsIdentityWith T X C := by
  have h' : FactorsIdentityWith
      ((E.toLinearIsometry.toContinuousLinearMap.comp T).comp E.symm.toLinearIsometry.toContinuousLinearMap) X C := by
    simpa only [operatorTransport, ContinuousLinearMap.comp_assoc] using h
  apply (h'.of_compression E.toLinearIsometry.toContinuousLinearMap E.symm.toLinearIsometry.toContinuousLinearMap).mono
  have hprod : ‖E.toLinearIsometry.toContinuousLinearMap‖ * ‖E.symm.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul E.toLinearIsometry.norm_toContinuousLinearMap_le
      E.symm.toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _) zero_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hC

theorem lp_primary_coordinate_factor_selection (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : IsPrimary 𝕜 X)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (hproj : ∀ γ, (lpCoordinateEntry p T γ γ).comp (lpCoordinateEntry p T γ γ) =
      lpCoordinateEntry p T γ γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp T).comp
        (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ (FactorsIdentityWith T (lp (fun _ : Γ => X) p) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T) (lp (fun _ : Γ => X) p) C) := by
  obtain ⟨C, hC, hchoose⟩ := full_cardinal_bounded_factor_branch hΓ hcof Λ hΛ
    (fun γ => lpCoordinateEntry p T γ γ)
    (fun γ _ => hX.projection_factor_dichotomy _ (hproj γ))
  exact ⟨C, hC, lp_factor_dichotomy_of_selected_coordinates p hp T Λ hdiag
    (zero_le_one.trans hC) hchoose⟩

theorem lp_uniform_primary_coordinate_factor_selection (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (hproj : ∀ γ, (lpCoordinateEntry p T γ γ).comp (lpCoordinateEntry p T γ γ) =
      lpCoordinateEntry p T γ γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp T).comp
        (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0)
    (C : ℝ → ℝ) (hmono : MonotoneOn C (Set.Ici 1)) (hC : ∀ t, 1 ≤ t → 1 ≤ C t)
    (hprimary : ∀ Q : X →L[𝕜] X, Q.comp Q = Q →
      IsomorphicWithBound 𝕜 X (LinearMap.range Q.toLinearMap) (C (max 1 ‖Q‖)) ∨
      IsomorphicWithBound 𝕜 X (LinearMap.range (ContinuousLinearMap.id 𝕜 X - Q).toLinearMap)
        (C (max 1 ‖Q‖))) {t : ℝ} (ht : 1 ≤ t) (hTt : ‖T‖ ≤ t) :
    FactorsIdentityWith T (lp (fun _ : Γ => X) p) (C t * (1 + t)) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T) (lp (fun _ : Γ => X) p)
        (C t * (1 + t)) := by
  have hCt : 0 ≤ C t := zero_le_one.trans (hC t ht)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  apply lp_factor_dichotomy_of_selected_coordinates p hp T Λ hdiag (mul_nonneg hCt (by linarith))
  apply full_cardinal_factor_branch hΓ Λ hΛ (fun γ => lpCoordinateEntry p T γ γ)
  intro γ _
  let Q := lpCoordinateEntry p T γ γ
  have hQ : ‖Q‖ ≤ t := (norm_lpCoordinateEntry_le p T γ γ).trans hTt
  have hm : C (max 1 ‖Q‖) ≤ C t := hmono
    (by change (1 : ℝ) ≤ max 1 ‖Q‖; exact le_max_left 1 ‖Q‖)
    (show t ∈ Set.Ici (1 : ℝ) from ht) (max_le ht hQ)
  rcases hprimary Q (hproj γ) with h | h
  · exact Or.inl ((h.factorsIdentityWith_projection (hproj γ)).mono
      (mul_le_mul hm (hQ.trans (by linarith)) (norm_nonneg Q) hCt))
  · have hQc : ‖ContinuousLinearMap.id 𝕜 X - Q‖ ≤ 1 + t :=
      (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hQ)
    exact Or.inr ((h.factorsIdentityWith_projection (complementary_projection (hproj γ))).mono
      (mul_le_mul hm hQc (norm_nonneg _) hCt))

end ThesisCommon
