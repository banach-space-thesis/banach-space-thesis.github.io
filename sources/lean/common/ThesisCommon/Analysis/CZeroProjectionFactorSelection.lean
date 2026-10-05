import ThesisCommon.Analysis.CZeroCoordinateFactorization
import ThesisCommon.Analysis.LpProjectionFactorSelection

/-! Primary c₀ model fibres give uniformly controlled projection factors
on a full-cardinality common branch. -/
noncomputable section
open scoped Cardinal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem norm_cZeroCoordinateEntry_le
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (α β : Γ) :
    ‖cZeroCoordinateEntry T β α‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (BoundedContinuousFunction.norm_coe_le_norm (T (cZeroSingleAt α x)).toBCF β).trans
    ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_cZeroSingleAt_le α x) (norm_nonneg T)))
theorem cZero_primary_coordinate_factor_selection 
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : IsPrimary 𝕜 X)
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X))
    (hproj : ∀ γ, (cZeroCoordinateEntry T γ γ).comp (cZeroCoordinateEntry T γ γ) =
      cZeroCoordinateEntry T γ γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp T).comp
        (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0) :
    ∃ C : ℝ, 1 ≤ C ∧ (FactorsIdentityWith T (C₀(Γ, X)) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T) (C₀(Γ, X)) C) := by
  obtain ⟨C, hC, hchoose⟩ := full_cardinal_bounded_factor_branch hΓ hcof Λ hΛ
    (fun γ => cZeroCoordinateEntry T γ γ)
    (fun γ _ => hX.projection_factor_dichotomy _ (hproj γ))
  exact ⟨C, hC, cZero_factor_dichotomy_of_selected_coordinates T Λ hdiag
    (zero_le_one.trans hC) hchoose⟩

theorem cZero_uniform_primary_coordinate_factor_selection 
    (hΓ : Cardinal.aleph0 ≤ Cardinal.mk Γ)
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X))
    (hproj : ∀ γ, (cZeroCoordinateEntry T γ γ).comp (cZeroCoordinateEntry T γ γ) =
      cZeroCoordinateEntry T γ γ)
    (Λ : Set Γ) (hΛ : Cardinal.mk Λ = Cardinal.mk Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp T).comp
        (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0)
    (C : ℝ → ℝ) (hmono : MonotoneOn C (Set.Ici 1)) (hC : ∀ t, 1 ≤ t → 1 ≤ C t)
    (hprimary : ∀ Q : X →L[𝕜] X, Q.comp Q = Q →
      IsomorphicWithBound 𝕜 X (LinearMap.range Q.toLinearMap) (C (max 1 ‖Q‖)) ∨
      IsomorphicWithBound 𝕜 X (LinearMap.range (ContinuousLinearMap.id 𝕜 X - Q).toLinearMap)
        (C (max 1 ‖Q‖))) {t : ℝ} (ht : 1 ≤ t) (hTt : ‖T‖ ≤ t) :
    FactorsIdentityWith T (C₀(Γ, X)) (C t * (1 + t)) ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - T) (C₀(Γ, X))
        (C t * (1 + t)) := by
  have hCt : 0 ≤ C t := zero_le_one.trans (hC t ht)
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  apply cZero_factor_dichotomy_of_selected_coordinates T Λ hdiag (mul_nonneg hCt (by linarith))
  apply full_cardinal_factor_branch hΓ Λ hΛ (fun γ => cZeroCoordinateEntry T γ γ)
  intro γ _
  let Q := cZeroCoordinateEntry T γ γ
  have hQ : ‖Q‖ ≤ t := (norm_cZeroCoordinateEntry_le T γ γ).trans hTt
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

