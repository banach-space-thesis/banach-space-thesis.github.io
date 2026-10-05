import ThesisCommon.Analysis.LpCoordinateFactorization
import ThesisCommon.Analysis.CardinalFactorSelection

/-! The full WCG ℓ₁ transfer of PFP and UPFP. Uniform bounds are preserved
exactly. The extra cofinality assumption appears only in the nonuniform case.
-/
noncomputable section
open scoped Cardinal ENNReal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lp_factor_dichotomy_of_selected_coordinates (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp T).comp
        (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hchoose :
      (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith (lpCoordinateEntry p T γ γ) X C) ∨
      (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith
          (ContinuousLinearMap.id 𝕜 X - lpCoordinateEntry p T γ γ) X C)) :
    FactorsIdentityWith T (lp (fun _ : Γ => X) p) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (lp (fun _ : Γ => X) p) - T)
        (lp (fun _ : Γ => X) p) C := by
  classical
  rcases hchoose with ⟨H, hHΛ, hHcard, hH⟩ | ⟨H, hHΛ, hHcard, hH⟩
  · obtain ⟨a⟩ := Cardinal.eq.mp hHcard.symm
    let e : Γ ↪ Γ := a.toEmbedding.trans (Function.Embedding.subtype H)
    have he (γ : Γ) : e γ ∈ Λ := hHΛ (a γ).property
    left
    exact lp_factors_of_coordinate_compression p T (fun γ => lpCoordinateEntry p T γ γ) e
      (lp_coordinate_compression p hp T Λ hdiag e he) hC
      (fun γ => hH (e γ) (a γ).property)
  · obtain ⟨a⟩ := Cardinal.eq.mp hHcard.symm
    let e : Γ ↪ Γ := a.toEmbedding.trans (Function.Embedding.subtype H)
    have he (γ : Γ) : e γ ∈ Λ := hHΛ (a γ).property
    right
    refine lp_factors_of_coordinate_compression p _
      (fun γ => ContinuousLinearMap.id 𝕜 X - lpCoordinateEntry p T γ γ) e ?_ hC
      (fun γ => hH (e γ) (a γ).property)
    intro x γ
    change lpExtend (𝕜 := 𝕜) p e x (e γ) - T (lpExtend p e x) (e γ) =
      x γ - lpCoordinateEntry p T (e γ) (e γ) (x γ)
    rw [lpExtend_apply_image, lp_coordinate_compression p hp T Λ hdiag e he]

theorem IsWeaklyCompactlyGenerated.ellOne_hasCPFP
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) {C : ℝ} (hC : 1 ≤ C)
    (hPFP : HasCPFP 𝕜 X C) : HasCPFP 𝕜 (lp (fun _ : Γ => X) 1) C := by
  intro T
  obtain ⟨Λ, hΛ, hdiag⟩ := hX.ellOne_diagonal_coordinates hΓ T
  have hinf := (Cardinal.aleph0_le_aleph 1).trans hΓ.le
  apply lp_factor_dichotomy_of_selected_coordinates 1 (by norm_num) T Λ hdiag
    (zero_le_one.trans hC)
  exact full_cardinal_factor_branch hinf Λ hΛ (fun γ => lpCoordinateEntry 1 T γ γ)
    (fun γ _ => hPFP (lpCoordinateEntry 1 T γ γ))

theorem IsWeaklyCompactlyGenerated.ellOne_hasUPFP
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hPFP : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (lp (fun _ : Γ => X) 1) := by
  obtain ⟨C, hC, hPFP⟩ := hPFP
  exact ⟨C, hC, hX.ellOne_hasCPFP hΓ hC hPFP⟩

theorem IsWeaklyCompactlyGenerated.ellOne_hasPFP_of_uncountable_cofinality
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hPFP : HasPFP 𝕜 X) :
    HasPFP 𝕜 (lp (fun _ : Γ => X) 1) := by
  intro T
  obtain ⟨Λ, hΛ, hdiag⟩ := hX.ellOne_diagonal_coordinates hΓ T
  have hinf := (Cardinal.aleph0_le_aleph 1).trans hΓ.le
  obtain ⟨C, hC, hchoose⟩ := full_cardinal_bounded_factor_branch hinf hcof Λ hΛ
    (fun γ => lpCoordinateEntry 1 T γ γ) (fun γ _ => hPFP (lpCoordinateEntry 1 T γ γ))
  exact (lp_factor_dichotomy_of_selected_coordinates 1 (by norm_num) T Λ hdiag
    (zero_le_one.trans hC) hchoose).imp
      FactorsIdentityWith.forget_bound FactorsIdentityWith.forget_bound

end ThesisCommon
