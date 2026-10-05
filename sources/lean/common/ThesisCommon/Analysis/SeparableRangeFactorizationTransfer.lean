import ThesisCommon.Analysis.WCGEllOneFactorizationTransfer
import ThesisCommon.Analysis.UncountableSchauderTransfer
import ThesisCommon.Analysis.UncountableSchauderOperatorSupport

/-! The separable-range replacements in PFP Remarks 4.5 and 4.31.
Countable outgoing coordinates suffice above aleph-one. The construction
preserves uniform constants; only the nonuniform version uses cofinality. -/
noncomputable section
open TopologicalSpace
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem ellOne_countable_outgoing_entries_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (T : lp (fun _ : Γ => X) 1 →L[𝕜] lp (fun _ : Γ => X) 1) (α : Γ) :
    {β | ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
      (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) ≠ 0}.Countable := by
  classical
  obtain ⟨Λ, hΛ, hz⟩ := ellOne_operator_countable_support_of_separable_scalar_ranges hsep
    (T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1) (E := fun _ : Γ => X) α))
  apply hΛ.mono
  intro β hβ
  by_contra hβΛ
  apply hβ
  apply ContinuousLinearMap.ext
  intro x
  have hzero := hz (x α) β hβΛ
  change T (lp.single 1 α (x α)) β = 0 at hzero
  simp only [ContinuousLinearMap.comp_apply, lpCoordinateProjection_singleton, hzero]
  exact lp.single_zero 1 β

theorem ellOne_diagonal_coordinates_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : lp (fun _ : Γ => X) 1 →L[𝕜] lp (fun _ : Γ => X) 1) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
      ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
        ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
          (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) = 0 := by
  obtain ⟨Λ, hΛ, hfree⟩ := relation_free_set_of_countable_outgoing
    (fun α β => ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
      (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) ≠ 0) hΓ
    (ellOne_countable_outgoing_entries_of_separable_scalar_ranges hsep T)
  exact ⟨Λ, hΛ, fun α hα β hβ hne => not_not.mp (hfree α hα β hβ hne)⟩

theorem ellOne_hasCPFP_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) {C : ℝ} (hC : 0 ≤ C)
    (hX : HasCPFP 𝕜 X C) : HasCPFP 𝕜 (lp (fun _ : Γ => X) 1) C := by
  intro T
  obtain ⟨Λ, hΛ, hdiag⟩ := ellOne_diagonal_coordinates_of_separable_scalar_ranges hsep hΓ T
  apply lp_factor_dichotomy_of_selected_coordinates 1 (by norm_num) T Λ hdiag hC
  exact full_cardinal_factor_branch ((Cardinal.aleph0_le_aleph 1).trans hΓ.le)
    Λ hΛ (fun γ => lpCoordinateEntry 1 T γ γ) (fun γ _ => hX (lpCoordinateEntry 1 T γ γ))

theorem ellOne_hasUPFP_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (lp (fun _ : Γ => X) 1) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨C, hC, ellOne_hasCPFP_of_separable_scalar_ranges hsep hΓ (zero_le_one.trans hC) hX⟩

theorem ellOne_hasPFP_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : HasPFP 𝕜 X) :
    HasPFP 𝕜 (lp (fun _ : Γ => X) 1) := by
  intro T
  obtain ⟨Λ, hΛ, hdiag⟩ := ellOne_diagonal_coordinates_of_separable_scalar_ranges hsep hΓ T
  obtain ⟨C, hC, hchoose⟩ := full_cardinal_bounded_factor_branch
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le) hcof Λ hΛ
    (fun γ => lpCoordinateEntry 1 T γ γ) (fun γ _ => hX (lpCoordinateEntry 1 T γ γ))
  exact (lp_factor_dichotomy_of_selected_coordinates 1 (by norm_num) T Λ hdiag
    (zero_le_one.trans hC) hchoose).imp
      FactorsIdentityWith.forget_bound FactorsIdentityWith.forget_bound

namespace UncountableSchauderSum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

theorem countable_outgoing_entries_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X) (α : Γ) :
    {β | coordinateEntry T β α ≠ 0}.Countable := by
  obtain ⟨Λ, hΛ, hz⟩ := operator_countable_support_of_separable_scalar_ranges hsep
    (T.comp (singleL (b := b) (hb := hb) (Y := X) α))
  apply hΛ.mono
  intro β hβ
  by_contra hβΛ
  apply hβ
  apply ContinuousLinearMap.ext
  intro x
  have hzero := hz (x α) β hβΛ
  change T (single α (x α)) β = 0 at hzero
  rw [coordinateEntry_apply, hzero]
  change singleL (b := b) (hb := hb) (Y := X) β 0 = 0
  exact map_zero _

theorem diagonal_coordinates_of_separable_scalar_ranges
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧ ∀ α ∈ Λ, ∀ β ∈ Λ,
      α ≠ β → coordinateEntry T β α = 0 :=
  diagonal_coordinates_of_countable_outgoing hΓ T
    (countable_outgoing_entries_of_separable_scalar_ranges hsep T)

theorem hasCPFP_of_separable_scalar_ranges (hs : b.HasSymmetricNorm)
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) {C : ℝ} (hC : 0 ≤ C)
    (hX : HasCPFP 𝕜 X C) : HasCPFP 𝕜 (UncountableSchauderSum b hs.1 X) C :=
  hasCPFP_of_diagonal_selection hs (Cardinal.aleph0_lt_aleph_one.trans hΓ).le
    (diagonal_coordinates_of_separable_scalar_ranges hsep hΓ) hC hX

theorem hasUPFP_of_separable_scalar_ranges (hs : b.HasSymmetricNorm)
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ) (hX : HasUPFP 𝕜 X) :
    HasUPFP 𝕜 (UncountableSchauderSum b hs.1 X) := by
  obtain ⟨C, hC, hX⟩ := hX
  exact ⟨C, hC, hasCPFP_of_separable_scalar_ranges hs hsep hΓ (zero_le_one.trans hC) hX⟩

theorem hasPFP_of_separable_scalar_ranges (hs : b.HasSymmetricNorm)
    (hsep : ∀ S : X →L[𝕜] E, IsSeparable (Set.range S))
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (hcof : Cardinal.aleph0 < (Cardinal.mk Γ).ord.cof) (hX : HasPFP 𝕜 X) :
    HasPFP 𝕜 (UncountableSchauderSum b hs.1 X) :=
  hasPFP_of_diagonal_selection hs (Cardinal.aleph0_lt_aleph_one.trans hΓ).le hcof
    (diagonal_coordinates_of_separable_scalar_ranges hsep hΓ) hX

end UncountableSchauderSum
end ThesisCommon
