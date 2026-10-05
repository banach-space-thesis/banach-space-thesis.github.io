import ThesisCommon.Analysis.WCGEllOneIteratedSupport
import ThesisCommon.Analysis.WCGEllOneDiagonalSelection

/-! Hajnal selection for the actual iterated countable model, using WCG on
the original coefficient space and its countable coordinate expansion. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsWeaklyCompactlyGenerated.iterated_ellOne_diagonal_coordinates
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1 →L[𝕜]
      lp (fun _ : Γ => lp (fun _ : ℕ => X) 1) 1) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
      ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
        ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
          (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) = 0 := by
  classical
  let F (α : Γ) : Set Γ :=
    {β | ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
      (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) ≠ 0}
  have hcount (α : Γ) : (F α).Countable := by
    obtain ⟨Λ, hΛ, hz⟩ := hX.iterated_ellOne_operator_countable_support
      (T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1)
        (E := fun _ : Γ => lp (fun _ : ℕ => X) 1) α))
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
  obtain ⟨Λ, hΛ, hfree⟩ := hajnal_free_set F (Cardinal.aleph 1)
    ((Cardinal.aleph0_le_aleph 1).trans hΓ.le) hΓ
    (fun α => (Cardinal.countable_iff_lt_aleph_one _).mp (hcount α))
  exact ⟨Λ, hΛ, fun α hα β hβ hne => not_not.mp (hfree α hα β hβ hne).2⟩

end ThesisCommon
