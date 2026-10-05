import ThesisCommon.Analysis.WCGEllOneSupport
import ThesisCommon.Analysis.CoordinateMasks
import ThesisCommon.Analysis.HajnalFreeSet

/-! Coordinate selection for actual vector-valued ℓ₁ sums with WCG
coefficients. Countable outgoing supports and full Hajnal selection apply
also at singular index cardinals strictly above aleph-one. -/
noncomputable section
open scoped Cardinal ENNReal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lpCoordinateProjection_singleton (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (α : Γ) (x : lp (fun _ : Γ => X) p) :
    lpCoordinateProjection (𝕜 := 𝕜) p {α} x = lp.single p α (x α) := by
  classical
  apply lp.ext
  funext γ
  by_cases h : γ = α
  · subst γ
    simp
  · simp [lpCoordinateProjection_apply, h]

theorem IsWeaklyCompactlyGenerated.ellOne_countable_outgoing_entries
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (T : lp (fun _ : Γ => X) 1 →L[𝕜] lp (fun _ : Γ => X) 1) (α : Γ) :
    {β | ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
      (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) ≠ 0}.Countable := by
  classical
  obtain ⟨Λ, hΛ, hz⟩ := hX.ellOne_operator_countable_support
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

theorem IsWeaklyCompactlyGenerated.ellOne_diagonal_coordinates
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (hΓ : Cardinal.aleph 1 < Cardinal.mk Γ)
    (T : lp (fun _ : Γ => X) 1 →L[𝕜] lp (fun _ : Γ => X) 1) :
    ∃ Λ : Set Γ, Cardinal.mk Λ = Cardinal.mk Γ ∧
      ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
        ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
          (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) = 0 := by
  classical
  let F : Γ → Set Γ := fun α =>
    {β | ((lpCoordinateProjection (𝕜 := 𝕜) 1 {β}).comp T).comp
      (lpCoordinateProjection (𝕜 := 𝕜) 1 {α}) ≠ 0}
  have hcount (α : Γ) : (F α).Countable := hX.ellOne_countable_outgoing_entries T α
  have hsize (α : Γ) : Cardinal.mk (F α) < Cardinal.aleph 1 :=
    (Cardinal.countable_iff_lt_aleph_one _).mp (hcount α).to_subtype
  have hinf : Cardinal.aleph0 ≤ Cardinal.mk Γ :=
    (Cardinal.aleph0_le_aleph 1).trans hΓ.le
  obtain ⟨Λ, hΛ, hfree⟩ := hajnal_free_set F (Cardinal.aleph 1) hinf hΓ hsize
  refine ⟨Λ, hΛ, ?_⟩
  intro α hα β hβ hne
  exact not_not.mp (hfree α hα β hβ hne).2

end ThesisCommon
