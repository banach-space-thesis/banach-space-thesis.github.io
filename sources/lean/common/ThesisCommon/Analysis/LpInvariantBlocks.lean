import ThesisCommon.Analysis.LpCountableIncoming
import ThesisCommon.Analysis.CountableInvariantPartition
import ThesisCommon.Analysis.LpTriangularSupport

/-! Separable-valued lp projections, 1 < p < ∞, admit a partition into
countable invariant coordinate blocks. Every pair of different blocks is
separated, so the conclusion holds for arbitrary cardinalities. -/
noncomputable section
open TopologicalSpace
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]

theorem lp_invariant_countable_blocks (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hfin : p ≠ ∞)
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p) (hP : P.comp P = P) :
    ∃ B : (Cardinal.mk Γ).ord.toType → Set Γ,
      (Pairwise (fun α β => Disjoint (B α) (B β)) ∧
        (∀ α, (B α).Countable) ∧ (⋃ α, B α) = Set.univ) ∧
      (∀ α, (lpBlockCompression p P (B α)).comp (lpBlockCompression p P (B α)) =
        lpBlockCompression p P (B α)) ∧
      ∀ α β, α ≠ β → ((lpCoordinateProjection (𝕜 := 𝕜) p (B β)).comp P).comp
        (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p (B α)).subtypeL = 0 := by
  classical
  let F (α : Γ) : Set Γ := {β | lpFibreRelation p P α β ∨ lpFibreRelation p P β α}
  have hF (α : Γ) : (F α).Countable :=
    (lpFibreRelation_outgoing_countable p hfin P α).union
      (lpFibreRelation_incoming_countable p hp P α)
  obtain ⟨B, hdisj, hcount, hcover, hclosed⟩ := countable_invariant_partition F hF
    (fun _ _ h => h.symm)
  have hinv (i : (Cardinal.mk Γ).ord.toType) :
      ∀ x : lp (fun _ : Γ => X) p, (∀ γ ∉ B i, x γ = 0) →
        ∀ γ ∉ B i, P x γ = 0 := by
    apply lp_operator_supported_of_single p hfin P (B i) (B i)
    intro α hα x β hβ
    exact lpFibreRelation_zero p P (fun h => hβ (hclosed i α hα (Or.inl h))) x
  have hfix (A : Set Γ) (y : lp (fun _ : Γ => X) p) (hy : ∀ γ ∉ A, y γ = 0) :
      lpCoordinateProjection (𝕜 := 𝕜) p A y = y := by
    apply lp.ext
    funext γ
    by_cases hγ : γ ∈ A
    · simp only [lpCoordinateProjection_apply, if_pos hγ]
    · simp only [lpCoordinateProjection_apply, if_neg hγ, hy γ hγ]
  refine ⟨B, ⟨hdisj, hcount, hcover⟩, ?_, ?_⟩
  · intro i
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change lpCoordinateProjection p (B i) (P (lpCoordinateProjection p (B i) (P x.val))) =
      lpCoordinateProjection p (B i) (P x.val)
    rw [hfix (B i) (P x.val) (hinv i x.val x.property)]
    have hPP := DFunLike.congr_fun hP x.val
    change P (P x.val) = P x.val at hPP
    rw [hPP]
    exact hfix (B i) (P x.val) (hinv i x.val x.property)
  · intro i j hij
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext γ
    change lpCoordinateProjection p (B j) (P x.val) γ = 0
    by_cases hγ : γ ∈ B j
    · rw [lpCoordinateProjection_apply, if_pos hγ]
      exact hinv i x.val x.property γ (fun hγi => Set.disjoint_left.mp (hdisj hij) hγi hγ)
    · simp only [lpCoordinateProjection_apply, if_neg hγ]

end ThesisCommon
