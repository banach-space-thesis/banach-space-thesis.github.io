import ThesisCommon.Analysis.LpInvariantBlocks
import ThesisCommon.Analysis.FullCountablePartitionEmbedding
import ThesisCommon.Analysis.LpPartitionCoordinates

/-! For a separable countable model, all countable invariant blocks become
model fibres under one actual isometry. Every off-diagonal entry vanishes. -/
noncomputable section
open TopologicalSpace
open scoped Cardinal ENNReal
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem separable_lp_primary_coordinates (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hfin : p ≠ ∞)
    [SeparableSpace (lp (fun _ : ℕ => X) p)]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (P : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p →L[𝕜]
      lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (hP : P.comp P = P) :
    ∃ E : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p ≃ₗᵢ[𝕜]
        lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p,
      (∀ γ, (lpCoordinateEntry p (operatorTransport E E P) γ γ).comp
        (lpCoordinateEntry p (operatorTransport E E P) γ γ) =
          lpCoordinateEntry p (operatorTransport E E P) γ γ) ∧
      ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
          ((lpCoordinateProjection (𝕜 := 𝕜) p {β}).comp (operatorTransport E E P)).comp
            (lpCoordinateProjection (𝕜 := 𝕜) p {α}) = 0 := by
  classical
  obtain ⟨B, ⟨hB, hBcount, hcover⟩, hproj, hdiag⟩ := lp_invariant_countable_blocks p hp hfin P hP
  obtain ⟨e, hne, hecover⟩ := countable_partition_nonempty_embedding B hΓ
    (Cardinal.mk_ord_toType _) hBcount hcover
  let D (γ : Γ) := B (e γ)
  have hD : Pairwise (fun i j => Disjoint (D i) (D j)) := fun _ _ h => hB (e.injective.ne h)
  have hφ (γ : Γ) : Nonempty (D γ × ℕ ≃ ℕ) := by
    letI : Countable (D γ) := (hBcount (e γ)).to_subtype
    letI : Nonempty (D γ) := (hne γ).to_subtype
    exact ⟨countableBlockIndexEquiv (D γ)⟩
  let φ (γ : Γ) : D γ × ℕ ≃ ℕ := Classical.choice (hφ γ)
  let E := lpPartitionReadIsometry (𝕜 := 𝕜) (X := X) p (zero_lt_one.trans hp) D hD hecover φ
  refine ⟨E, fun γ => lpPartitionReadIsometry_entry_idempotent p (zero_lt_one.trans hp)
    D hD hecover φ P γ (hproj (e γ)), Set.univ, Cardinal.mk_univ, ?_⟩
  intro α _ β _ hαβ
  have hz := lpPartitionReadIsometry_entry_zero p (zero_lt_one.trans hp)
    D hD hecover φ P α β (hdiag (e α) (e β) (e.injective.ne hαβ))
  apply ContinuousLinearMap.ext
  intro x
  have heq := congrArg (fun T => T (x α)) hz
  change operatorTransport E E P (lp.single p α (x α)) β = 0 at heq
  simp only [ContinuousLinearMap.comp_apply, lpCoordinateProjection_singleton, heq,
    lp.single_zero, ContinuousLinearMap.zero_apply]

end ThesisCommon
