import ThesisCommon.Analysis.CZeroInvariantBlocks
import ThesisCommon.Analysis.FullCountablePartitionEmbedding
import ThesisCommon.Analysis.CZeroPartitionCoordinates

/-! For a separable countable model, all countable invariant blocks become
model fibres under one actual isometry. Every off-diagonal entry vanishes. -/
noncomputable section
open TopologicalSpace
open scoped Cardinal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem separable_cZero_primary_coordinates

    [SeparableSpace (C₀(ℕ, X))]
    (hΓ : Cardinal.aleph0 < Cardinal.mk Γ)
    (P : C₀(Γ, C₀(ℕ, X)) →L[𝕜]
      C₀(Γ, C₀(ℕ, X))) (hP : P.comp P = P) :
    ∃ E : C₀(Γ, C₀(ℕ, X)) ≃ₗᵢ[𝕜]
        C₀(Γ, C₀(ℕ, X)),
      (∀ γ, (cZeroCoordinateEntry (operatorTransport E E P) γ γ).comp
        (cZeroCoordinateEntry (operatorTransport E E P) γ γ) =
          cZeroCoordinateEntry (operatorTransport E E P) γ γ) ∧
      ∃ H : Set Γ, Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ α ∈ H, ∀ β ∈ H, α ≠ β →
          ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp (operatorTransport E E P)).comp
            (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0 := by
  classical
  obtain ⟨B, ⟨hB, hBcount, hcover⟩, hproj, hdiag⟩ := cZero_invariant_countable_blocks P hP
  obtain ⟨e, hne, hecover⟩ := countable_partition_nonempty_embedding B hΓ
    (Cardinal.mk_ord_toType _) hBcount hcover
  let D (γ : Γ) := B (e γ)
  have hD : Pairwise (fun i j => Disjoint (D i) (D j)) := fun _ _ h => hB (e.injective.ne h)
  have hφ (γ : Γ) : Nonempty (D γ × ℕ ≃ ℕ) := by
    letI : Countable (D γ) := (hBcount (e γ)).to_subtype
    letI : Nonempty (D γ) := (hne γ).to_subtype
    exact ⟨countableBlockIndexEquiv (D γ)⟩
  let φ (γ : Γ) : D γ × ℕ ≃ ℕ := Classical.choice (hφ γ)
  let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) D hD hecover φ
  refine ⟨E, fun γ => cZeroPartitionReadIsometry_entry_idempotent
    D hD hecover φ P γ (hproj (e γ)), Set.univ, Cardinal.mk_univ, ?_⟩
  intro α _ β _ hαβ
  have hz := cZeroPartitionReadIsometry_entry_zero
    D hD hecover φ P α β (hdiag (e α) (e β) (e.injective.ne hαβ))
  apply ContinuousLinearMap.ext
  intro x
  have heq := congrArg (fun T => T (x α)) hz
  change operatorTransport E E P (cZeroSingleAt α (x α)) β = 0 at heq
  simp only [ContinuousLinearMap.comp_apply, cZeroCoordinateProjection_singleton, heq,
    ContinuousLinearMap.zero_apply]
  ext γ; simp

end ThesisCommon


