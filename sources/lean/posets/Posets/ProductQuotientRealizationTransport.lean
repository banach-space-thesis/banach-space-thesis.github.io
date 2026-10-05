import Posets.ProductQuotientRealizationChoice
import Posets.ProductQuotientRealizationFamily
import PosetsCommon.CZeroSumFlatten

/-! Isometric transport of the quantitative product split to one Mrówka space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

theorem quantitativeSplit_transport {𝕜 : Type} [RCLike 𝕜] {E F C : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (e : E ≃ₗᵢ[𝕜] F) (h : HasQuantitativeSplit 𝕜 E C) :
    HasQuantitativeSplit 𝕜 F C := by
  obtain ⟨θ, ρ, hs, hρ, hθ, hθone⟩ := h
  let c := LinearIsometryEquiv.refl 𝕜 C
  have hc : ∀ a b, c (a * b) = c a * c b := fun _ _ => rfl
  refine ⟨transportQuotient e c hc θ, transportSection e c hc ρ,
    strongSplit_transport e c hc θ ρ hs,
    isometry_transportSection e c hc ρ hρ, ?_, ?_⟩
  · exact (norm_transportQuotient e c hc θ).trans_le hθ
  · intro hn
    exact (norm_transportQuotient e c hc θ).trans (hθone hn)

theorem exists_product_space_realization {𝕜 : Type} [RCLike 𝕜] {C : ℕ → Type}
    [∀ n, NormedRing (C n)] [∀ n, NormedAlgebra 𝕜 (C n)]
    (d : ∀ n, ProductQuotientComponent 𝕜 (C n)) :
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      HasQuantitativeSplit 𝕜 (Space 𝕜 𝒜) (NormedProduct C) := by
  letI := space_empty_separable (𝕜 := 𝕜)
  obtain ⟨B, hB, h⟩ := exists_product_leaf_realization d
  letI : Infinite (Σ n, (d n).Coordinates) := Infinite.of_injective
    (fun n : ℕ => (⟨n, Classical.choice (inferInstance : Nonempty (d n).Coordinates)⟩ :
      Σ n, (d n).Coordinates))
    (fun _ _ h => congrArg Sigma.fst h)
  obtain ⟨𝒜, had, ⟨e⟩⟩ := exists_combined_countableSpace (𝕜 := 𝕜)
    (fun p : Σ n, (d n).Coordinates => B p.1 p.2) (fun p => hB p.1 p.2)
  let f : DependentCZeroSum 𝕜 (ProductLeafSum d B) ≃ₗᵢ[𝕜] Space 𝕜 𝒜 :=
    (cZeroSumFlattenEquiv (𝕜 := 𝕜) (fun n q => Space 𝕜 (B n q))).trans e
  exact ⟨𝒜, had, quantitativeSplit_transport f h⟩

end Posets
