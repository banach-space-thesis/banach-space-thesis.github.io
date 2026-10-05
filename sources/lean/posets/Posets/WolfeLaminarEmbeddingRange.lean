import Posets.WolfeLaminarEmbeddingCoordinates
import JLMS.CompactCZeroEquiv


/-! Pullback embeds the quotient function space isometrically into C₀(K).
The range of any such complete isometry is exactly the closed span of the
images of a family with dense linear span. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem linearIsometry_range_eq_closedSpan {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (P : E →ₗᵢ[𝕜] F) (v : ι → E) (u : ι → F)
    (hd : Dense (Submodule.span 𝕜 (range v) : Set E)) (hPu : ∀ i, P (v i) = u i) :
    range P = ((Submodule.span 𝕜 (range u)).topologicalClosure : Set F) := by
  apply subset_antisymm
  · rintro _ ⟨f, rfl⟩
    have hm : Submodule.span 𝕜 (range v) ≤
        (Submodule.span 𝕜 (range u)).comap P.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change P (v i) ∈ Submodule.span 𝕜 (range u)
      rw [hPu i]
      exact Submodule.subset_span (mem_range_self i)
    have hi : P '' (Submodule.span 𝕜 (range v) : Set E) ⊆
        (Submodule.span 𝕜 (range u) : Set F) := by
      rintro _ ⟨g, hg, rfl⟩
      exact hm hg
    exact closure_mono hi (image_closure_subset_closure_image P.continuous (mem_image_of_mem P (hd f)))
  · apply closure_minimal _ P.isometry.isClosedEmbedding.isClosed_range
    change Submodule.span 𝕜 (range u) ≤ LinearMap.range P.toLinearMap
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, hPu i⟩

variable {K ι : Type*} [TopologicalSpace K] [CompactSpace K]

def wolfeClopenCZeroIsometry (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) :
    C(WolfeClopenQuotient A hA, 𝕜) →ₗᵢ[𝕜] JLMS.CZero 𝕜 K :=
  (JLMS.compactContinuousCZeroEquiv (𝕜 := 𝕜) (K := K)).toLinearIsometry.comp
    (wolfeClopenPullIsometry A hA)

theorem wolfeClopenCZeroIsometry_coordinate (A : ι → Set K) (hA : ∀ i, IsClopen (A i)) (i : ι) :
    wolfeClopenCZeroIsometry (𝕜 := 𝕜) A hA (wolfeClopenCoordinate A hA i) =
      JLMS.clopenIndicator (A i) (hA i) (hA i).isClosed.isCompact := by
  ext x
  change wolfeClopenCoordinate (𝕜 := 𝕜) A hA i (wolfeClopenProjection A hA x) = _
  rw [wolfeClopenCoordinate_projection, JLMS.clopenIndicator_apply]
  rfl

end Posets

