import BanachIsometric.RawLipschitzChains
import BanachIsometric.AffineCarrierSupport
import BanachIsometric.LipschitzAffineSimplex
import BanachIsometric.UniversalSingularSubdivision

/-! The actual affine simplex pieces used by subdivision and its homotopy
are Lipschitz. Both operators therefore preserve the Lipschitz chain subcomplex. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_lipschitz_affineCarrierSimplex {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : {v : Fin (n + 1) → E // ∀ i, v i ∈ s}) :
    ∃ L : ℝ≥0, LipschitzWith L (affineCarrierSimplex hs v) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_affineSingularSimplex v.val
  exact ⟨L, hL.subtype_mk (fun w => (affineCarrierSimplex hs v w).property)⟩

theorem affineCarrierRealization_mem_lipschitz {s : Set E} (hs : Convex ℝ s) (n : ℕ)
    (c : affineCarrier s n) : affineCarrierRealization hs n c ∈ rawLipschitzCarrier s n := by
  refine affineCarrierRealization_supported hs n Set.univ
    {simplex | ∃ L : ℝ≥0, LipschitzWith L simplex} ?_ c ?_
  · intro v hv _
    exact exists_lipschitz_affineCarrierSimplex hs ⟨v, hv⟩
  · exact (Finsupp.mem_supported ℚ c.val).mpr (Set.subset_univ _)

theorem rawSubdivision_preserves_lipschitz {X : Type*} [PseudoMetricSpace X] (n : ℕ) :
    rawLipschitzCarrier X n ≤ (rawLipschitzCarrier X n).comap (rawSubdivision X n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨simplex, ⟨L, hL⟩, rfl⟩
  change rawSubdivision X n (Finsupp.single simplex 1) ∈ rawLipschitzCarrier X n
  rw [rawSubdivision_single_one]
  exact rawChainMap_preserves_lipschitz simplex hL n
    (affineCarrierRealization_mem_lipschitz (convex_stdSimplex ℝ _) n (universalAffineSubdivision n))

theorem rawSubdivisionHomotopy_preserves_lipschitz {X : Type*} [PseudoMetricSpace X] (n : ℕ) :
    rawLipschitzCarrier X n ≤ (rawLipschitzCarrier X (n + 1)).comap (rawSubdivisionHomotopy X n) := by
  conv_lhs => rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨simplex, ⟨L, hL⟩, rfl⟩
  change rawSubdivisionHomotopy X n (Finsupp.single simplex 1) ∈ rawLipschitzCarrier X (n + 1)
  rw [rawSubdivisionHomotopy_single_one]
  exact rawChainMap_preserves_lipschitz simplex hL (n + 1)
    (affineCarrierRealization_mem_lipschitz (convex_stdSimplex ℝ _) (n + 1)
      (universalAffineSubdivisionHomotopy n))

end BanachIsometric.SingularPrism
