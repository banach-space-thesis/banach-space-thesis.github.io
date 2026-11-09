import JLMS.ScatteredTopology
import JLMS.Rudin

/-!
# Printed Section 4 statements

These wrappers state Lemmas 4.5 and 4.7 and Theorem 4.8 directly, using the
already proved constructions. The finite point set in Lemma 4.5 is explicit;
Lemma 4.7 contains all three clauses in one conclusion, including the printed
nonempty-set exception for norm one; Theorem 4.8 asserts the isometric dual
equivalence for locally compact scattered spaces over either scalar field.

Source: the original JLMS author proof, pages 8-9. No changes to the printed
mathematical hypotheses or conclusions are made here.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

local instance printedTopologyDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) :=
  inferInstance
local instance printedTopologyDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) :=
  inferInstance

/-- Lemma 4.5: every finite point set has pairwise disjoint compact clopen
neighborhoods. Indexing by the points expresses the paper's neighborhood
collection bijection; disjointness and point membership make the sets distinct. -/
theorem lemma_4_5 (hK : IsScattered K) (F : Finset K) :
    ∃ U : F → Set K,
      (∀ k : F, IsOpen (U k) ∧ IsClosed (U k) ∧ IsCompact (U k) ∧ k.val ∈ U k) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  obtain ⟨U⟩ := exists_neighborhoodFamily hK (fun k : F => k.val) Subtype.val_injective
  exact ⟨U.sets, fun k => ⟨(U.clopen k).isOpen, (U.clopen k).isClosed,
    U.compact k, U.contains k⟩, U.disjoint⟩

/-- Lemma 4.7(a)-(c), with exactly the exception to norm one printed in(b). -/
theorem lemma_4_7 (hK : IsScattered K) (F : Finset K)
    (U : NeighborhoodFamily (fun k : F => k.val)) :
    let P := neighborhoodProjection (𝕜 := 𝕜) U
    (FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) ∧ P.comp P = P) ∧
      ((F.Nonempty → ‖P‖ = 1) ∧ ‖ContinuousLinearMap.id 𝕜 (CZero 𝕜 K) - P‖ ≤ 2) ∧
      (∀ k : F, banachAdjoint P (evaluation k.val) = evaluation k.val) := by
  refine ⟨⟨neighborhoodProjection_finiteRank U, neighborhoodProjection_idempotent U⟩,
    ⟨?_, norm_id_sub_neighborhoodProjection_le_two U⟩,
    neighborhoodProjection_adjoint_evaluation U⟩
  intro hF
  obtain ⟨k, hk⟩ := hF
  letI : Nonempty F := ⟨⟨k, hk⟩⟩
  exact neighborhoodProjection_norm_eq_one U

/-- Theorem 4.8: the locally compact Rudin representation, over ℝ or ℂ. -/
theorem theorem_4_8 (hK : IsScattered K) :
    Nonempty ((CZero 𝕜 K →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] ellOneOn 𝕜 K) := by
  obtain ⟨M⟩ := exists_atomicDualModel (𝕜 := 𝕜) hK
  exact ⟨M.representation⟩

end JLMS
