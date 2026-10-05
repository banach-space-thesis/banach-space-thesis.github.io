import Posets.OrdinalRegularOmegaSelectedEstimates
import Posets.OrdinalRegularOmegaSelectedBounds
import Posets.OrdinalRegularOmegaAssemblyFactorization

/-! The selected compact cells give a literal identity factorisation for
one of the two arbitrary complementary global operators. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets
open ThesisCommon

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000

variable {𝕜 : Type*} [RCLike 𝕜] {c : Cardinal.{u}} {hc : Cardinal.aleph0 < c}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (c.ord ^ Ordinal.omega0))}
  {T S : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0))} {N : ℕ}

namespace OrdinalRegularOmegaColouredCores

local instance selectedFactorModelCompact
    (F : OrdinalRegularOmegaColouredCores c hc M T S N (1 / 100) (1 / 100)) :
    ∀ i, CompactSpace (F.selectedModel i) := fun i => by
  change CompactSpace (OrdinalInterval (c.ord ^ ((F.index i+2 : ℕ) : Ordinal)))
  infer_instance

theorem selected_block_factorization
    (F : OrdinalRegularOmegaColouredCores c hc M T S N (1 / 100) (1 / 100))
    (hr : c.IsRegular) :
    ∃ (J : OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.selectedModel i)) →L[𝕜]
        JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
      (R : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
        OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.selectedModel i))),
      R.comp ((if F.colour then T else S).comp J) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 5 / 2 := by
  have hescape : ∀ U ∈ cocompact (Iio (c.ord ^ Ordinal.omega0)),
      ∀ᶠ i in cofinite, ∀ x, (F.selectedQ hr i x).val ∈ U := by
    apply ordinalRegularOmega_selected_escape c hc N F.index F.strictMono
      (fun i x => (F.selectedQ hr i x).val)
    intro i x
    exact F.selectedH_block hr i (F.selectedQ hr i x).property
  have hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion (F.selectedH hr) i)
      ((JLMS.evaluation (F.selectedQ hr i x).val).comp (if F.colour then T else S))‖ ≤ 1 / 100 := by
    intro i x
    exact F.selected_cross_bound (F.selectedH hr) (F.selectedH_block hr) i _
      (F.selectedQ_core hr i x)
  obtain ⟨R, hR, hRn⟩ := ordinalOmega_geometric_factors_from_leaf_mass
    (F.selectedH hr) (F.selectedH_disjoint hr) (F.selectedH_clopen hr)
    (F.selectedP hr) (F.selectedQ hr) (F.selected_section hr) M
    (if F.colour then T else S) hescape
    (F.selectedLeaves hr) (F.selectedLeaves_subset hr) (F.selectedQ_leaf_closure hr)
    F.selectedV (F.selectedV_subset hr) (F.selectedV_clopen hr) (F.selectedV_compact hr)
    (F.selectedP_constant_on_selectedV hr)
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : 10 * (1 / 100 : ℝ) < 1 / 2)
    (F.selected_leaf_diagonal hr) (F.selected_leaf_restriction_mass hr) hcross
  refine ⟨ordinalOmegaGeometricInsertion (F.selectedH hr) (F.selectedH_disjoint hr)
    (F.selectedH_clopen hr) (F.selectedP hr) (F.selectedQ hr) (F.selected_section hr),
    R, hR, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    rw [ordinalOmegaGeometricInsertion_norm]
    simp
  · norm_num at hRn ⊢
    exact hRn

end OrdinalRegularOmegaColouredCores
end Posets
