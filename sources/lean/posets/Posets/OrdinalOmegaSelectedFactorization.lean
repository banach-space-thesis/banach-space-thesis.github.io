import Posets.OrdinalOmegaSelectedEstimates
import Posets.OrdinalRegularOmegaSelectedBounds
import Posets.OrdinalRegularOmegaAssemblyFactorization

/-! The selected compact cells give a literal identity factorisation for
arbitrary complementary operators at any uncountable initial cardinal. -/

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

local instance lossSelectedFactorModelCompact
    (F : OrdinalRegularOmegaColouredCores c hc M T S N (1 / 100) (1 / 100)) :
    ∀ i, CompactSpace (F.lossSelectedModel i) := fun i => by
  change CompactSpace (OrdinalInterval (c.ord ^ ((F.index i+1 : ℕ) : Ordinal)))
  infer_instance

theorem lossSelected_block_factorization
    (F : OrdinalRegularOmegaColouredCores c hc M T S N (1 / 100) (1 / 100)) :
    ∃ (J : OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.lossSelectedModel i)) →L[𝕜]
        JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)))
      (R : JLMS.CZero 𝕜 (Iio (c.ord ^ Ordinal.omega0)) →L[𝕜]
        OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.lossSelectedModel i))),
      R.comp ((if F.colour then T else S).comp J) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 5 / 2 := by
  have hescape : ∀ U ∈ cocompact (Iio (c.ord ^ Ordinal.omega0)),
      ∀ᶠ i in cofinite, ∀ x, (F.lossSelectedQ i x).val ∈ U := by
    apply ordinalRegularOmega_selected_escape c hc N F.index F.strictMono
      (fun i x => (F.lossSelectedQ i x).val)
    intro i x
    exact F.lossSelectedH_block i (F.lossSelectedQ i x).property
  have hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion (F.lossSelectedH) i)
      ((JLMS.evaluation (F.lossSelectedQ i x).val).comp (if F.colour then T else S))‖ ≤ 1 / 100 := by
    intro i x
    exact F.selected_cross_bound (F.lossSelectedH) (F.lossSelectedH_block) i _
      (F.lossSelectedQ_core i x)
  obtain ⟨R, hR, hRn⟩ := ordinalOmega_geometric_factors_from_leaf_mass
    (F.lossSelectedH) (F.lossSelectedH_disjoint) (F.lossSelectedH_clopen)
    (F.lossSelectedP) (F.lossSelectedQ) (F.lossSelected_section) M
    (if F.colour then T else S) hescape
    (F.lossSelectedLeaves) (F.lossSelectedLeaves_subset) (F.lossSelectedQ_leaf_closure)
    F.lossSelectedV (F.lossSelectedV_subset) (F.lossSelectedV_clopen) (F.lossSelectedV_compact)
    (F.lossSelectedP_constant_on_V)
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : 10 * (1 / 100 : ℝ) < 1 / 2)
    (F.lossSelected_leaf_diagonal) (F.lossSelected_leaf_restriction_mass) hcross
  refine ⟨ordinalOmegaGeometricInsertion (F.lossSelectedH) (F.lossSelectedH_disjoint)
    (F.lossSelectedH_clopen) (F.lossSelectedP) (F.lossSelectedQ) (F.lossSelected_section),
    R, hR, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    rw [ordinalOmegaGeometricInsertion_norm]
    simp
  · norm_num at hRn ⊢
    exact hRn

end OrdinalRegularOmegaColouredCores
end Posets

