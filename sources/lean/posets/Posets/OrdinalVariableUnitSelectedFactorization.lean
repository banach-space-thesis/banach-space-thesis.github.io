import Posets.OrdinalVariableUnitSelectedEstimates
import Posets.OrdinalVariableUnitSelectedBounds
import Posets.OrdinalVariableUnitSelectedRanks
import Posets.OrdinalRegularOmegaAssemblyFactorization

/-! The selected compact cells give a literal identity factorisation along
an actual cofinal sequence of variable ordinal rank units. -/

noncomputable section
open Set Filter Topology
universe u
namespace Posets
open ThesisCommon

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000

variable {𝕜 : Type*} [RCLike 𝕜] {γ : Ordinal.{u}} {N : ℕ} {P : OrdinalVariableUnitParameters γ N}
  {M : JLMS.AtomicDualModel 𝕜 (Iio (Ordinal.omega0 ^ γ))}
  {T S : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
    JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ))}

namespace OrdinalVariableUnitColouredCores

local instance selectedFactorModelCompact
    (F : OrdinalVariableUnitColouredCores P M T S (1 / 100) (1 / 100)) :
    ∀ i, CompactSpace (F.selectedModel i) := fun i => by
  change CompactSpace (OrdinalInterval (Ordinal.omega0 ^ P.sourceUnit (F.index i)))
  infer_instance

theorem selected_block_factorization
    (F : OrdinalVariableUnitColouredCores P M T S (1 / 100) (1 / 100)) (hγ : Order.IsSuccLimit γ) :
    ∃ (J : OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.selectedModel i)) →L[𝕜]
        JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)))
      (R : JLMS.CZero 𝕜 (Iio (Ordinal.omega0 ^ γ)) →L[𝕜]
        OrdinalBlockFunctionSum 𝕜 (fun i => ↥(F.selectedModel i))),
      R.comp ((if F.colour then T else S).comp J) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖J‖ ≤ 1 ∧ ‖R‖ ≤ 5 / 2 := by
  have hescape : ∀ U ∈ cocompact (Iio (Ordinal.omega0 ^ γ)),
      ∀ᶠ i in cofinite, ∀ x, (F.selectedQ i x).val ∈ U := by
    apply ordinalVariableUnit_selected_escape P hγ F.index F.strictMono
      (fun i x => (F.selectedQ i x).val)
    intro i x
    exact F.selectedH_block i (F.selectedQ i x).property
  have hcross : ∀ i x, ‖JLMS.atomicRestriction M (wolfeCrossUnion (F.selectedH) i)
      ((JLMS.evaluation (F.selectedQ i x).val).comp (if F.colour then T else S))‖ ≤ 1 / 100 := by
    intro i x
    exact F.selected_cross_bound (F.selectedH) (F.selectedH_block) i _
      (F.selectedQ_core i x)
  obtain ⟨R, hR, hRn⟩ := ordinalOmega_geometric_factors_from_leaf_mass
    (F.selectedH) (F.selectedH_disjoint) (F.selectedH_clopen)
    (F.selectedP) (F.selectedQ) (F.selected_section) M
    (if F.colour then T else S) hescape
    (F.selectedLeaves) (F.selectedLeaves_subset) (F.selectedQ_leaf_closure)
    F.selectedV (F.selectedV_subset) (F.selectedV_clopen) (F.selectedV_compact)
    (F.selectedP_constant_on_V)
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : 10 * (1 / 100 : ℝ) < 1 / 2)
    (F.selected_leaf_diagonal) (F.selected_leaf_restriction_mass) hcross
  refine ⟨ordinalOmegaGeometricInsertion (F.selectedH) (F.selectedH_disjoint)
    (F.selectedH_clopen) (F.selectedP) (F.selectedQ) (F.selected_section),
    R, hR, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    rw [ordinalOmegaGeometricInsertion_norm]
    simp
  · norm_num at hRn ⊢
    exact hRn

end OrdinalVariableUnitColouredCores
end Posets




