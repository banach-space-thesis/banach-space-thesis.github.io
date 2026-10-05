import Posets.CountableOrdinalUPFPCanonical
import Posets.OrdinalIdealTransportRepeatedModel
import JLMS.OrdinalAtomicMatrix
import ThesisCommon.Analysis.DualDirectSums
import ThesisCommon.Analysis.CZeroSelfSimilarity
import ThesisCommon.Analysis.OrdinalFiniteAssembly
import ThesisCommon.Analysis.OrdinalInfinityDichotomy
import ThesisCommon.Analysis.EllOneSelfSimilarPreservation

/-! Actual ordinal background from the checked ordinal tower and Rudin
constructions. The direct-sum models are identified by their coordinates. -/
noncomputable section
open Filter Topology Set
open scoped ZeroAtInfty ENNReal
namespace LPCK
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalContinuousDualEllOneEquiv (α : Ordinal) :
    (OrdinalContinuous 𝕜 α →L[𝕜] 𝕜) ≃L[𝕜] EllOneSum (OrdinalInterval α) 𝕜 :=
  (banachDualEquiv (JLMS.ordinalContinuousCZeroEquiv (𝕜 := 𝕜) α).toContinuousLinearEquiv).trans
    (JLMS.ordinalAtomicDualModel (𝕜 := 𝕜) α).representation.toContinuousLinearEquiv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def jlmsCZeroToMap (x : JLMS.CZeroSum 𝕜 (fun _ : ℕ => X)) : CZeroSum X where
  toFun := x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, tendsto_zero_iff_norm_tendsto_zero]
    exact x.tendsto_norm

def mapToJlmsCZero (x : CZeroSum X) : JLMS.CZeroSum 𝕜 (fun _ : ℕ => X) :=
  JLMS.CZeroSum.mk (fun i => x i)
    (by simpa only [cocompact_eq_cofinite, norm_zero] using (zero_at_infty x).norm)

def jlmsCZeroMapIsometry : JLMS.CZeroSum 𝕜 (fun _ : ℕ => X) ≃ₗᵢ[𝕜] CZeroSum X where
  toFun := jlmsCZeroToMap
  invFun := mapToJlmsCZero
  left_inv x := by apply JLMS.CZeroSum.ext; intro i; rfl
  right_inv x := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl
  norm_map' x := by
    apply le_antisymm
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).2
      exact x.norm_apply_le_norm
    · apply JLMS.CZeroSum.norm_le (norm_nonneg (jlmsCZeroToMap x))
      exact (jlmsCZeroToMap x).toBCF.norm_coe_le_norm

end LPCK
