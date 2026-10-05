import JLMS.LoyWillisIdeal
import JLMS.OrdinalMatrixAlgebra
import JLMS.AtomicRankOneMatrix

/-! # Splitting an operator in M into its endpoint column and the remaining matrix -/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)

local instance loyWillisDecompositionOperatorGroup : NormedAddCommGroup
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance
local instance loyWillisDecompositionOperatorSpace : NormedSpace 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance

def loyWillisEndpointColumn (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) : OrdinalC 𝕜 c.ord :=
  ⟨_, continuous_endpointColumn_of_mem_loyWillisSubspace hc hu T hT⟩

@[simp] theorem loyWillisEndpointColumn_apply
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) (x : OrdinalInterval c.ord) :
    loyWillisEndpointColumn hc hu T hT x =
      ordinalOperatorMatrix c.ord T x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := rfl

def ordinalEndpointRankOne (α : Ordinal.{u}) (f : OrdinalC 𝕜 α) :
    OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α :=
  (ContinuousMap.evalCLM (R := 𝕜) ⟨α, Ordinal.zero_le _, le_rfl⟩).smulRight f

@[simp] theorem ordinalOperatorMatrix_endpointRankOne (α : Ordinal.{u})
    (f : OrdinalC 𝕜 α) (x : OrdinalInterval α) :
    ordinalOperatorMatrix α (ordinalEndpointRankOne α f) x ⟨α, Ordinal.zero_le _, le_rfl⟩ = f x := by
  simp [ordinalEndpointRankOne, ordinalOperatorMatrix_rankOne]

theorem ordinalEndpointRankOne_mem_loyWillisSubspace (f : OrdinalC 𝕜 c.ord) :
    ordinalEndpointRankOne c.ord f ∈ loyWillisSubspace hc hu := by
  apply mem_loyWillisSubspace_of_continuous_endpointColumn hc hu
  simpa only [ordinalOperatorMatrix_endpointRankOne] using f.continuous

theorem loyWillis_sub_endpointRankOne_zero_column
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) (x : OrdinalInterval c.ord) :
    ordinalOperatorMatrix c.ord
      (T - ordinalEndpointRankOne c.ord (loyWillisEndpointColumn hc hu T hT))
        x ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = 0 := by
  simp

theorem loyWillis_sub_endpointRankOne_mem
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) :
    T - ordinalEndpointRankOne c.ord (loyWillisEndpointColumn hc hu T hT) ∈
      loyWillisSubspace (𝕜 := 𝕜) hc hu := by
  exact (loyWillisSubspace (𝕜 := 𝕜) hc hu).sub_mem hT
    (ordinalEndpointRankOne_mem_loyWillisSubspace (𝕜 := 𝕜) hc hu
      (loyWillisEndpointColumn (𝕜 := 𝕜) hc hu T hT))

end JLMS
