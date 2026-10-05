import JLMS.InitialEndpointColumnLimit
import JLMS.OrdinalConstantTailContinuity

/-!
# Ogden Section 4: the endpoint-column jump and the Loy--Willis subspace

For a regular uncountable initial ordinal κ, every endpoint column has an
actual constant tail below κ. Subtracting that tail value from Tκκ defines
a bounded linear functional. Its closed kernel is exactly the operators
whose endpoint column is continuous, as in Ogden's definition of M.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)

local instance loyWillisOperatorGroup : NormedAddCommGroup
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance
local instance loyWillisOperatorSpace : NormedSpace 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance

def initialEndpointJump :
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →L[𝕜] 𝕜 :=
  ordinalEndpointCoefficient c.ord - initialEndpointColumnLimitCLM hc hu

@[simp] theorem initialEndpointJump_apply
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    initialEndpointJump (𝕜 := 𝕜) hc hu T = ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord T -
      initialEndpointColumnLimit hc hu T := rfl

theorem norm_initialEndpointJump_le : ‖initialEndpointJump (𝕜 := 𝕜) hc hu‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro T
  have hentry : ‖ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord T‖ ≤ ‖T‖ :=
    (lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0)
      (ordinalOperatorRow c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)
        ⟨c.ord, Ordinal.zero_le _, le_rfl⟩).trans
          (norm_ordinalOperatorRow_le c.ord T _)
  calc
    ‖initialEndpointJump (𝕜 := 𝕜) hc hu T‖ ≤ ‖ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord T‖ +
        ‖initialEndpointColumnLimit hc hu T‖ := norm_sub_le _ _
    _ ≤ ‖T‖ + ‖T‖ := add_le_add hentry (norm_initialEndpointColumnLimit_le hc hu T)
    _ = 2 * ‖T‖ := (two_mul _).symm

def loyWillisSubspace : Submodule 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :=
  LinearMap.ker (initialEndpointJump (𝕜 := 𝕜) hc hu)

theorem mem_loyWillisSubspace_iff
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    T ∈ loyWillisSubspace hc hu ↔
      initialEndpointColumnLimit hc hu T = ordinalEndpointCoefficient (𝕜 := 𝕜) c.ord T := by
  rw [loyWillisSubspace, LinearMap.mem_ker]
  change initialEndpointJump (𝕜 := 𝕜) hc hu T = 0 ↔ _
  rw [initialEndpointJump_apply, sub_eq_zero, eq_comm]

theorem isClosed_loyWillisSubspace :
    IsClosed (loyWillisSubspace (𝕜 := 𝕜) hc hu :
      Set (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)) := by
  exact isClosed_eq (initialEndpointJump (𝕜 := 𝕜) hc hu).continuous continuous_const

theorem continuous_endpointColumn_of_mem_loyWillisSubspace
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) :
    Continuous (fun x => ordinalOperatorMatrix c.ord T x
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.val < c.ord
  · exact continuousAt_initialOrdinalEndpointColumn hc hu T x hx
  · have hxe : x = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
      Subtype.ext (le_antisymm x.property.2 (le_of_not_gt hx))
    subst x
    obtain ⟨β, hβ, ht⟩ := exists_initialEndpointColumnLimit_tail hc hu T
    apply continuousAt_of_ordinal_constant_tail hβ
    intro y hy
    by_cases hyα : y.val < c.ord
    · rw [ht y hy hyα, (mem_loyWillisSubspace_iff hc hu T).mp hT]
      rfl
    · have hye : y = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
        Subtype.ext (le_antisymm y.property.2 (le_of_not_gt hyα))
      rw [hye]

theorem mem_loyWillisSubspace_of_continuous_endpointColumn
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : Continuous (fun x => ordinalOperatorMatrix c.ord T x
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩)) : T ∈ loyWillisSubspace hc hu := by
  let f : OrdinalC 𝕜 c.ord := ⟨_, hT⟩
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  obtain ⟨β, hβ, ht⟩ := exists_constant_ordinalC_tail hcf f
  apply (mem_loyWillisSubspace_iff hc hu T).mpr
  apply initialEndpointColumnLimit_eq_of_tail hc hu T hβ
  intro x hx _
  exact ht x hx

theorem mem_loyWillisSubspace_iff_continuous_endpointColumn
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    T ∈ loyWillisSubspace hc hu ↔ Continuous (fun x => ordinalOperatorMatrix c.ord T x
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) :=
  ⟨continuous_endpointColumn_of_mem_loyWillisSubspace hc hu T,
    mem_loyWillisSubspace_of_continuous_endpointColumn hc hu T⟩

end JLMS
