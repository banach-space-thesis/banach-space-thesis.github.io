import JLMS.LoyWillisIdeal
import JLMS.OrdinalMatrixAlgebra
import JLMS.CodimensionOneContinuity

/-!
# Ogden Section 4: the closed codimension-one ideal

The identity has jump one, so each operator is the sum of a jump-zero
operator and a scalar multiple of the identity. Continuous endpoint columns
give the left ideal law through matrix multiplication. The decomposition
then gives the right ideal law, exactly as in the article.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {c : Cardinal.{u}} (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)

local instance loyWillisAlgebraOperatorGroup : NormedAddCommGroup
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance
local instance loyWillisAlgebraOperatorSpace : NormedSpace 𝕜
    (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) := inferInstance

@[simp] theorem initialEndpointColumnLimit_id :
    initialEndpointColumnLimit hc hu (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)) = 0 := by
  have hpos : 0 < c.ord := by
    have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
    obtain ⟨β, hβ⟩ := (Ordinal.aleph0_le_cof.mp hcf.le).nonempty_Iio
    exact (Ordinal.zero_le β).trans_lt hβ
  apply initialEndpointColumnLimit_eq_of_tail hc hu _ hpos
  intro x _ hx
  have hne : x ≠ ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
    intro he
    exact (ne_of_lt hx) (congrArg Subtype.val he)
  simp only [ordinalOperatorMatrix_id, if_neg hne]

@[simp] theorem initialEndpointJump_id :
    initialEndpointJump (𝕜 := 𝕜) hc hu (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)) = 1 := by
  simp [initialEndpointJump_apply, initialEndpointColumnLimit_id,
    ordinalEndpointCoefficient_apply, ordinalOperatorMatrix_id]

theorem sub_jump_smul_id_mem_loyWillisSubspace
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) :
    T - initialEndpointJump (𝕜 := 𝕜) hc hu T •
      ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord) ∈ loyWillisSubspace hc hu := by
  rw [loyWillisSubspace, LinearMap.mem_ker]
  change initialEndpointJump (𝕜 := 𝕜) hc hu
    (T - initialEndpointJump (𝕜 := 𝕜) hc hu T • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)) = 0
  rw [map_sub, map_smul, initialEndpointJump_id]
  simp

theorem loyWillisSubspace_mul_left
    (S T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hT : T ∈ loyWillisSubspace hc hu) : S * T ∈ loyWillisSubspace hc hu := by
  let f : OrdinalC 𝕜 c.ord := ⟨_, continuous_endpointColumn_of_mem_loyWillisSubspace hc hu T hT⟩
  apply mem_loyWillisSubspace_of_continuous_endpointColumn hc hu
  have he : (fun x => ordinalOperatorMatrix c.ord (S * T) x
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩) = S f := by
    funext x
    exact ordinalOperatorMatrix_comp_column c.ord S T _ f (fun _ => rfl) x
  rw [he]
  exact (S f).continuous

theorem loyWillisSubspace_mul_right
    (S T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord)
    (hS : S ∈ loyWillisSubspace hc hu) : S * T ∈ loyWillisSubspace hc hu := by
  let a := initialEndpointJump (𝕜 := 𝕜) hc hu T
  let U := T - a • ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)
  have hU : U ∈ loyWillisSubspace hc hu := sub_jump_smul_id_mem_loyWillisSubspace hc hu T
  have hSU := loyWillisSubspace_mul_left hc hu S U hU
  have hscalar := (loyWillisSubspace hc hu).smul_mem a hS
  have he : S * T = S * U + a • S := by
    ext f x
    change S (T f) x = S (T f - a • f) x + a * S f x
    rw [map_sub, map_smul]
    change S (T f) x = (S (T f) x - a * S f x) + a * S f x
    exact (sub_add_cancel _ _).symm
  rw [he]
  exact (loyWillisSubspace hc hu).add_mem hSU hscalar

theorem continuous_of_continuous_on_loyWillisSubspace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : (OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) →ₗ[𝕜] F)
    (hf : Continuous (f.comp (loyWillisSubspace hc hu).subtype)) : Continuous f :=
  continuous_of_continuous_on_codimensionOne_kernel f (initialEndpointJump hc hu)
    (ContinuousLinearMap.id 𝕜 (OrdinalC 𝕜 c.ord)) (initialEndpointJump_id hc hu) hf

end JLMS
