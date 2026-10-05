import JLMS.OrdinalSpaceSplit
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Kislyakov's endpoint-zero identification

For infinite α, C[0,α] is isomorphic to the subspace of functions vanishing
at α (Kislyakov, 1975, equation (1.1)). Split off the isolated point 0.
The forward map stores f(α) at that point and puts f−f(α) on the shifted
copy (0,α]. This proof also gives a reusable kernel lemma for a stable split.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance endpointZeroFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointZeroFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance

def ordinalIntervalCongr {α β : Ordinal.{u}} (h : α = β) :
    OrdinalInterval α ≃ₜ OrdinalInterval β where
  toFun x := ⟨x.val, by simpa only [← h] using x.property⟩
  invFun x := ⟨x.val, by simpa only [h] using x.property⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def ordinalSpaceCongrIsometry {α β : Ordinal.{u}} (h : α = β) :
    OrdinalC 𝕜 α ≃ₗᵢ[𝕜] OrdinalC 𝕜 β :=
  continuousMapDomainIsometry (ordinalIntervalCongr h.symm)

def ordinalZeroEvaluation : OrdinalC 𝕜 (0 : Ordinal.{u}) ≃L[𝕜] 𝕜 where
  toFun f := f ⟨0, le_rfl, le_rfl⟩
  invFun c := ContinuousMap.const _ c
  left_inv f := by
    ext x
    have hx : x = (⟨0, le_rfl, le_rfl⟩ : OrdinalInterval (0 : Ordinal.{u})) :=
      Subtype.ext (le_antisymm x.property.2 x.property.1)
    simp only [hx, ContinuousMap.const_apply]
  right_inv c := rfl
  map_add' f g := rfl
  map_smul' c f := rfl
  continuous_toFun := (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜) _).continuous
  continuous_invFun := (ContinuousLinearMap.const (R := 𝕜) _).continuous

theorem exists_ordinalIsolatedSplit (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    ∃ e : OrdinalC 𝕜 α ≃L[𝕜] 𝕜 × OrdinalC 𝕜 α,
      ∀ f, (e f).2 ⟨α, Ordinal.zero_le _, le_rfl⟩ =
        f ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
  refine ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) (zero_add α).symm).toContinuousLinearEquiv.trans
    ((ordinalSpaceAddIsometry (𝕜 := 𝕜) 0 α hα).toContinuousLinearEquiv.trans
      (ordinalZeroEvaluation.prodCongr (ContinuousLinearEquiv.refl 𝕜 _))), ?_⟩
  intro f
  change f ((ordinalIntervalCongr (zero_add α))
    (ordinalSplitRight 0 α hα ⟨α, Ordinal.zero_le _, le_rfl⟩)) = _
  congr 1
  apply Subtype.ext
  change (0 + 1) + α = α
  simp only [zero_add, Ordinal.one_add_of_omega0_le hα]

/-- A split preserving the functional on its second coordinate absorbs its kernel. -/
def kernelEquivOfStableSplit {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (χ : E →L[𝕜] 𝕜) (v : E) (hv : χ v = 1)
    (e : E ≃L[𝕜] 𝕜 × E) (he : ∀ x, χ (e x).2 = χ x) : E ≃L[𝕜] LinearMap.ker χ := by
  let L : E →L[𝕜] E := e.symm.toContinuousLinearMap.comp
    (χ.prod (ContinuousLinearMap.id 𝕜 E - χ.smulRight v))
  have hL (x : E) : L x ∈ LinearMap.ker χ := by
    change χ (L x) = 0
    rw [← he (L x)]
    simp [L, hv]
  let F : E →L[𝕜] LinearMap.ker χ := L.codRestrict (LinearMap.ker χ) hL
  let H : E →L[𝕜] E :=
    ((ContinuousLinearMap.snd 𝕜 𝕜 E) +
      (ContinuousLinearMap.fst 𝕜 𝕜 E).smulRight v).comp e.toContinuousLinearMap
  let G : LinearMap.ker χ →L[𝕜] E := H.comp (LinearMap.ker χ).subtypeL
  apply ContinuousLinearEquiv.equivOfInverse F G
  · intro x
    change H (L x) = x
    simp [H, L]
  · intro x
    apply Subtype.ext
    change L (H x.val) = x.val
    have hx : χ x.val = 0 := x.property
    have hχ : χ (H x.val) = (e x.val).1 := by
      simp [H, he x.val, hx, hv]
    apply e.injective
    change e (e.symm (χ (H x.val), H x.val - χ (H x.val) • v)) = e x.val
    rw [e.apply_symm_apply, hχ]
    apply Prod.ext
    · rfl
    · change (e x.val).2 + (e x.val).1 • v - (e x.val).1 • v = (e x.val).2
      exact add_sub_cancel_right _ _

/-- Continuous functions vanishing at the ordinal endpoint. -/
def ordinalEndpointZero (𝕜 : Type*) [RCLike 𝕜] (α : Ordinal.{u}) :
    Submodule 𝕜 (OrdinalC 𝕜 α) :=
  LinearMap.ker (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜)
    (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α))

/-- Kislyakov (1.1), with the endpoint-zero space constructed as the actual kernel. -/
def ordinalSpaceEndpointZeroEquiv (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    OrdinalC 𝕜 α ≃L[𝕜] ordinalEndpointZero 𝕜 α := by
  let e := Classical.choose (exists_ordinalIsolatedSplit (𝕜 := 𝕜) α hα)
  have he := Classical.choose_spec (exists_ordinalIsolatedSplit (𝕜 := 𝕜) α hα)
  let χ : OrdinalC 𝕜 α →L[𝕜] 𝕜 := ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜)
    (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α)
  let v : OrdinalC 𝕜 α := ContinuousMap.const _ 1
  exact kernelEquivOfStableSplit (𝕜 := 𝕜) (E := OrdinalC 𝕜 α) χ v rfl e he

end JLMS
