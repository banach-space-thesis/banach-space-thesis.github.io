import ThesisCommon.Analysis.GowersMaureyStrictlySingularSubspaces
import ThesisCommon.Analysis.StrictlySingularOperatorCalculus

/-! The genuinely strictly singular operators form a norm-closed two-sided
ideal on the actual shift space. Additivity follows from the proved
infinite-dimensional small-subspace construction; no ideal axiom or
operator-representation hypothesis is used. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingular_add (D : ConstructionData 𝕜)
    {S T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (hS : IsStrictlySingularOperator S) (hT : IsStrictlySingularOperator T) :
    IsStrictlySingularOperator (S+T) := by
  intro E hEbound
  obtain ⟨c,hc,hb⟩ := hEbound
  by_contra hE
  obtain ⟨F,hFE,hF,hsmall⟩ := strictlySingular_exists_infinite_small_subspace D S hS E hE
    (show 0 < c/2 by positivity)
  apply hF
  apply hT F
  refine ⟨c/2, by positivity, ?_⟩
  intro x
  change (c/2) * ‖x.val‖ ≤ ‖T x.val‖
  have hh := hb ⟨x.val,hFE x.property⟩
  change c * ‖x.val‖ ≤ ‖S x.val+T x.val‖ at hh
  have hu := hh.trans (norm_add_le (S x.val) (T x.val))
  have hs := hsmall x
  nlinarith

theorem strictlySingular_sub (D : ConstructionData 𝕜)
    {S T : ShiftSpace D →L[𝕜] ShiftSpace D}
    (hS : IsStrictlySingularOperator S) (hT : IsStrictlySingularOperator T) :
    IsStrictlySingularOperator (S-T) := by
  simpa only [sub_eq_add_neg] using strictlySingular_add D hS hT.neg

theorem strictlySingular_add_iff_of_right (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    {S : ShiftSpace D →L[𝕜] ShiftSpace D} (hS : IsStrictlySingularOperator S) :
    IsStrictlySingularOperator (T+S) ↔ IsStrictlySingularOperator T := by
  constructor
  · intro h
    simpa only [add_sub_cancel_right] using strictlySingular_sub D h hS
  · intro h
    exact strictlySingular_add D h hS

def strictlySingularIdeal (D : ConstructionData 𝕜) :
    TwoSidedIdeal (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  TwoSidedIdeal.mk' {T | IsStrictlySingularOperator T}
    IsStrictlySingularOperator.zero
    (fun hS hT => strictlySingular_add D hS hT)
    (fun hT => hT.neg)
    (fun {S _} hT => hT.comp_left S)
    (fun {_ T} hS => hS.comp_right T)

@[simp] theorem mem_strictlySingularIdeal (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    T ∈ strictlySingularIdeal D ↔ IsStrictlySingularOperator T := by
  simp only [strictlySingularIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

instance strictlySingularIdeal_isClosed (D : ConstructionData 𝕜) :
    IsClosed (strictlySingularIdeal D : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) := by
  have he : (strictlySingularIdeal D : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) =
      {T | IsStrictlySingularOperator T} := by
    ext T
    exact mem_strictlySingularIdeal D T
  rw [he]
  exact isClosed_setOf_isStrictlySingularOperator

instance operatorIdealSubmodule_strictlySingularIdeal_isClosed (D : ConstructionData 𝕜) :
    IsClosed (operatorIdealSubmodule (strictlySingularIdeal D) :
      Set (ShiftSpace D →L[𝕜] ShiftSpace D)) := by
  change IsClosed (strictlySingularIdeal D : Set (ShiftSpace D →L[𝕜] ShiftSpace D))
  infer_instance

end ThesisCommon.GowersMaurey
