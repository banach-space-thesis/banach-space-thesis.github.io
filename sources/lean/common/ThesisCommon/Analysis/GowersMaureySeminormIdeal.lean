import ThesisCommon.Analysis.GowersMaureyWienerRepresentativeProduct

/-! The actual closed zero-seminorm subspace, and its two-sided ideal structure
under explicit finite-spread approximation. Only inclusion in the genuinely
strictly singular operators is asserted here; the converse is separate. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def spaceOperatorSeminormKernel (D : ConstructionData 𝕜) :
    Submodule 𝕜 (ShiftSpace D →L[𝕜] ShiftSpace D) where
  carrier := {T | spaceOperatorSeminorm D T = 0}
  zero_mem' := map_zero _
  add_mem' hS hT := by
    apply le_antisymm _ (apply_nonneg _ _)
    exact (map_add_le_add (spaceOperatorSeminorm D) _ _).trans_eq (by rw [hS, hT, zero_add])
  smul_mem' c T hT := by
    change spaceOperatorSeminorm D (c • T) = 0
    rw [map_smul_eq_mul, hT, mul_zero]

@[simp] theorem mem_spaceOperatorSeminormKernel (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    T ∈ spaceOperatorSeminormKernel D ↔ spaceOperatorSeminorm D T = 0 := Iff.rfl

instance spaceOperatorSeminormKernel_isClosed (D : ConstructionData 𝕜) :
    IsClosed (spaceOperatorSeminormKernel D : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) :=
  isClosed_eq (spaceOperatorSeminorm_continuous D) continuous_const

theorem spaceOperatorSeminormKernel_eq_ker_representative (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    spaceOperatorSeminormKernel D = LinearMap.ker (wienerRepresentative D happrox).toLinearMap := by
  ext T
  exact (wienerRepresentative_eq_zero_iff D happrox T).symm

def spaceOperatorSeminormIdeal (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    TwoSidedIdeal (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  TwoSidedIdeal.mk' (spaceOperatorSeminormKernel D)
    (spaceOperatorSeminormKernel D).zero_mem
    (spaceOperatorSeminormKernel D).add_mem
    (spaceOperatorSeminormKernel D).neg_mem
    (fun {S T} hT => spaceOperatorSeminorm_comp_eq_zero_of_right D S T hT)
    (fun {S T} hS => spaceOperatorSeminorm_comp_eq_zero_of_left D happrox S T hS)

@[simp] theorem mem_spaceOperatorSeminormIdeal (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    T ∈ spaceOperatorSeminormIdeal D happrox ↔ spaceOperatorSeminorm D T = 0 := by
  simp only [spaceOperatorSeminormIdeal, TwoSidedIdeal.mem_mk']
  rfl

theorem operatorIdealSubmodule_spaceOperatorSeminormIdeal (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    operatorIdealSubmodule (spaceOperatorSeminormIdeal D happrox) =
      spaceOperatorSeminormKernel D := by
  ext T
  simp only [mem_operatorIdealSubmodule, mem_spaceOperatorSeminormIdeal,
    mem_spaceOperatorSeminormKernel]

instance spaceOperatorSeminormIdeal_isClosed (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    IsClosed (spaceOperatorSeminormIdeal D happrox : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) := by
  have he : (spaceOperatorSeminormIdeal D happrox : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) =
      (spaceOperatorSeminormKernel D : Set (ShiftSpace D →L[𝕜] ShiftSpace D)) := by
    ext T
    exact mem_spaceOperatorSeminormIdeal D happrox T
  rw [he]
  infer_instance

instance operatorIdealSubmodule_spaceOperatorSeminormIdeal_isClosed (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    IsClosed (operatorIdealSubmodule (spaceOperatorSeminormIdeal D happrox) :
      Set (ShiftSpace D →L[𝕜] ShiftSpace D)) := by
  rw [operatorIdealSubmodule_spaceOperatorSeminormIdeal]
  infer_instance

theorem isStrictlySingularOperator_of_mem_spaceOperatorSeminormIdeal
    (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    {T : ShiftSpace D →L[𝕜] ShiftSpace D} (hT : T ∈ spaceOperatorSeminormIdeal D happrox) :
    IsStrictlySingularOperator T :=
  isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D T
    ((mem_spaceOperatorSeminormIdeal D happrox T).mp hT)

end ThesisCommon.GowersMaurey
