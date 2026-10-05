import ThesisCommon.Analysis.GowersMaureyStrictlySingularTailBound
import ThesisCommon.Analysis.StrictlySingularScalarKernel
import ThesisCommon.Analysis.FiniteCodimensionalLowerBound

/-! Actual finite-codimensional restrictions and closed range for nonzero
scalar perturbations of strictly singular operators on the constructed
space. No finite-codimension assertion about the range is assumed here. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def completedPrefixCoordinates (D : ConstructionData 𝕜) (N : ℕ) :
    ShiftSpace D →L[𝕜] (Fin N → 𝕜) :=
  ContinuousLinearMap.pi (fun i => completedCoordinate D i.val)

def completedCoordinateTail (D : ConstructionData 𝕜) (B : ℕ) :
    Submodule 𝕜 (ShiftSpace D) :=
  LinearMap.ker (completedPrefixCoordinates D (B+1)).toLinearMap

theorem mem_completedCoordinateTail_iff (D : ConstructionData 𝕜) (B : ℕ)
    (x : ShiftSpace D) :
    x ∈ completedCoordinateTail D B ↔ ∀ k ≤ B, completedCoordinate D k x = 0 := by
  change (fun i : Fin (B+1) => completedCoordinate D i.val x) = 0 ↔ _
  constructor
  · intro h k hk
    exact congrFun h ⟨k,by omega⟩
  · intro h
    funext i
    exact h i.val (by omega)

theorem completedCoordinateTail_isClosed (D : ConstructionData 𝕜) (B : ℕ) :
    IsClosed (completedCoordinateTail D B : Set (ShiftSpace D)) :=
  ContinuousLinearMap.isClosed_ker (completedPrefixCoordinates D (B+1))

theorem completedCoordinateTail_quotient_finiteDimensional
    (D : ConstructionData 𝕜) (B : ℕ) :
    FiniteDimensional 𝕜 (ShiftSpace D ⧸ completedCoordinateTail D B) := by
  let f := (completedPrefixCoordinates D (B+1)).toLinearMap
  exact FiniteDimensional.of_injective f.quotKerEquivRange.toLinearMap
    f.quotKerEquivRange.injective

theorem strictlySingular_finiteCodimensional_lower_bound
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hT : IsStrictlySingularOperator T) (a : 𝕜) (ha : a ≠ 0) :
    ∃ E : Submodule 𝕜 (ShiftSpace D), IsClosed (E : Set (ShiftSpace D)) ∧
      FiniteDimensional 𝕜 (ShiftSpace D ⧸ E) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x : E, c*‖x.val‖ ≤ ‖T x.val-a • x.val‖ := by
  obtain ⟨B,c,hc,hb⟩ := strictlySingular_completed_tail_lower_bound D T hT a ha
  refine ⟨completedCoordinateTail D B,completedCoordinateTail_isClosed D B,
    completedCoordinateTail_quotient_finiteDimensional D B,c,hc,?_⟩
  intro x
  exact hb x.val ((mem_completedCoordinateTail_iff D B x.val).mp x.property)

theorem strictlySingular_sub_smul_id_isClosed_range
    (D : ConstructionData 𝕜) (T : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hT : IsStrictlySingularOperator T) (a : 𝕜) (ha : a ≠ 0) :
    IsClosed (LinearMap.range
      (T-a • ContinuousLinearMap.id 𝕜 (ShiftSpace D)).toLinearMap : Set (ShiftSpace D)) := by
  obtain ⟨E,hE,hfd,c,hc,hb⟩ := strictlySingular_finiteCodimensional_lower_bound D T hT a ha
  letI := hfd
  exact ThesisCommon.ContinuousLinearMap.isClosed_range_of_finiteCodimensional_lower_bound
    (T-a • ContinuousLinearMap.id 𝕜 (ShiftSpace D)) E hE hc hb

theorem strictlySingular_id_sub_smul_finiteCodimensional_lower_bound
    (D : ConstructionData 𝕜) (S : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hS : IsStrictlySingularOperator S) (t : 𝕜) :
    ∃ E : Submodule 𝕜 (ShiftSpace D), IsClosed (E : Set (ShiftSpace D)) ∧
      FiniteDimensional 𝕜 (ShiftSpace D ⧸ E) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x : E, c*‖x.val‖ ≤ ‖x.val-t • S x.val‖ := by
  obtain ⟨E,hE,hfd,c,hc,hb⟩ :=
    strictlySingular_finiteCodimensional_lower_bound D (t • S) (hS.smul t) 1 one_ne_zero
  refine ⟨E,hE,hfd,c,hc,?_⟩
  intro x
  simpa only [ContinuousLinearMap.smul_apply, one_smul, norm_sub_rev] using hb x

theorem strictlySingular_id_sub_smul_isClosed_range
    (D : ConstructionData 𝕜) (S : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hS : IsStrictlySingularOperator S) (t : 𝕜) :
    IsClosed (LinearMap.range
      (ContinuousLinearMap.id 𝕜 (ShiftSpace D)-t • S).toLinearMap : Set (ShiftSpace D)) := by
  obtain ⟨E,hE,hfd,c,hc,hb⟩ :=
    strictlySingular_id_sub_smul_finiteCodimensional_lower_bound D S hS t
  letI := hfd
  exact ThesisCommon.ContinuousLinearMap.isClosed_range_of_finiteCodimensional_lower_bound
    (ContinuousLinearMap.id 𝕜 (ShiftSpace D)-t • S) E hE hc hb

end ThesisCommon.GowersMaurey
