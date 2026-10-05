import ThesisCommon.Analysis.GowersMaureySeminormSpreadComposition
import ThesisCommon.Analysis.GowersMaureySeminormLeftComposition
import ThesisCommon.Analysis.GowersMaureyWienerCompletion

/-! The actual zero-seminorm kernel is a right ideal whenever the right
factor admits the finite-spread approximation asserted in the source.
The approximation premise is explicit and is not added to construction data. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spaceOperatorSeminorm_comp_eq_zero_of_left_of_approximable
    (D : ConstructionData 𝕜) (T S : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hT : spaceOperatorSeminorm D T = 0) (hS : IsFiniteSpreadApproximable D S) :
    spaceOperatorSeminorm D (T.comp S) = 0 := by
  obtain ⟨a, ha, _⟩ := hS.exists_unique_wiener_representative
  have he : T.comp S = T.comp (laurentOperator D a) + T.comp (S - laurentOperator D a) := by
    rw [ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  apply le_antisymm _ (apply_nonneg _ _)
  exact (map_add_le_add (spaceOperatorSeminorm D) _ _).trans_eq (by
    rw [spaceOperatorSeminorm_comp_laurent_eq_zero D T a hT,
      spaceOperatorSeminorm_comp_eq_zero_of_right D T _ ha, zero_add])

theorem spaceOperatorSeminorm_comp_eq_zero_of_left
    (D : ConstructionData 𝕜)
    (happrox : ∀ S : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D S)
    (T S : ShiftSpace D →L[𝕜] ShiftSpace D) (hT : spaceOperatorSeminorm D T = 0) :
    spaceOperatorSeminorm D (T.comp S) = 0 :=
  spaceOperatorSeminorm_comp_eq_zero_of_left_of_approximable D T S hT (happrox S)

end ThesisCommon.GowersMaurey
