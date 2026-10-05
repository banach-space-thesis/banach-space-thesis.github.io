import ThesisCommon.Analysis.GowersMaureyWienerRepresentativeCalculus
import ThesisCommon.Analysis.GowersMaureySeminormRightComposition

/-! Literal convolution multiplication for the actual Wiener representative,
conditional only on the explicitly stated finite-spread approximation theorem.
The boundary defect of unilateral Laurent composition is removed in the
seminorm kernel, rather than incorrectly asserted to vanish as an operator. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wienerRepresentative_comp (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    wienerRepresentative D happrox (S.comp T) =
      wienerConvolution (wienerRepresentative D happrox S) (wienerRepresentative D happrox T) := by
  let a := wienerRepresentative D happrox S
  let b := wienerRepresentative D happrox T
  have h₁ : spaceOperatorSeminorm D ((S-laurentOperator D a).comp T) = 0 :=
    spaceOperatorSeminorm_comp_eq_zero_of_left D happrox _ T
      (wienerRepresentative_spec D happrox S)
  have h₂ : spaceOperatorSeminorm D ((laurentOperator D a).comp (T-laurentOperator D b)) = 0 :=
    spaceOperatorSeminorm_comp_eq_zero_of_right D _ _
      (wienerRepresentative_spec D happrox T)
  have h₃ := spaceOperatorSeminorm_laurent_product_defect D a b
  have h₁₂ : spaceOperatorSeminorm D
      ((S-laurentOperator D a).comp T + (laurentOperator D a).comp (T-laurentOperator D b)) = 0 := by
    apply le_antisymm _ (apply_nonneg _ _)
    exact (map_add_le_add (spaceOperatorSeminorm D) _ _).trans_eq (by rw [h₁, h₂, zero_add])
  apply wienerRepresentative_eq_of_error_zero D happrox
  change spaceOperatorSeminorm D (S.comp T - laurentOperator D (wienerConvolution a b)) = 0
  have he : S.comp T - laurentOperator D (wienerConvolution a b) =
      ((S-laurentOperator D a).comp T + (laurentOperator D a).comp (T-laurentOperator D b)) +
        ((laurentOperator D a).comp (laurentOperator D b) -
          laurentOperator D (wienerConvolution a b)) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  apply le_antisymm _ (apply_nonneg _ _)
  exact (map_add_le_add (spaceOperatorSeminorm D) _ _).trans_eq (by rw [h₁₂, h₃, zero_add])

theorem spaceOperatorSeminorm_comp_eq_convolution_norm (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D (S.comp T) =
      ‖wienerConvolution (wienerRepresentative D happrox S) (wienerRepresentative D happrox T)‖ := by
  rw [← wienerRepresentative_norm D happrox (S.comp T), wienerRepresentative_comp]

theorem spaceOperatorSeminorm_comp_le (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D (S.comp T) ≤ spaceOperatorSeminorm D S * spaceOperatorSeminorm D T := by
  rw [spaceOperatorSeminorm_comp_eq_convolution_norm D happrox,
    ← wienerRepresentative_norm D happrox S, ← wienerRepresentative_norm D happrox T]
  exact norm_wienerConvolution_le _ _

theorem spaceOperatorSeminorm_commutator_zero (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D (S.comp T - T.comp S) = 0 := by
  apply (wienerRepresentative_eq_zero_iff D happrox _).mp
  rw [map_sub, wienerRepresentative_comp, wienerRepresentative_comp,
    wienerConvolution_comm (wienerRepresentative D happrox S), sub_self]

theorem isStrictlySingularOperator_commutator (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (S T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    IsStrictlySingularOperator (S.comp T - T.comp S) :=
  isStrictlySingularOperator_of_spaceOperatorSeminorm_zero D _
    (spaceOperatorSeminorm_commutator_zero D happrox S T)

end ThesisCommon.GowersMaurey
