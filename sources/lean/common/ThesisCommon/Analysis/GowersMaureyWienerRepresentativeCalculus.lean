import ThesisCommon.Analysis.GowersMaureyWienerRepresentative
import ThesisCommon.Analysis.GowersMaureyLaurentProductDefect

/-! Values of the actual conditional Wiener representative on spreads,
the identity, and products of Laurent operators. The approximation premise
remains explicit throughout; no general operator product assertion is used. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem wienerRepresentative_integerShift (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (d : ℤ) :
    wienerRepresentative D happrox (integerShift D d) = lp.single 1 d 1 := by
  rw [← laurentOperator_single D d, wienerRepresentative_laurentOperator]

theorem wienerRepresentative_completedSpread (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (m n : ℕ) :
    wienerRepresentative D happrox (completedSpread D m n) =
      lp.single 1 ((n : ℤ)-m) 1 := by
  apply wienerRepresentative_eq_of_error_zero D happrox
  rw [laurentOperator_single]
  exact spaceOperatorSeminorm_spread_sub_integerShift D m n

theorem wienerRepresentative_id (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T) :
    wienerRepresentative D happrox (ContinuousLinearMap.id 𝕜 (ShiftSpace D)) =
      lp.single 1 0 1 := by
  apply wienerRepresentative_eq_of_error_zero D happrox
  rw [laurentOperator_single]
  apply spaceOperatorSeminorm_eq_zero_of_basis_tail D _ 0
  intro j _
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    integerShift_basis_tail D 0 j (by simp)]
  simp

theorem wienerRepresentative_laurent_comp (D : ConstructionData 𝕜)
    (happrox : ∀ T : ShiftSpace D →L[𝕜] ShiftSpace D, IsFiniteSpreadApproximable D T)
    (a b : WienerSequences 𝕜) :
    wienerRepresentative D happrox ((laurentOperator D a).comp (laurentOperator D b)) =
      wienerConvolution a b :=
  wienerRepresentative_eq_of_error_zero D happrox
    (spaceOperatorSeminorm_laurent_product_defect D a b)

end ThesisCommon.GowersMaurey
