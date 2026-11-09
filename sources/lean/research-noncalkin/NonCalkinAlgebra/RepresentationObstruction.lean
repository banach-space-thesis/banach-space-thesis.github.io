import NonCalkinAlgebra.ConstructedBanachAlgebra
import NonCalkinAlgebra.QuotientMatrixObstruction

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set TopologicalSpace
universe u v

namespace OperatorQuotientIso
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {convention : QuotientConvention}
  {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

theorem map_mul (e : OperatorQuotientIso X convention A)
    (a b : OperatorQuotient X convention) :
    e.toContinuousLinearEquiv (a * b) =
      e.toContinuousLinearEquiv a * e.toContinuousLinearEquiv b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  exact e.map_mul_representatives S T

theorem symm_map_mul (e : OperatorQuotientIso X convention A) (a b : A) :
    e.toContinuousLinearEquiv.symm (a * b) =
      e.toContinuousLinearEquiv.symm a * e.toContinuousLinearEquiv.symm b := by
  apply e.toContinuousLinearEquiv.injective
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (e.map_mul (e.toContinuousLinearEquiv.symm a) (e.toContinuousLinearEquiv.symm b)).symm

end OperatorQuotientIso

variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]
  [NormOneClass D] [Nontrivial D]
  (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The final, zero-separable-range-ideal branch of the proof of Theorem 1.1.
This conclusion is proved under its explicit operator-ideal hypothesis;
it is not an unconditional nonrepresentation theorem for arbitrary X. -/
theorem not_representable_of_separableRange_in_operatorIdeal
    (convention : QuotientConvention)
    (hsep : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → T ∈ operatorIdeal X convention) :
    ¬ Nonempty (OperatorQuotientIso X convention (matrixAlgebra D)) := by
  rintro ⟨iso⟩
  let f := iso.toContinuousLinearEquiv.symm
  let e : ℕ → ℕ → OperatorQuotient X convention :=
    fun i j => f (canonicalMatrixUnit D i j)
  let C : ℝ := ‖f.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg f.toContinuousLinearMap
  have hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0 := by
    intro i j k l
    change f (canonicalMatrixUnit D i j) * f (canonicalMatrixUnit D k l) = _
    rw [← iso.symm_map_mul, canonicalMatrixUnit_mul]
    split_ifs <;> simp only [map_zero, e] <;> rfl
  have hne : e 0 0 ≠ 0 := by
    intro hzero
    apply canonicalMatrixUnit_ne_zero D 0 0
    apply f.injective
    simpa only [map_zero] using hzero
  have hrow (F : Finset ℕ) (a : F → ℂ) :
      ‖∑ j : F, a j • e 0 j.val‖ ≤ C * ‖a‖ := by
    have heq : (∑ j : F, a j • e 0 j.val) =
        f (∑ j : F, a j • canonicalMatrixUnit D 0 j.val) := by
      simp only [map_sum, map_smul, e]
    rw [heq]
    exact (f.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (canonicalMatrixUnit_row_le D F a) hC)
  have hcolumn (i : ℕ) : ‖e i 0‖ ≤ C := by
    calc
      ‖e i 0‖ ≤ C * ‖canonicalMatrixUnit D i 0‖ := f.toContinuousLinearMap.le_opNorm _
      _ = C := by rw [norm_canonicalMatrixUnit, mul_one]
  exact controlled_quotient_matrix_units_impossible X convention hsep
    e hmul hne C C hC hC hrow hcolumn

/-- The finite-dimensional case of the main nonrepresentation argument,
for either quotient convention. -/
theorem not_representable_of_finiteDimensional [FiniteDimensional ℂ X]
    (convention : QuotientConvention) :
    ¬ Nonempty (OperatorQuotientIso X convention (matrixAlgebra D)) := by
  apply not_representable_of_separableRange_in_operatorIdeal D X convention
  intro T hT
  have hfinite : HasFiniteRank X T := by
    change FiniteDimensional ℂ (LinearMap.range T.toLinearMap)
    infer_instance
  cases convention
  · exact finiteRank_le_approximable X hfinite
  · exact finiteRank_isCompact X hfinite

end NonCalkinAlgebra
