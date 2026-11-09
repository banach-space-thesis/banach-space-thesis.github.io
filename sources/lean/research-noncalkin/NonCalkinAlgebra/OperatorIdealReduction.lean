import NonCalkinAlgebra.OperatorIdealMultiplication
import NonCalkinAlgebra.MatrixObstruction

noncomputable section
set_option autoImplicit false
open TopologicalSpace
open scoped BigOperators
namespace NonCalkinAlgebra
open SurveyStatements.P2
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem separable_closed_range_iff (T : BoundedOperators X) :
    IsSeparable (closure (Set.range T)) ↔ IsSeparable (Set.range T) :=
  ⟨fun h => h.mono subset_closure, fun h => h.closure⟩

/-- In the zero separable-range quotient case, either convention equals K(X).
This permits the compact matrix-unit obstruction to cover both conventions.
-/
theorem operatorIdeal_eq_compact_of_separableRange
    (convention : QuotientConvention)
    (hsep : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → T ∈ operatorIdeal X convention) :
    operatorIdeal X convention = CompactOperators X := by
  apply le_antisymm (operatorIdeal_le_compact X convention)
  intro T hT
  exact hsep T (compactOperator_range_isSeparable hT)

theorem compact_of_separableRange_in_operatorIdeal
    (convention : QuotientConvention)
    (hsep : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → T ∈ operatorIdeal X convention)
    (T : BoundedOperators X) (hT : IsSeparable (Set.range T)) :
    IsCompactOperator T :=
  operatorIdeal_le_compact X convention (hsep T hT)

/-- Proposition 4.3 under either fixed quotient convention, after the canonical
identification J(X)=K(X) forced by its own separable-range hypothesis.
-/
theorem controlled_matrix_units_impossible_of_separableRange
    (convention : QuotientConvention)
    (hsep : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → T ∈ operatorIdeal X convention)
    (e : ℕ → ℕ → Calkin X)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (hne : e 0 0 ≠ 0)
    (Cr Cc : ℝ) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc)
    (hrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖∑ j : F, a j • e 0 j.val‖ ≤ Cr * ‖a‖)
    (hcolumn : ∀ i, ‖e i 0‖ ≤ Cc) : False :=
  controlled_calkin_matrix_units_impossible X
    (compact_of_separableRange_in_operatorIdeal X convention hsep)
    e hmul hne Cr Cc hCr hCc hrow hcolumn

end NonCalkinAlgebra
