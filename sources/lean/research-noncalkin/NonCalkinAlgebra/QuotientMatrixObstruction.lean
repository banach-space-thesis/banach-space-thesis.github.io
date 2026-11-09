import NonCalkinAlgebra.OperatorIdealReduction
import NonCalkinAlgebra.QuotientAlgebra

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2 Set TopologicalSpace
universe v

def quotientIsometryOfEq {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N M : Submodule ℂ E) (h : N = M) : (E ⧸ N) ≃ₗᵢ[ℂ] E ⧸ M := by
  subst M
  exact LinearIsometryEquiv.refl ℂ (E ⧸ N)

@[simp] theorem quotientIsometryOfEq_mk {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N M : Submodule ℂ E) (h : N = M) (x : E) :
    quotientIsometryOfEq N M h (N.mkQ x) = M.mkQ x := by
  subst M
  rfl

variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem quotientIsometryOfEq_mul (convention : QuotientConvention)
    (h : operatorIdeal X convention = CompactOperators X)
    (a b : OperatorQuotient X convention) :
    quotientIsometryOfEq _ _ h (a * b) =
      quotientIsometryOfEq _ _ h a * quotientIsometryOfEq _ _ h b := by
  refine Quotient.inductionOn₂ a b ?_
  intro S T
  change quotientIsometryOfEq _ _ h (operatorQuotientMap X convention S *
    operatorQuotientMap X convention T) =
      quotientIsometryOfEq _ _ h ((operatorIdeal X convention).mkQ S) *
      quotientIsometryOfEq _ _ h ((operatorIdeal X convention).mkQ T)
  rw [← operatorQuotientMap_mul]
  change quotientIsometryOfEq _ _ h ((operatorIdeal X convention).mkQ (S * T)) = _
  rw [quotientIsometryOfEq_mk, quotientIsometryOfEq_mk, quotientIsometryOfEq_mk]
  exact calkinQuotient_mul X S T

/-- Proposition 4.3 literally in either quotient algebra. The hypothesis
forces its ideal to equal K(X); the isometric identification is proved above. -/
theorem controlled_quotient_matrix_units_impossible
    (convention : QuotientConvention)
    (hsep : ∀ T : BoundedOperators X,
      IsSeparable (Set.range T) → T ∈ operatorIdeal X convention)
    (e : ℕ → ℕ → OperatorQuotient X convention)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (hne : e 0 0 ≠ 0)
    (Cr Cc : ℝ) (hCr : 0 ≤ Cr) (hCc : 0 ≤ Cc)
    (hrow : ∀ (F : Finset ℕ) (a : F → ℂ),
      ‖∑ j : F, a j • e 0 j.val‖ ≤ Cr * ‖a‖)
    (hcolumn : ∀ i, ‖e i 0‖ ≤ Cc) : False := by
  classical
  let h := operatorIdeal_eq_compact_of_separableRange X convention hsep
  let f := quotientIsometryOfEq _ _ h
  let E : ℕ → ℕ → Calkin X := fun i j => f (e i j)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    change f (e i j) * f (e k l) = _
    rw [← quotientIsometryOfEq_mul X convention h, hmul]
    split_ifs <;> simp only [map_zero, E] <;> rfl
  have hEne : E 0 0 ≠ 0 := by
    intro he
    apply hne
    apply f.injective
    simpa only [map_zero] using he
  have hErow (F : Finset ℕ) (a : F → ℂ) :
      ‖∑ j : F, a j • E 0 j.val‖ ≤ Cr * ‖a‖ := by
    have heq : (∑ j : F, a j • E 0 j.val) = f (∑ j : F, a j • e 0 j.val) := by
      simp only [map_sum, map_smul, E]
    rw [heq, f.norm_map]
    exact hrow F a
  have hEcolumn (i : ℕ) : ‖E i 0‖ ≤ Cc := by
    change ‖f (e i 0)‖ ≤ Cc
    rw [f.norm_map]
    exact hcolumn i
  exact controlled_calkin_matrix_units_impossible X
    (compact_of_separableRange_in_operatorIdeal X convention hsep)
    E hE hEne Cr Cc hCr hCc hErow hEcolumn

end NonCalkinAlgebra
