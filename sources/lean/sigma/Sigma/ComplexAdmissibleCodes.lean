import Sigma.ComplexCoefficientEnumeration

/-! The two classes of admissible codes have genuine enumerations with family
support strictly below the stage. The opposite copy's infinity coefficient is
retained. The antisymmetric copy has zero infinity coefficient. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] Classical.decEq

def ComplexFullCodeAdmissible (side : Bool) (c : ComplexFullCoefficientRows) : Prop :=
  (∀ n, ‖c n‖ ≤ 1) ∧
  (∀ n k, c n (side,Sum.inl (k,false)) = -c n (side,Sum.inl (k,true))) ∧
  (∀ n i, c n (familyAtom side false i) = -c n (familyAtom side true i)) ∧
  (∀ n, c n (side,Sum.inr (Sum.inr ())) = 0) ∧
  ∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ ‖c n (side,Sum.inl (n,false))‖

def complexDefaultFullRows (side : Bool) : ComplexFullCoefficientRows := fun n =>
  lp.single 1 (side,Sum.inl (n,false)) (1/2 : ℂ) -
    lp.single 1 (side,Sum.inl (n,true)) (1/2 : ℂ)

theorem complexDefaultFullRows_admissible (side : Bool) : ComplexFullCodeAdmissible side (complexDefaultFullRows side) := by
  refine ⟨?_,?_,?_,?_,1/2,by norm_num,?_⟩
  · intro n
    apply (norm_sub_le _ _).trans
    rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal)),
      lp.norm_single (by norm_num : 0 < (1 : ENNReal))]
    norm_num
  · intro n k
    by_cases h : k = n
    · subst k
      norm_num [complexDefaultFullRows, lp.coeFn_sub, lp.single_apply, Pi.single_apply]
    · simp [complexDefaultFullRows, lp.single_apply, h]
  · intro n i
    simp [complexDefaultFullRows, lp.single_apply, familyAtom]
  · intro n
    simp [complexDefaultFullRows, lp.single_apply]
  · intro n
    norm_num [complexDefaultFullRows, lp.coeFn_sub, lp.single_apply, Pi.single_apply]

theorem complexFullCodeAdmissible_truncate (side : Bool) (a : ConstructionIndex) (c : ComplexFullCoefficientRows)
    (hc : ComplexFullCodeAdmissible side c) : ComplexFullCodeAdmissible side (complexTruncateCoefficients a c) := by
  refine ⟨fun n => (complexTruncateCoefficients_norm_le a c n).trans (hc.1 n), ?_, ?_, ?_, ?_⟩
  · intro n k
    rw [complexTruncateCoefficients_base,complexTruncateCoefficients_base]
    exact hc.2.1 n k
  · intro n i
    by_cases hi : i < a
    · simp only [complexTruncateCoefficients,JLMS.restrictL1_apply]
      rw [if_pos (show familyAtom side false i ∈ atomsBefore a from hi),
        if_pos (show familyAtom side true i ∈ atomsBefore a from hi)]
      exact hc.2.2.1 n i
    · rw [complexTruncateCoefficients_future _ _ _ _ _ _ (le_of_not_gt hi),
        complexTruncateCoefficients_future _ _ _ _ _ _ (le_of_not_gt hi),neg_zero]
  · intro n
    rw [complexTruncateCoefficients_infinity]
    exact hc.2.2.2.1 n
  · obtain ⟨b,hb,hdiag⟩ := hc.2.2.2.2
    exact ⟨b,hb,fun n => by rw [complexTruncateCoefficients_base]; exact hdiag n⟩

theorem complex_exists_admissible_code_enumeration (side : Bool) :
    ∃ e : ConstructionIndex → ComplexFullCoefficientRows,
      (∀ a, ComplexFullCodeAdmissible side (e a)) ∧
      (∀ a n s bit i, a ≤ i → e a n (familyAtom s bit i) = 0) ∧
      ∀ c, ComplexFullCodeAdmissible side c → ∃ a, e a = c :=
  complex_exists_supported_coefficient_enumeration (ComplexFullCodeAdmissible side)
    ⟨complexDefaultFullRows side,complexDefaultFullRows_admissible side⟩ (complexFullCodeAdmissible_truncate side)

end SigmaNonprimarity
