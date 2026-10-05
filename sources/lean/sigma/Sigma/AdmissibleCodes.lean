import Sigma.CoefficientEnumeration

/-! The two classes of admissible codes have genuine enumerations with family
support strictly below the stage. The opposite copy's infinity coefficient is
retained. The antisymmetric copy has zero infinity coefficient. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] Classical.decEq

def FullCodeAdmissible (side : Bool) (c : FullCoefficientRows) : Prop :=
  (∀ n, ‖c n‖ ≤ 1) ∧
  (∀ n k, c n (side,Sum.inl (k,false)) = -c n (side,Sum.inl (k,true))) ∧
  (∀ n i, c n (familyAtom side false i) = -c n (familyAtom side true i)) ∧
  (∀ n, c n (side,Sum.inr (Sum.inr ())) = 0) ∧
  ∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ |c n (side,Sum.inl (n,false))|

def defaultFullRows (side : Bool) : FullCoefficientRows := fun n =>
  lp.single 1 (side,Sum.inl (n,false)) (1/2 : ℝ) -
    lp.single 1 (side,Sum.inl (n,true)) (1/2 : ℝ)

theorem defaultFullRows_admissible (side : Bool) : FullCodeAdmissible side (defaultFullRows side) := by
  refine ⟨?_,?_,?_,?_,1/2,by norm_num,?_⟩
  · intro n
    apply (norm_sub_le _ _).trans
    rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal)),
      lp.norm_single (by norm_num : 0 < (1 : ENNReal))]
    norm_num
  · intro n k
    by_cases h : k = n
    · subst k
      norm_num [defaultFullRows, lp.coeFn_sub, lp.single_apply, Pi.single_apply]
    · simp [defaultFullRows, lp.single_apply, h]
  · intro n i
    simp [defaultFullRows, lp.single_apply, familyAtom]
  · intro n
    simp [defaultFullRows, lp.single_apply]
  · intro n
    norm_num [defaultFullRows, lp.coeFn_sub, lp.single_apply, Pi.single_apply]

theorem fullCodeAdmissible_truncate (side : Bool) (a : ConstructionIndex) (c : FullCoefficientRows)
    (hc : FullCodeAdmissible side c) : FullCodeAdmissible side (truncateCoefficients a c) := by
  refine ⟨fun n => (truncateCoefficients_norm_le a c n).trans (hc.1 n), ?_, ?_, ?_, ?_⟩
  · intro n k
    rw [truncateCoefficients_base,truncateCoefficients_base]
    exact hc.2.1 n k
  · intro n i
    by_cases hi : i < a
    · simp only [truncateCoefficients,lpOneRestrict_apply]
      rw [if_pos (show familyAtom side false i ∈ atomsBefore a from hi),
        if_pos (show familyAtom side true i ∈ atomsBefore a from hi)]
      exact hc.2.2.1 n i
    · rw [truncateCoefficients_future _ _ _ _ _ _ (le_of_not_gt hi),
        truncateCoefficients_future _ _ _ _ _ _ (le_of_not_gt hi),neg_zero]
  · intro n
    rw [truncateCoefficients_infinity]
    exact hc.2.2.2.1 n
  · obtain ⟨b,hb,hdiag⟩ := hc.2.2.2.2
    exact ⟨b,hb,fun n => by rw [truncateCoefficients_base]; exact hdiag n⟩

theorem exists_admissible_code_enumeration (side : Bool) :
    ∃ e : ConstructionIndex → FullCoefficientRows,
      (∀ a, FullCodeAdmissible side (e a)) ∧
      (∀ a n s bit i, a ≤ i → e a n (familyAtom s bit i) = 0) ∧
      ∀ c, FullCodeAdmissible side c → ∃ a, e a = c :=
  exists_supported_coefficient_enumeration (FullCodeAdmissible side)
    ⟨defaultFullRows side,defaultFullRows_admissible side⟩ (fullCodeAdmissible_truncate side)

end SigmaNonprimarity
