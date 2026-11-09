import NonCalkinAlgebra.Statements

set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v

theorem densityCharacter_unique {A : Type u} [TopologicalSpace A]
    {κ ν : Cardinal.{u}} (hκ : HasDensityCharacter A κ) (hν : HasDensityCharacter A ν) :
    κ = ν := by
  obtain ⟨S, hS, hcardS⟩ := hκ.1
  obtain ⟨T, hT, hcardT⟩ := hν.1
  exact le_antisymm ((hκ.2 T hT).trans_eq hcardT)
    ((hν.2 S hS).trans_eq hcardS)

/-- The quantified convention requires a single witness algebra, not a separate
witness chosen after the convention is fixed. -/
theorem avoids_both_quotients_iff (A : SurveyStatements.P2.ComplexBanachAlgebra.{u}) :
    (∀ (convention : QuotientConvention) (X : Type v)
      [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
        ¬ Nonempty (OperatorQuotientIso X convention A.Carrier)) ↔
    (∀ (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ¬ Nonempty (OperatorQuotientIso X .approximable A.Carrier)) ∧
    (∀ (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X],
      ¬ Nonempty (OperatorQuotientIso X .compact A.Carrier)) := by
  constructor
  · intro h
    exact ⟨h .approximable, h .compact⟩
  · rintro ⟨ha, hk⟩ convention
    cases convention
    · exact ha
    · exact hk

theorem unique_closed_ideal_iff_three_ideals (A : Type u) [NormedRing A] :
    HasExactlyOneNonzeroProperClosedIdeal A ↔
      ∃ J : TwoSidedIdeal A, IsNonzeroProperClosedIdeal J ∧
        ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = J ∨ I = ⊤ := by
  constructor
  · rintro ⟨J, hJ, hunique⟩
    refine ⟨J, hJ, ?_⟩
    intro I hI
    by_cases hzero : I = ⊥
    · exact Or.inl hzero
    by_cases htop : I = ⊤
    · exact Or.inr (Or.inr htop)
    exact Or.inr (Or.inl (hunique I ⟨hI, hzero, htop⟩))
  · rintro ⟨J, hJ, hall⟩
    refine ⟨J, hJ, ?_⟩
    intro I hI
    rcases hall I hI.1 with hz | heq | ht
    · exact False.elim (hI.2.1 hz)
    · exact heq
    · exact False.elim (hI.2.2 ht)

end NonCalkinAlgebra
