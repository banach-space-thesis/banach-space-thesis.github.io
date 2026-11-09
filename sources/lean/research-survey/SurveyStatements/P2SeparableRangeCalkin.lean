import SurveyStatements.P2SeparableRange
import SurveyStatements.P2Calkin

/-! In a simple Calkin algebra over a nonseparable space, every
separable-range operator is compact. The ideal is the actual image of the
separable-range operator ideal under the Calkin quotient. -/

noncomputable section
set_option autoImplicit false
open TopologicalSpace

namespace SurveyStatements.P2

universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]

def separableRangeCalkinIdeal : TwoSidedIdeal (Calkin X) :=
  TwoSidedIdeal.mk' {z | ∃ T : BoundedOperators X,
      T ∈ SeparableRangeOperators X ∧ calkinQuotient X T = z}
    (by exact ⟨0, (SeparableRangeOperators X).zero_mem, rfl⟩)
    (by
      rintro z w ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
      refine ⟨S + T, (SeparableRangeOperators X).add_mem hS hT, ?_⟩
      exact map_add (CompactOperators X).mkQ S T)
    (by
      rintro z ⟨T, hT, rfl⟩
      refine ⟨-T, (SeparableRangeOperators X).neg_mem hT, ?_⟩
      exact map_neg (CompactOperators X).mkQ T)
    (by
      rintro z w ⟨T, hT, rfl⟩
      obtain ⟨S, rfl⟩ := calkinQuotient_surjective X z
      exact ⟨S * T, (SeparableRangeOperators X).mul_mem_left S T hT, rfl⟩)
    (by
      rintro z w ⟨S, hS, rfl⟩
      obtain ⟨T, rfl⟩ := calkinQuotient_surjective X w
      exact ⟨S * T, (SeparableRangeOperators X).mul_mem_right S T hS, rfl⟩)

@[simp] theorem mem_separableRangeCalkinIdeal (z : Calkin X) :
    z ∈ separableRangeCalkinIdeal X ↔ ∃ T : BoundedOperators X,
      T ∈ SeparableRangeOperators X ∧ calkinQuotient X T = z := by
  simp [separableRangeCalkinIdeal]

@[simp] theorem calkinQuotient_mem_separableRangeCalkinIdeal (T : BoundedOperators X) :
    calkinQuotient X T ∈ separableRangeCalkinIdeal X ↔ T ∈ SeparableRangeOperators X := by
  constructor
  · intro hT
    obtain ⟨S, hS, hq⟩ := (mem_separableRangeCalkinIdeal X _).mp hT
    have hk : IsCompactOperator (T - S) := by
      apply (calkinQuotient_eq_zero_iff X (T - S)).mp
      change (CompactOperators X).mkQ (T - S) = 0
      rw [map_sub]
      change calkinQuotient X T - calkinQuotient X S = 0
      rw [hq, sub_self]
    have hsep := isSeparableRange_add (compactOperator_range_isSeparable hk)
      ((mem_separableRangeOperators S).mp hS)
    have heq : T - S + S = T := by abel
    apply (mem_separableRangeOperators T).mpr
    rwa [heq] at hsep
  · intro hT
    exact (mem_separableRangeCalkinIdeal X _).mpr ⟨T, hT, rfl⟩

theorem separableRangeCalkinIdeal_isClosed :
    IsClosed (separableRangeCalkinIdeal X : Set (Calkin X)) := by
  apply (Submodule.isOpenQuotientMap_mkQ (CompactOperators X)).isQuotientMap.isClosed_preimage.mp
  have hpre : (CompactOperators X).mkQ ⁻¹'
      (separableRangeCalkinIdeal X : Set (Calkin X)) =
        (SeparableRangeOperators X : Set (BoundedOperators X)) := by
    ext T
    exact calkinQuotient_mem_separableRangeCalkinIdeal X T
  rw [hpre]
  exact separableRangeOperators_isClosed

theorem separableRangeCalkinIdeal_ne_top (hX : ¬ SeparableSpace X) :
    separableRangeCalkinIdeal X ≠ ⊤ := by
  intro htop
  obtain ⟨T, hT, hq⟩ := (mem_separableRangeCalkinIdeal X 1).mp
    ((separableRangeCalkinIdeal X).one_mem htop)
  have hk : IsCompactOperator (T - (1 : BoundedOperators X)) := by
    apply (calkinQuotient_eq_zero_iff X (T - (1 : BoundedOperators X))).mp
    change (CompactOperators X).mkQ (T - (1 : BoundedOperators X)) = 0
    rw [map_sub]
    change calkinQuotient X T - calkinQuotient X 1 = 0
    rw [hq, calkinQuotient_one, sub_self]
  have hI : (1 : BoundedOperators X) ∈ SeparableRangeOperators X := by
    have hsep := isSeparableRange_add ((mem_separableRangeOperators T).mp hT)
      (isSeparableRange_neg (compactOperator_range_isSeparable hk))
    have heq : T + -(T - 1) = (1 : BoundedOperators X) := by abel
    apply (mem_separableRangeOperators 1).mpr
    rwa [heq] at hsep
  exact hX ((one_mem_separableRangeOperators_iff (X := X)).mp hI)

/-- Simplicity kills the proper separable-range ideal in the Calkin algebra. -/
theorem compact_of_separableRange_of_simple_calkin
    (hX : ¬ SeparableSpace X)
    (hsimple : ∀ J : TwoSidedIdeal (Calkin X), J = ⊥ ∨ J = ⊤)
    {T : BoundedOperators X} (hT : IsSeparable (Set.range T)) :
    IsCompactOperator T := by
  have hbot : separableRangeCalkinIdeal X = ⊥ :=
    (hsimple (separableRangeCalkinIdeal X)).resolve_right
      (separableRangeCalkinIdeal_ne_top X hX)
  have hq : calkinQuotient X T ∈ separableRangeCalkinIdeal X :=
    (mem_separableRangeCalkinIdeal X _).mpr
      ⟨T, (mem_separableRangeOperators T).mpr hT, rfl⟩
  rw [hbot, TwoSidedIdeal.mem_bot] at hq
  exact (calkinQuotient_eq_zero_iff X T).mp hq

/-- The same conclusion needs only topological simplicity, as in the source. -/
theorem compact_of_separableRange_of_topologicallySimple_calkin
    (hX : ¬ SeparableSpace X)
    (hsimple : ∀ J : TwoSidedIdeal (Calkin X), IsClosed (J : Set (Calkin X)) →
      J = ⊥ ∨ J = ⊤)
    {T : BoundedOperators X} (hT : IsSeparable (Set.range T)) :
    IsCompactOperator T := by
  have hbot : separableRangeCalkinIdeal X = ⊥ :=
    (hsimple (separableRangeCalkinIdeal X) (separableRangeCalkinIdeal_isClosed X)).resolve_right
      (separableRangeCalkinIdeal_ne_top X hX)
  have hq : calkinQuotient X T ∈ separableRangeCalkinIdeal X :=
    (mem_separableRangeCalkinIdeal X _).mpr
      ⟨T, (mem_separableRangeOperators T).mpr hT, rfl⟩
  rw [hbot, TwoSidedIdeal.mem_bot] at hq
  exact (calkinQuotient_eq_zero_iff X T).mp hq

end SurveyStatements.P2
