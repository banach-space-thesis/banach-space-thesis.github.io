import NonCalkinAlgebra.QuotientAlgebra
import SurveyStatements.P2SeparableRangeCalkin

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open SurveyStatements.P2 TopologicalSpace
universe v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

/-- The paper's R_X, using the actual image of separable-range operators
under the quotient by the fixed selected operator ideal. -/
def separableRangeQuotientIdeal : TwoSidedIdeal (OperatorQuotient X convention) :=
  TwoSidedIdeal.mk' {z | ∃ T : BoundedOperators X,
      T ∈ SeparableRangeOperators X ∧ operatorQuotientMap X convention T = z}
    ⟨0, (SeparableRangeOperators X).zero_mem, rfl⟩
    (by
      rintro z w ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
      exact ⟨S + T, (SeparableRangeOperators X).add_mem hS hT,
        map_add (operatorQuotientMap X convention) S T⟩)
    (by
      rintro z ⟨T, hT, rfl⟩
      exact ⟨-T, (SeparableRangeOperators X).neg_mem hT,
        map_neg (operatorQuotientMap X convention) T⟩)
    (by
      rintro z w ⟨T, hT, rfl⟩
      obtain ⟨S, rfl⟩ := operatorQuotientMap_surjective X convention z
      exact ⟨S * T, (SeparableRangeOperators X).mul_mem_left S T hT, rfl⟩)
    (by
      rintro z w ⟨S, hS, rfl⟩
      obtain ⟨T, rfl⟩ := operatorQuotientMap_surjective X convention w
      exact ⟨S * T, (SeparableRangeOperators X).mul_mem_right S T hS, rfl⟩)

@[simp] theorem mem_separableRangeQuotientIdeal (z : OperatorQuotient X convention) :
    z ∈ separableRangeQuotientIdeal X convention ↔ ∃ T : BoundedOperators X,
      T ∈ SeparableRangeOperators X ∧ operatorQuotientMap X convention T = z := by
  simp only [separableRangeQuotientIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

@[simp] theorem operatorQuotientMap_mem_separableRangeQuotientIdeal (T : BoundedOperators X) :
    operatorQuotientMap X convention T ∈ separableRangeQuotientIdeal X convention ↔
      T ∈ SeparableRangeOperators X := by
  constructor
  · intro hT
    obtain ⟨S, hS, hq⟩ := (mem_separableRangeQuotientIdeal X convention _).mp hT
    have hdiff : T - S ∈ operatorIdeal X convention := by
      apply (operatorQuotientMap_eq_zero X convention _).mp
      rw [map_sub, hq, sub_self]
    have hsep := isSeparableRange_add
      (compactOperator_range_isSeparable (operatorIdeal_le_compact X convention hdiff))
      ((mem_separableRangeOperators S).mp hS)
    have heq : T - S + S = T := by abel
    apply (mem_separableRangeOperators T).mpr
    rwa [heq] at hsep
  · intro hT
    exact (mem_separableRangeQuotientIdeal X convention _).mpr ⟨T, hT, rfl⟩

theorem separableRangeQuotientIdeal_isClosed :
    IsClosed (separableRangeQuotientIdeal X convention : Set (OperatorQuotient X convention)) := by
  apply (Submodule.isOpenQuotientMap_mkQ (operatorIdeal X convention)).isQuotientMap.isClosed_preimage.mp
  have hpre : (operatorIdeal X convention).mkQ ⁻¹'
      (separableRangeQuotientIdeal X convention : Set (OperatorQuotient X convention)) =
        (SeparableRangeOperators X : Set (BoundedOperators X)) := by
    ext T
    exact operatorQuotientMap_mem_separableRangeQuotientIdeal X convention T
  rw [hpre]
  exact separableRangeOperators_isClosed

theorem separableRangeQuotientIdeal_ne_top (hX : ¬ SeparableSpace X) :
    separableRangeQuotientIdeal X convention ≠ ⊤ := by
  intro htop
  have hone : operatorQuotientMap X convention 1 ∈ separableRangeQuotientIdeal X convention := by
    rw [htop]
    trivial
  have hsep := (operatorQuotientMap_mem_separableRangeQuotientIdeal X convention 1).mp hone
  exact hX (one_mem_separableRangeOperators_iff.mp hsep)

theorem exists_separable_representative {e : OperatorQuotient X convention}
    (he : e ∈ separableRangeQuotientIdeal X convention) :
    ∃ T : BoundedOperators X, IsSeparable (Set.range T) ∧ operatorQuotientMap X convention T = e := by
  obtain ⟨T, hT, hq⟩ := (mem_separableRangeQuotientIdeal X convention e).mp he
  exact ⟨T, (mem_separableRangeOperators T).mp hT, hq⟩

end NonCalkinAlgebra
