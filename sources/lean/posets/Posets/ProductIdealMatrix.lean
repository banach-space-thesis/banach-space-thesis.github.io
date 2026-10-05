import Posets.ProductIdealCZero
import Posets.FiniteIncidenceAlgebra
import JFA.RankOneIdeal

/-! A full finite-dimensional matrix operator algebra has exactly two
closed ideals. Every nonzero ideal contains all rank-one operators. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Fintype P]

theorem finiteOperator_rankOne_sum (T : (P → 𝕜) →L[𝕜] (P → 𝕜)) :
    (∑ i : P, (ContinuousLinearMap.proj i).smulRight (T (Pi.single i 1))) = T := by
  apply ContinuousLinearMap.ext
  intro x
  conv_rhs => rw [finiteCoordinateExpansion x]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, map_sum, map_smul]

theorem fullFiniteOperator_closedIdeal_classification
    (I : ClosedIdeal 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜))) : I.val = {0} ∨ I.val = Set.univ := by
  by_cases h0 : I.val = {0}
  · exact Or.inl h0
  · right
    have hex : ∃ Q ∈ I.val, Q ≠ 0 := by
      by_contra h
      push_neg at h
      apply h0
      apply Set.Subset.antisymm
      · exact fun Q hQ => Set.mem_singleton_iff.mpr (h Q hQ)
      · rintro Q rfl
        exact I.property.2.1
    obtain ⟨Q, hQ, hQ0⟩ := hex
    apply Set.eq_univ_of_forall
    intro T
    rw [← finiteOperator_rankOne_sum T]
    exact (closedIdealSubmodule I).sum_mem (fun i _ =>
      JFA.smulRight_mem_ideal_of_ne_zero I.property hQ hQ0 _ _)

variable [Nonempty P]

def fullFiniteOperatorClosedIdealAt (n : Fin 2) :
    ClosedIdeal 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
  if n = 0 then ⟨{0}, JFA.zeroOperators_closedIdeal⟩ else ⊤

theorem fullFiniteOperatorClosedIdealAt_bijective :
    Function.Bijective (fullFiniteOperatorClosedIdealAt (𝕜 := 𝕜) (P := P)) := by
  have hne : ({0} : Set ((P → 𝕜) →L[𝕜] (P → 𝕜))) ≠ Set.univ := Set.singleton_ne_univ 0
  constructor
  · intro i j hij
    have hv := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [fullFiniteOperatorClosedIdealAt]
    exact (Set.singleton_ne_univ (0 : (P → 𝕜) →L[𝕜] (P → 𝕜))) hv.symm
  · intro I
    rcases fullFiniteOperator_closedIdeal_classification I with h | h
    · exact ⟨0, Subtype.ext (by simpa [fullFiniteOperatorClosedIdealAt] using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [fullFiniteOperatorClosedIdealAt] using h.symm)⟩

def fullFiniteOperatorClosedIdealEquivFinTwo :
    ClosedIdeal 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) ≃ Fin 2 :=
  (Equiv.ofBijective fullFiniteOperatorClosedIdealAt fullFiniteOperatorClosedIdealAt_bijective).symm

theorem fullFiniteOperatorClosedIdeal_card :
    Nat.card (ClosedIdeal 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜))) = 2 := by
  rw [Nat.card_congr (fullFiniteOperatorClosedIdealEquivFinTwo (𝕜 := 𝕜) (P := P)), Nat.card_fin]

theorem fullFiniteOperator_maximalClosedIdeal_iff
    (I : Set ((P → 𝕜) →L[𝕜] (P → 𝕜))) :
    IsMaximalClosedIdeal 𝕜 I ↔ I = {0} := by
  constructor
  · intro hI
    exact (fullFiniteOperator_closedIdeal_classification ⟨I, hI.1⟩).resolve_right hI.2.1
  · rintro rfl
    refine ⟨JFA.zeroOperators_closedIdeal, Set.singleton_ne_univ 0, ?_⟩
    intro J hJ _
    exact fullFiniteOperator_closedIdeal_classification ⟨J, hJ⟩

def fullFiniteOperatorMaximalClosedIdealEquivFinOne :
    MaximalClosedIdeals 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜)) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨{0}, (fullFiniteOperator_maximalClosedIdeal_iff _).mpr rfl⟩
  left_inv I := Subtype.ext ((fullFiniteOperator_maximalClosedIdeal_iff I.val).mp I.property).symm
  right_inv _ := Subsingleton.elim _ _

theorem fullFiniteOperatorMaximalClosedIdeal_card :
    Nat.card (MaximalClosedIdeals 𝕜 ((P → 𝕜) →L[𝕜] (P → 𝕜))) = 1 := by
  rw [Nat.card_congr (fullFiniteOperatorMaximalClosedIdealEquivFinOne (𝕜 := 𝕜) (P := P)), Nat.card_fin]

end Posets
