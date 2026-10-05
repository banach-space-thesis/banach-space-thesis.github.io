import ThesisCommon.Analysis.ChargeBasics
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! Ultrafilter point masses on the full power set. Free ultrafilters supply
family atoms and the infinity atom in almost-disjoint compactifications. -/
noncomputable section
open Set Filter
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

def ultrafilterCharge {α : Type*} (U : Ultrafilter α) : UnitCharge α where
  toFun A := if A ∈ U then 1 else 0
  map_empty := by simp
  map_union A B hAB := by
    have hnot : ¬ (A ∈ U ∧ B ∈ U) := fun h => U.neBot.not_disjoint h.1 h.2 hAB
    simp only [Ultrafilter.union_mem_iff]
    by_cases ha : A ∈ U <;> by_cases hb : B ∈ U <;> simp_all
  variation_le F A hA := by
    classical
    by_cases h : ∃ i ∈ F, A i ∈ U
    · obtain ⟨i,hi,hAi⟩ := h
      have hj (j : ℕ) (hj : j ∈ F) (hne : j ≠ i) : A j ∉ U := fun hAj =>
        U.neBot.not_disjoint hAj hAi (hA hj hi hne)
      rw [Finset.sum_eq_single i]
      · simp [hAi]
      · intro j hjF hne
        simp [hj j hjF hne]
      · exact fun hni => False.elim (hni hi)
    · have hn (i : ℕ) (hi : i ∈ F) : A i ∉ U := fun hAi => h ⟨i,hi,hAi⟩
      have heq : (∑ i ∈ F, |if A i ∈ U then (1 : ℝ) else 0|) = 0 :=
        Finset.sum_eq_zero (fun i hi => by simp [hn i hi])
      rw [heq]
      norm_num

@[simp] theorem ultrafilterCharge_apply {α : Type*} (U : Ultrafilter α) (A : Set α) :
    ultrafilterCharge U A = if A ∈ U then 1 else 0 := rfl

@[simp] theorem ultrafilterCharge_univ {α : Type*} (U : Ultrafilter α) :
    ultrafilterCharge U Set.univ = 1 := if_pos Filter.univ_mem

def diracCharge {α : Type*} (a : α) : UnitCharge α := ultrafilterCharge (pure a)

@[simp] theorem diracCharge_apply {α : Type*} (a : α) (A : Set α) :
    diracCharge a A = if a ∈ A then 1 else 0 := by simp [diracCharge]

def freeUltrafilterOn {α : Type*} (A : Set α) (hA : A.Infinite) : Ultrafilter α := by
  haveI := hA.cofinite_inf_principal_neBot
  exact Ultrafilter.of (Filter.cofinite ⊓ Filter.principal A)

theorem freeUltrafilterOn_le_cofinite {α : Type*} (A : Set α) (hA : A.Infinite) :
    (freeUltrafilterOn A hA : Filter α) ≤ Filter.cofinite := by
  haveI := hA.cofinite_inf_principal_neBot
  unfold freeUltrafilterOn
  exact (Ultrafilter.of_le _).trans inf_le_left

theorem mem_freeUltrafilterOn {α : Type*} (A : Set α) (hA : A.Infinite) :
    A ∈ freeUltrafilterOn A hA := by
  haveI := hA.cofinite_inf_principal_neBot
  apply Filter.le_principal_iff.mp
  unfold freeUltrafilterOn
  exact (Ultrafilter.of_le _).trans inf_le_right

theorem finite_not_mem_free {α : Type*} (U : Ultrafilter α)
    (hU : (U : Filter α) ≤ Filter.cofinite) {A : Set α} (hA : A.Finite) : A ∉ U := by
  intro h
  exact Filter.compl_notMem h (hU hA.compl_mem_cofinite)

theorem ultrafilterCharge_finite {α : Type*} (U : Ultrafilter α)
    (hU : (U : Filter α) ≤ Filter.cofinite) {A : Set α} (hA : A.Finite) :
    ultrafilterCharge U A = 0 := by
  simp [finite_not_mem_free U hU hA]

theorem ultrafilterCharge_eq_zero_of_finite_inter {α : Type*} (U : Ultrafilter α)
    (hU : (U : Filter α) ≤ Filter.cofinite) {A B : Set α}
    (hA : A ∈ U) (hAB : (A ∩ B).Finite) : ultrafilterCharge U B = 0 := by
  have hB : B ∉ U := fun hB => finite_not_mem_free U hU hAB (Filter.inter_mem hA hB)
  simp [hB]

end ThesisCommon
