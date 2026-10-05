import ThesisCommon.Analysis.UltrafilterCharge

/-! Boolean operations on the zero-one charges represented by ultrafilters. -/
noncomputable section
open Set Filter
namespace ThesisCommon
attribute [local instance] Classical.propDecidable

theorem ultrafilterCharge_union {α : Type*} (U : Ultrafilter α) (A B : Set α) :
    ultrafilterCharge U (A ∪ B) = max (ultrafilterCharge U A) (ultrafilterCharge U B) := by
  simp only [ultrafilterCharge_apply, Ultrafilter.union_mem_iff]
  by_cases hA : A ∈ U <;> by_cases hB : B ∈ U <;> norm_num [hA,hB]

theorem ultrafilterCharge_compl {α : Type*} (U : Ultrafilter α) (A : Set α) :
    ultrafilterCharge U Aᶜ = 1 - ultrafilterCharge U A := by
  simp only [ultrafilterCharge_apply, Ultrafilter.compl_mem_iff_notMem]
  by_cases hA : A ∈ U <;> norm_num [hA]

theorem ultrafilterCharge_inter {α : Type*} (U : Ultrafilter α) (A B : Set α) :
    ultrafilterCharge U (A ∩ B) = ultrafilterCharge U A * ultrafilterCharge U B := by
  have hinter : A ∩ B ∈ U ↔ A ∈ U ∧ B ∈ U := Filter.inter_mem_iff
  simp only [ultrafilterCharge_apply, hinter]
  by_cases hA : A ∈ U <;> by_cases hB : B ∈ U <;> norm_num [hA,hB]

end ThesisCommon
