import ThesisCommon.Analysis.LatticeDisjointness
import ThesisCommon.Analysis.RieszDecomposition

/-! Finite disjoint sums in an additive vector lattice. -/
namespace ThesisCommon
open scoped BigOperators
variable {E ι : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

theorem inf_sum_eq_zero_of_nonneg (a : E) (ha : 0 ≤ a) (F : Finset ι) (v : ι → E)
    (hv : ∀ i ∈ F, 0 ≤ v i) (hd : ∀ i ∈ F, a ⊓ v i = 0) :
    a ⊓ ∑ i ∈ F, v i = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, inf_eq_right.mpr ha]
  | @insert i F hi ih =>
    have hpos := hv i (Finset.mem_insert_self _ _)
    have hposF : ∀ j ∈ F, 0 ≤ v j := fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hdisF := ih hposF (fun j hj => hd j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    let z := a ⊓ (v i + ∑ j ∈ F, v j)
    have hz : 0 ≤ z := le_inf ha (add_nonneg hpos (Finset.sum_nonneg hposF))
    obtain ⟨u,w,hu,huv,hw,hwv,huw⟩ := riesz_split_pair hz hpos
      (Finset.sum_nonneg hposF) inf_le_right
    have hua : u ≤ a := (show u ≤ z by rw [← huw]; exact le_add_of_nonneg_right hw).trans inf_le_left
    have hwa : w ≤ a := (show w ≤ z by rw [← huw]; exact le_add_of_nonneg_left hu).trans inf_le_left
    have hu0 : u = 0 := le_antisymm ((le_inf hua huv).trans_eq (hd i (Finset.mem_insert_self _ _))) hu
    have hw0 : w = 0 := le_antisymm ((le_inf hwa hwv).trans_eq hdisF) hw
    change z = 0
    rw [← huw, hu0, hw0, add_zero]

theorem lattice_abs_sum_of_pairwise_disjoint (F : Finset ι) (v : ι → E)
    (hd : (↑F : Set ι).Pairwise (fun i j => |v i| ⊓ |v j| = 0)) :
    |∑ i ∈ F, v i| = ∑ i ∈ F, |v i| := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    have hdF : (↑F : Set ι).Pairwise (fun i j => |v i| ⊓ |v j| = 0) :=
      fun j hj k hk hjk => hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
    have hdis : |v i| ⊓ |∑ j ∈ F, v j| = 0 := by
      rw [ih hdF]
      exact inf_sum_eq_zero_of_nonneg _ (abs_nonneg _) F _ (fun _ _ => abs_nonneg _)
        (fun j hj => hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj)))
    rw [Finset.sum_insert hi, lattice_abs_add_of_disjoint hdis, ih hdF, Finset.sum_insert hi]

end ThesisCommon
