import ThesisCommon.Analysis.FiniteFactorNormalization
import Mathlib.Algebra.BigOperators.Intervals

/-! Bounded multiplicities bound finite products. In particular, a list of
positive natural sizes at most k, with each size occurring at most twice,
has product at most (k!)², also when viewed as a list of real factors. -/
noncomputable section
namespace ThesisCommon
local instance : DecidableEq ℝ := Classical.decEq ℝ

theorem realList_prod_le_of_sublist {l r : List ℝ} (h : l.Sublist r)
    (hr : ∀ x ∈ r, 1 ≤ x) : l.prod ≤ r.prod := by
  induction h with
  | slnil => exact le_rfl
  | cons x h ih =>
    have hx := hr x (List.mem_cons_self ..)
    have ht : ∀ a : ℝ, a ∈ _ → 1 ≤ a := fun a ha => hr a (List.mem_cons_of_mem _ ha)
    simp only [List.prod_cons]
    exact (ih ht).trans (le_mul_of_one_le_left (zero_le_one.trans (list_prod_ge_one ht)) hx)
  | cons₂ x h ih =>
    have hx := hr x (List.mem_cons_self ..)
    have ht : ∀ a : ℝ, a ∈ _ → 1 ≤ a := fun a ha => hr a (List.mem_cons_of_mem _ ha)
    simp only [List.prod_cons]
    exact mul_le_mul_of_nonneg_left (ih ht) (zero_le_one.trans hx)

theorem realList_prod_le_square_of_count_le_two
    (l r : List ℝ) (hr : r.Nodup) (hsub : l ⊆ r)
    (hge : ∀ x ∈ r, 1 ≤ x) (hcount : ∀ x ∈ l, l.count x ≤ 2) :
    l.prod ≤ r.prod ^ 2 := by
  have hp : l.Subperm (r ++ r) := by
    apply List.subperm_ext_iff.mpr
    intro x hx
    have hc1 := (List.nodup_iff_count_le_one.mp hr) x
    have hc2 : 0 < r.count x := List.count_pos_iff.mpr (hsub hx)
    have he : r.count x = 1 := by omega
    simpa only [List.count_append, he] using hcount x hx
  obtain ⟨s, hs, hsr⟩ := hp
  have hb := realList_prod_le_of_sublist hsr (fun x hx =>
    (List.mem_append.mp hx).elim (hge x) (hge x))
  simpa only [hs.prod_eq, List.prod_append, pow_two] using hb

theorem realList_prod_le_factorial_square (l : List ℝ) (k : ℕ)
    (hmem : ∀ x ∈ l, ∃ n : ℕ, 1 ≤ n ∧ n ≤ k ∧ x = (n : ℝ))
    (hcount : ∀ x ∈ l, l.count x ≤ 2) :
    l.prod ≤ (k.factorial : ℝ) ^ 2 := by
  let r : List ℝ := ((Finset.Ico 1 (k+1)).toList).map (fun n : ℕ => (n : ℝ))
  have hr : r.Nodup := (Finset.nodup_toList _).map Nat.cast_injective
  have hsub : l ⊆ r := by
    intro x hx
    obtain ⟨n, hn, hnk, rfl⟩ := hmem x hx
    apply List.mem_map.mpr
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_toList, Finset.mem_Ico]
    exact ⟨hn, Nat.lt_succ_of_le hnk⟩
  have hge : ∀ x ∈ r, 1 ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp (Finset.mem_toList.mp hn)).1
    exact_mod_cast hn1
  have hprod : r.prod = (k.factorial : ℝ) := by
    dsimp only [r]
    rw [← Nat.cast_list_prod, Finset.prod_toList, Finset.prod_Ico_id_eq_factorial]
  exact (realList_prod_le_square_of_count_le_two l r hr hsub hge hcount).trans_eq
    (congrArg (fun x : ℝ => x ^ 2) hprod)

end ThesisCommon
