import ThesisCommon.Analysis.SubmultiplicativeHull
import Mathlib.Data.List.Perm.Basic

/-! Finite multiplicative factorizations can be normalized by two cost
reductions. The proof chooses a shortest factorization below the original
cost, and rules out reducible pairs and triples by actual list replacement. -/
noncomputable section
namespace ThesisCommon

def FactorListNormalized (K : Set ℝ) (l : List ℝ) : Prop := by
  classical
  exact (l.filter (fun x => decide (x ∉ K ∧ 1 < x))).length ≤ 1 ∧
    ∀ k ∈ K, l.count k ≤ 2

theorem exists_shorter_factorList_of_merge
    (φ : ℝ → ℝ) (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    {l a b : List ℝ} (hl : ∀ x ∈ l, 1 ≤ x)
    (hp : l.Perm (a ++ b)) (ha : 2 ≤ a.length)
    (hcost : φ a.prod ≤ (a.map φ).prod) :
    ∃ m : List ℝ, (∀ x ∈ m, 1 ≤ x) ∧ m.prod = l.prod ∧
      (m.map φ).prod ≤ (l.map φ).prod ∧ m.length < l.length := by
  have hab : ∀ x ∈ a ++ b, 1 ≤ x := fun x hx => hl x (hp.mem_iff.mpr hx)
  have hba : ∀ x ∈ b, 1 ≤ x := fun x hx => hab x (List.mem_append_right _ hx)
  have haa : ∀ x ∈ a, 1 ≤ x := fun x hx => hab x (List.mem_append_left _ hx)
  have hbc : 0 ≤ (b.map φ).prod := by
    apply zero_le_one.trans (list_prod_ge_one ?_)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hφ x (hba x hx)
  refine ⟨a.prod :: b, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact list_prod_ge_one haa
    · exact hba x hx
  · simpa only [List.prod_cons, List.prod_append] using hp.prod_eq.symm
  · rw [(hp.map φ).prod_eq]
    simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append]
    exact mul_le_mul_of_nonneg_right hcost hbc
  · have hlen := hp.length_eq
    simp only [List.length_append, List.length_cons] at *
    omega

theorem exists_normalized_factorList
    (K : Set ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    (hpair : ∀ x y, 1 < x → 1 < y → x ∉ K → y ∉ K →
      φ (x * y) ≤ φ x * φ y)
    (htriple : ∀ k ∈ K, 1 ≤ k → φ (k ^ 3) ≤ (φ k) ^ 3)
    (l : List ℝ) (hl : ∀ x ∈ l, 1 ≤ x) :
    ∃ m : List ℝ, (∀ x ∈ m, 1 ≤ x) ∧ m.prod = l.prod ∧
      (m.map φ).prod ≤ (l.map φ).prod ∧ FactorListNormalized K m := by
  classical
  let P : ℕ → Prop := fun n => ∃ m : List ℝ, m.length = n ∧
    (∀ x ∈ m, 1 ≤ x) ∧ m.prod = l.prod ∧ (m.map φ).prod ≤ (l.map φ).prod
  have hex : ∃ n, P n := ⟨l.length, l, rfl, hl, rfl, le_rfl⟩
  obtain ⟨m, hlen, hm, hprod, hcost⟩ := Nat.find_spec hex
  have hminimal (s : List ℝ) (hs : ∀ x ∈ s, 1 ≤ x) (hsp : s.prod = m.prod)
      (hsc : (s.map φ).prod ≤ (m.map φ).prod) : m.length ≤ s.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨s, rfl, hs, hsp.trans hprod, hsc.trans hcost⟩
  refine ⟨m, hm, hprod, hcost, ?_⟩
  change (m.filter (fun x => decide (x ∉ K ∧ 1 < x))).length ≤ 1 ∧
    ∀ k ∈ K, m.count k ≤ 2
  constructor
  · let p : ℝ → Bool := fun x => decide (x ∉ K ∧ 1 < x)
    change (m.filter p).length ≤ 1
    cases he : m.filter p with
    | nil => simp
    | cons a t =>
      cases t with
      | nil => simp
      | cons b r =>
        have ha : a ∉ K ∧ 1 < a := by
          have h : a ∈ m.filter p := by rw [he]; simp
          exact of_decide_eq_true (List.mem_filter.mp h).2
        have hb : b ∉ K ∧ 1 < b := by
          have h : b ∈ m.filter p := by rw [he]; simp
          exact of_decide_eq_true (List.mem_filter.mp h).2
        have hp : m.Perm ([a, b] ++ (r ++ m.filter (fun x => !p x))) := by
          simpa only [he, List.cons_append, List.nil_append] using
            (List.filter_append_perm p m).symm
        have hc : φ ([a,b].prod) ≤ ([a,b].map φ).prod := by
          simpa only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, mul_one] using
            hpair a b ha.2 hb.2 ha.1 hb.1
        obtain ⟨s, hs, hsp, hsc, hsl⟩ :=
          exists_shorter_factorList_of_merge φ hφ hm hp (by simp) hc
        exact False.elim ((not_lt_of_ge (hminimal s hs hsp hsc)) hsl)
  · intro k hk
    by_contra hcount
    have hthree : (List.replicate 3 k).Sublist m :=
      List.replicate_sublist_iff.mpr (by omega)
    obtain ⟨r, hp⟩ := hthree.exists_perm_append
    have hk1 : 1 ≤ k := hm k (List.count_pos_iff.mp (by omega))
    have hc : φ (List.replicate 3 k).prod ≤ ((List.replicate 3 k).map φ).prod := by
      simpa [pow_succ, mul_assoc] using htriple k hk hk1
    obtain ⟨s, hs, hsp, hsc, hsl⟩ :=
      exists_shorter_factorList_of_merge φ hφ hm hp (by simp) hc
    exact ((not_lt_of_ge (hminimal s hs hsp hsc)) hsl)

end ThesisCommon
