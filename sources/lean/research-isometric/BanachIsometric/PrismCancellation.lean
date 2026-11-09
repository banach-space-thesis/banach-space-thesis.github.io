import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Exact finite-array cancellation for the signed terms in the topological
prism construction. This is an additive identity, not a homotopy premise. -/

namespace BanachIsometric

open Finset
open scoped BigOperators

theorem signed_prism_cancellation {A : Type*} [AddCommGroup A] (n : ℕ)
    (u : Fin (n + 2) → Fin (n + 3) → A)
    (v : Fin (n + 1) → Fin (n + 2) → A)
    (hlower : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)), j ≤ i.castSucc →
      u i.succ j.castSucc = -v i j)
    (hupper : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)), i.castSucc < j →
      u i.castSucc j.succ = -v i j)
    (hdiagonal : ∀ i : Fin (n + 1),
      u i.castSucc i.succ.castSucc = -u i.succ i.succ.castSucc) :
    (∑ i, ∑ j, u i j) + (∑ i, ∑ j, v i j) =
      u 0 0 + u (Fin.last (n + 1)) (Fin.last (n + 2)) := by
  classical
  let U := Fin (n + 2) × Fin (n + 3)
  let V := Fin (n + 1) × Fin (n + 2)
  let D : Finset U := univ.filter (fun p => p.2.val = p.1.val ∨ p.2.val = p.1.val + 1)
  let φ : V → U := fun p =>
    if p.2.val ≤ p.1.val then (p.1.succ, p.2.castSucc) else (p.1.castSucc, p.2.succ)
  have hφmem (p : V) : φ p ∈ Dᶜ := by
    rcases p with ⟨i, j⟩
    by_cases h : j.val ≤ i.val
    · simp only [φ, if_pos h, mem_compl, D, mem_filter, mem_univ, true_and,
        Fin.coe_castSucc, Fin.val_succ]
      omega
    · simp only [φ, if_neg h, mem_compl, D, mem_filter, mem_univ, true_and,
        Fin.coe_castSucc, Fin.val_succ]
      omega
  have hoff : (∑ p : V, -v p.1 p.2) = ∑ p ∈ Dᶜ, u p.1 p.2 := by
    apply Finset.sum_bij (fun p _ => φ p)
    · intro p _
      exact hφmem p
    · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ he
      have hr := congrArg (fun p : U => p.1.val) he
      have hc := congrArg (fun p : U => p.2.val) he
      by_cases h : j.val ≤ i.val <;> by_cases h' : j'.val ≤ i'.val
      all_goals
        simp [φ, h, h'] at hr hc
        apply Prod.ext <;> apply Fin.ext <;> omega
    · rintro ⟨r, c⟩ hrc
      have hd : ¬(c.val = r.val ∨ c.val = r.val + 1) := by
        simpa only [mem_compl, D, mem_filter, mem_univ, true_and] using hrc
      by_cases h : c.val < r.val
      · let i : Fin (n + 1) := ⟨r.val - 1, by omega⟩
        let j : Fin (n + 2) := ⟨c.val, by omega⟩
        refine ⟨(i, j), mem_univ _, ?_⟩
        have hij : j.val ≤ i.val := by dsimp [i, j]; omega
        simp only [φ, if_pos hij]
        apply Prod.ext
        · apply Fin.ext
          change r.val - 1 + 1 = r.val
          omega
        · rfl
      · let i : Fin (n + 1) := ⟨r.val, by omega⟩
        let j : Fin (n + 2) := ⟨c.val - 1, by omega⟩
        refine ⟨(i, j), mem_univ _, ?_⟩
        have hij : ¬j.val ≤ i.val := by dsimp [i, j]; omega
        simp only [φ, if_neg hij]
        apply Prod.ext
        · rfl
        · apply Fin.ext
          change c.val - 1 + 1 = c.val
          omega
    · rintro ⟨i, j⟩ _
      by_cases h : j.val ≤ i.val
      · simp only [φ, if_pos h]
        exact (hlower i j h).symm
      · simp only [φ, if_neg h]
        exact (hupper i j (lt_of_not_ge h)).symm
  have hD : (∑ p ∈ D, u p.1 p.2) =
      ∑ r : Fin (n + 2), (u r r.castSucc + u r r.succ) := by
    simp only [D, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro r _
    have hset : univ.filter (fun c : Fin (n + 3) => c.val = r.val ∨ c.val = r.val + 1) =
        {r.castSucc, r.succ} := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
    have hne : r.castSucc ≠ r.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    rw [← Finset.sum_filter, hset, Finset.sum_pair hne]
  have htel : (∑ r : Fin (n + 2), (u r r.castSucc + u r r.succ)) =
      u 0 0 + u (Fin.last (n + 1)) (Fin.last (n + 2)) := by
    rw [Finset.sum_add_distrib, Fin.sum_univ_succ (fun r => u r r.castSucc),
      Fin.sum_univ_castSucc (fun r => u r r.succ)]
    have he : (∑ i : Fin (n + 1), u i.castSucc i.castSucc.succ) =
        -(∑ i : Fin (n + 1), u i.succ i.succ.castSucc) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact hdiagonal i
    rw [he]
    have hzero : (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) := rfl
    have hlast : (Fin.last (n + 1)).succ = Fin.last (n + 2) := rfl
    rw [hzero, hlast]
    abel
  have hsplit := Finset.sum_add_sum_compl D (fun p : U => u p.1 p.2)
  rw [hD, htel, ← hoff] at hsplit
  have hu : (∑ p : U, u p.1 p.2) = ∑ i, ∑ j, u i j := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have hv : (∑ p : V, -v p.1 p.2) = -(∑ i, ∑ j, v i j) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_neg_distrib]
  rw [hu, hv] at hsplit
  rw [← hsplit]
  abel

end BanachIsometric
