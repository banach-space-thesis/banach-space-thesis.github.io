import JLMS.Definitions
import Mathlib.Tactic

/-!
# Gliding-hump selection of a nearly diagonal matrix

Rows tend to zero; columns tend to a sequence b that also tends to zero.
A finite-history recursion selects one common subsequence on which each
off-diagonal column has an arbitrarily prescribed small bound. The past
entries use column convergence; the future entries use row convergence.
The explicit column budget is suitable for estimating infinite c₀ sums.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_matrix_selection_step (A : ℕ → ℕ → 𝕜) (b : ℕ → 𝕜)
    (hrow : ∀ i, Tendsto (A i) atTop (𝓝 0))
    (hcol : ∀ j, Tendsto (fun n => A n j) atTop (𝓝 (b j)))
    (hb : Tendsto b atTop (𝓝 0))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (n lower : ℕ) (past : Finset (ℕ × ℕ)) :
    ∃ k, lower < k ∧ ‖b k‖ < w n ∧
      ∀ p ∈ past, ‖A p.2 k‖ < w n ∧ ‖A k p.2 - b p.2‖ < w p.1 := by
  have hsmall : ∀ᶠ k in atTop, ‖b k‖ < w n := by
    simpa only [dist_zero_right] using Metric.tendsto_nhds.mp hb (w n) (hw n)
  have hprev : ∀ᶠ k in atTop,
      ∀ p ∈ past, ‖A p.2 k‖ < w n ∧ ‖A k p.2 - b p.2‖ < w p.1 := by
    apply (past.eventually_all).mpr
    intro p hp
    have hr : ∀ᶠ k in atTop, ‖A p.2 k‖ < w n := by
      simpa only [dist_zero_right] using Metric.tendsto_nhds.mp (hrow p.2) (w n) (hw n)
    have hc : ∀ᶠ k in atTop, ‖A k p.2 - b p.2‖ < w p.1 := by
      simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp (hcol p.2) (w p.1) (hw p.1)
    exact hr.and hc
  exact ((eventually_gt_atTop lower).and (hsmall.and hprev)).exists

/-- The selected off-diagonal entries are bounded by twice the column budget. -/
theorem exists_small_offDiagonal_subsequence (A : ℕ → ℕ → 𝕜) (b : ℕ → 𝕜)
    (hrow : ∀ i, Tendsto (A i) atTop (𝓝 0))
    (hcol : ∀ j, Tendsto (fun n => A n j) atTop (𝓝 (b j)))
    (hb : Tendsto b atTop (𝓝 0))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ i j, i ≠ j → ‖A (s i) (s j)‖ ≤ 2 * w j := by
  classical
  choose k hk hbk hprev using exists_matrix_selection_step A b hrow hcol hb w hw
  let H : ℕ → ℕ × Finset (ℕ × ℕ) := Nat.rec (0, ∅)
    (fun n H => (k n H.1 H.2, insert (n, k n H.1 H.2) H.2))
  let s (n : ℕ) := k n (H n).1 (H n).2
  have hstep (n : ℕ) : (H (n + 1)).2 = insert (n, s n) (H n).2 := rfl
  have hmono : Monotone (fun n => (H n).2) := monotone_nat_of_le_succ (fun n => by
    rw [hstep]
    exact Finset.subset_insert _ _)
  have hin (i j : ℕ) (hij : i < j) : (i, s i) ∈ (H j).2 :=
    hmono (Nat.succ_le_of_lt hij) (by
      change (i, s i) ∈ (H (i + 1)).2
      rw [hstep]
      exact Finset.mem_insert_self _ _)
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun n => hk (n + 1) _ _)
  refine ⟨s, hs, ?_⟩
  intro i j hij
  obtain hlt | hgt := lt_or_gt_of_ne hij
  · have h := (hprev j (H j).1 (H j).2 (i, s i) (hin i j hlt)).1
    exact h.le.trans (by nlinarith [hw j])
  · have h := (hprev i (H i).1 (H i).2 (j, s j) (hin j i hgt)).2
    have hb' := hbk j (H j).1 (H j).2
    have htriangle : ‖A (s i) (s j)‖ ≤ ‖A (s i) (s j) - b (s j)‖ + ‖b (s j)‖ :=
      norm_le_norm_sub_add _ _
    exact (htriangle.trans_lt (by dsimp [s] at h hb' ⊢; linarith)).le

end JLMS
