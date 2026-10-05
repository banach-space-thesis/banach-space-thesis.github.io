import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A finite interval packing bound produces a probability on the underlying
points dominating every interval weight. The cumulative mass is the maximum
weight of a disjoint packing in each initial segment. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.FiniteIntervalDomination

def IsPacking (n : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ E ∈ S, E.1 ≤ E.2 ∧ E.2 < n) ∧
    ∀ E ∈ S, ∀ F ∈ S, E ≠ F →
      Disjoint (Finset.Icc E.1 E.2) (Finset.Icc F.1 F.2)

def packings (n : ℕ) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact ((Finset.range n).product (Finset.range n)).powerset.filter (IsPacking n)

theorem mem_packings {n : ℕ} {S : Finset (ℕ × ℕ)} : S ∈ packings n ↔ IsPacking n S := by
  classical
  rw [packings, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro E hE
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ((h.1 E hE).1.trans_lt (h.1 E hE).2),
      Finset.mem_range.mpr (h.1 E hE).2⟩

theorem empty_packing (n : ℕ) : IsPacking n ∅ := by simp [IsPacking]

theorem packings_nonempty (n : ℕ) : (packings n).Nonempty :=
  ⟨∅, mem_packings.mpr (empty_packing n)⟩

def cumulative (w : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (packings n).sup' (packings_nonempty n) (fun S => ∑ E ∈ S, w E.1 E.2)

theorem packing_le_cumulative {w : ℕ → ℕ → ℝ} {n : ℕ} {S : Finset (ℕ × ℕ)}
    (h : IsPacking n S) : (∑ E ∈ S, w E.1 E.2) ≤ cumulative w n :=
  Finset.le_sup' (fun S => ∑ E ∈ S, w E.1 E.2) (mem_packings.mpr h)

theorem exists_optimal (w : ℕ → ℕ → ℝ) (n : ℕ) :
    ∃ S, IsPacking n S ∧ cumulative w n = ∑ E ∈ S, w E.1 E.2 := by
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup' (packings_nonempty n)
    (fun S => ∑ E ∈ S, w E.1 E.2)
  exact ⟨S, mem_packings.mp hS, heq⟩

theorem cumulative_nonneg (w : ℕ → ℕ → ℝ) (n : ℕ) : 0 ≤ cumulative w n := by
  simpa using (packing_le_cumulative (w := w) (empty_packing n))

theorem IsPacking.mono {m n : ℕ} {S : Finset (ℕ × ℕ)}
    (h : IsPacking m S) (hmn : m ≤ n) : IsPacking n S :=
  ⟨fun E hE => ⟨(h.1 E hE).1, (h.1 E hE).2.trans_le hmn⟩, h.2⟩

theorem cumulative_mono (w : ℕ → ℕ → ℝ) : Monotone (cumulative w) := by
  intro m n hmn
  obtain ⟨S, hS, heq⟩ := exists_optimal w m
  rw [heq]
  exact packing_le_cumulative (hS.mono hmn)

@[simp] theorem cumulative_zero (w : ℕ → ℕ → ℝ) : cumulative w 0 = 0 := by
  obtain ⟨S, hS, heq⟩ := exists_optimal w 0
  have hempty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun E hE => Nat.not_lt_zero _ (hS.1 E hE).2)
  simp [heq, hempty]

theorem IsPacking.insert_after {a b : ℕ} {S : Finset (ℕ × ℕ)}
    (h : IsPacking a S) (hab : a ≤ b) : IsPacking (b + 1) (insert (a, b) S) := by
  classical
  have hd (E) (hE : E ∈ S) :
      Disjoint (Finset.Icc a b) (Finset.Icc E.1 E.2) := by
    apply Finset.disjoint_left.mpr
    intro k hk hkE
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk2 := (Finset.mem_Icc.mp hkE).2
    have hlt := (h.1 E hE).2
    omega
  constructor
  · intro E hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact ⟨hab, Nat.lt_succ_self b⟩
    · exact ⟨(h.1 E hE).1, (h.1 E hE).2.trans_le (by omega)⟩
  · intro E hE F hF hEF
    rcases Finset.mem_insert.mp hE with rfl | hE
    · rcases Finset.mem_insert.mp hF with rfl | hF
      · exact False.elim (hEF rfl)
      · exact hd F hF
    · rcases Finset.mem_insert.mp hF with rfl | hF
      · exact (hd E hE).symm
      · exact h.2 E hE F hF hEF

theorem interval_le_cumulative_difference (w : ℕ → ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    w a b ≤ cumulative w (b + 1) - cumulative w a := by
  classical
  obtain ⟨S, hS, heq⟩ := exists_optimal w a
  have hnot : (a, b) ∉ S := by
    intro hm
    have hlt := (hS.1 (a, b) hm).2
    dsimp at hlt
    omega
  have hh := packing_le_cumulative (w := w) (hS.insert_after hab)
  rw [Finset.sum_insert hnot, ← heq] at hh
  dsimp at hh
  linarith

theorem cumulative_le_of_packing_bound {w : ℕ → ℕ → ℝ} {N : ℕ}
    (h : ∀ S, IsPacking N S → (∑ E ∈ S, w E.1 E.2) ≤ 1) : cumulative w N ≤ 1 := by
  obtain ⟨S, hS, heq⟩ := exists_optimal w N
  rw [heq]
  exact h S hS

theorem sum_difference_Icc (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, (f (n + 1) - f n)) = f (b + 1) - f a := by
  have hset : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hset, Finset.sum_Ico_eq_sub _ (by omega : a ≤ b + 1),
    Finset.sum_range_sub, Finset.sum_range_sub]
  ring

theorem exists_probability_dominating_intervals (w : ℕ → ℕ → ℝ) {N : ℕ}
    (hN : 0 < N)
    (h : ∀ S, IsPacking N S → (∑ E ∈ S, w E.1 E.2) ≤ 1) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧ (∀ n, N ≤ n → μ n = 0) ∧
      (∑ n ∈ Finset.range N, μ n) = 1 ∧
      ∀ a b, a ≤ b → b < N → w a b ≤ ∑ n ∈ Finset.Icc a b, μ n := by
  classical
  let F := cumulative w
  have hF := cumulative_mono w
  have hFN : F N ≤ 1 := cumulative_le_of_packing_bound h
  let μ (n : ℕ) : ℝ := if n < N then F (n + 1) - F n +
    (if n = 0 then 1 - F N else 0) else 0
  have hpos (n : ℕ) : 0 ≤ μ n := by
    dsimp [μ]
    split_ifs <;> have hh := hF (Nat.le_succ n) <;> linarith
  have hdom {n : ℕ} (hn : n < N) : F (n + 1) - F n ≤ μ n := by
    dsimp [μ]
    rw [if_pos hn]
    split_ifs <;> linarith
  refine ⟨μ, hpos, ?_, ?_, ?_⟩
  · intro n hn
    simp [μ, Nat.not_lt.mpr hn]
  · have heq : (∑ n ∈ Finset.range N, μ n) =
        (∑ n ∈ Finset.range N, (F (n + 1) - F n)) + (1 - F N) := by
      calc
        _ = ∑ n ∈ Finset.range N,
            ((F (n + 1) - F n) + if n = 0 then 1 - F N else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [μ, if_pos (Finset.mem_range.mp hn)]
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hN]
    rw [heq, Finset.sum_range_sub]
    simp [F]
  · intro a b hab hb
    calc
      w a b ≤ F (b + 1) - F a := interval_le_cumulative_difference w hab
      _ = ∑ n ∈ Finset.Icc a b, (F (n + 1) - F n) := (sum_difference_Icc F hab).symm
      _ ≤ ∑ n ∈ Finset.Icc a b, μ n := Finset.sum_le_sum fun n hn =>
        hdom ((Finset.mem_Icc.mp hn).2.trans_lt hb)

theorem exists_probability_on_Icc_dominating_intervals (w : ℕ → ℕ → ℝ) {L R : ℕ}
    (hLR : L ≤ R)
    (h : ∀ S, IsPacking (R + 1) S → (∀ E ∈ S, L ≤ E.1) →
      (∑ E ∈ S, w E.1 E.2) ≤ 1) :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n) ∧ (∀ n, n ∉ Finset.Icc L R → μ n = 0) ∧
      (∑ n ∈ Finset.Icc L R, μ n) = 1 ∧
      ∀ a b, L ≤ a → a ≤ b → b ≤ R → w a b ≤ ∑ n ∈ Finset.Icc a b, μ n := by
  classical
  let v (a b : ℕ) := if L ≤ a then w a b else 0
  have hv : ∀ S, IsPacking (R + 1) S → (∑ E ∈ S, v E.1 E.2) ≤ 1 := by
    intro S hS
    let S' := S.filter (fun E => L ≤ E.1)
    have hS' : IsPacking (R + 1) S' := by
      constructor
      · intro E hE
        exact hS.1 E (Finset.mem_filter.mp hE).1
      · intro E hE F hF hEF
        exact hS.2 E (Finset.mem_filter.mp hE).1 F (Finset.mem_filter.mp hF).1 hEF
    have hh := h S' hS' (fun E hE => (Finset.mem_filter.mp hE).2)
    simpa only [S', Finset.sum_filter, v] using hh
  let F := cumulative v
  have hF := cumulative_mono v
  have hFR : F (R + 1) ≤ 1 := cumulative_le_of_packing_bound hv
  have hFL : F L = 0 := by
    obtain ⟨S, hS, heq⟩ := exists_optimal v L
    change cumulative v L = 0
    rw [heq]
    apply Finset.sum_eq_zero
    intro E hE
    have hlt : E.1 < L := (hS.1 E hE).1.trans_lt (hS.1 E hE).2
    simp [v, Nat.not_le.mpr hlt]
  let μ (n : ℕ) : ℝ := if n ∈ Finset.Icc L R then F (n + 1) - F n +
    (if n = L then 1 - F (R + 1) else 0) else 0
  have hpos (n : ℕ) : 0 ≤ μ n := by
    dsimp [μ]
    split_ifs <;> have hh := hF (Nat.le_succ n) <;> linarith
  have hdom {n : ℕ} (hn : n ∈ Finset.Icc L R) : F (n + 1) - F n ≤ μ n := by
    dsimp [μ]
    rw [if_pos hn]
    split_ifs <;> linarith
  refine ⟨μ, hpos, ?_, ?_, ?_⟩
  · intro n hn
    simp only [μ, if_neg hn]
  · have heq : (∑ n ∈ Finset.Icc L R, μ n) =
        (∑ n ∈ Finset.Icc L R, (F (n + 1) - F n)) + (1 - F (R + 1)) := by
      calc
        _ = ∑ n ∈ Finset.Icc L R,
            ((F (n + 1) - F n) + if n = L then 1 - F (R + 1) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [μ, if_pos hn]
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hLR]
    rw [heq, sum_difference_Icc F hLR, hFL]
    ring
  · intro a b ha hab hb
    have hvab : v a b = w a b := if_pos ha
    calc
      w a b = v a b := hvab.symm
      _ ≤ F (b + 1) - F a := interval_le_cumulative_difference v hab
      _ = ∑ n ∈ Finset.Icc a b, (F (n + 1) - F n) := (sum_difference_Icc F hab).symm
      _ ≤ ∑ n ∈ Finset.Icc a b, μ n := Finset.sum_le_sum fun n hn =>
        hdom (Finset.mem_Icc.mpr ⟨ha.trans (Finset.mem_Icc.mp hn).1,
          (Finset.mem_Icc.mp hn).2.trans hb⟩)

end ThesisCommon.FiniteIntervalDomination
