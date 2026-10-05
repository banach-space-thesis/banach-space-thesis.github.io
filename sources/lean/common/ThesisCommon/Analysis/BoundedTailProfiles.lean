import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-! Countable compactness and diagonal choices for bounded tail-mass profiles.
These selection lemmas use ordinary real numbers and actual subsequences. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon

theorem exists_strictMono_eventually_rows (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ k, P k (r k) := by
  choose N hN using fun k => eventually_atTop.mp (hP k)
  let r : ℕ → ℕ := Nat.rec (N 0) (fun k x => max (x + 1) (N (k + 1)))
  have hr : ∀ k, r (k + 1) = max (r k + 1) (N (k + 1)) := fun k => rfl
  refine ⟨r, strictMono_nat_of_lt_succ (fun k => ?_), fun k => hN k _ ?_⟩
  · rw [hr]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  · cases k with
    | zero => exact le_rfl
    | succ k => rw [hr]; exact le_max_right _ _

theorem exists_bounded_profile_subsequence (b : ℕ → ℕ → ℝ) {C : ℝ}
    (hb : ∀ n m, 0 ≤ b n m ∧ b n m ≤ C) :
    ∃ a : ℕ → ℝ, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ m, 0 ≤ a m ∧ a m ≤ C) ∧
      ∀ m, Tendsto (fun n => b (r n) m) atTop (𝓝 (a m)) := by
  letI : CompactSpace (Icc (0 : ℝ) C) := isCompact_iff_compactSpace.mp isCompact_Icc
  let v : ℕ → (ℕ → Icc (0 : ℝ) C) := fun n m => ⟨b n m, hb n m⟩
  obtain ⟨a, r, hr, ha⟩ := CompactSpace.tendsto_subseq v
  refine ⟨fun m => (a m).val, r, hr, fun m => (a m).property, fun m => ?_⟩
  exact continuous_subtype_val.tendsto (a m) |>.comp
    ((continuous_apply m).tendsto a |>.comp ha)

theorem exists_antitone_profile_limit (b : ℕ → ℕ → ℝ) {C : ℝ}
    (hb : ∀ n m, 0 ≤ b n m ∧ b n m ≤ C) (hanti : ∀ n, Antitone (b n)) :
    ∃ a : ℕ → ℝ, ∃ α : ℝ, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ m, 0 ≤ a m ∧ a m ≤ C) ∧ Antitone a ∧
      (∀ m, α ≤ a m) ∧ 0 ≤ α ∧ Tendsto a atTop (𝓝 α) ∧
      ∀ m, Tendsto (fun n => b (r n) m) atTop (𝓝 (a m)) := by
  obtain ⟨a, r, hr, ha, ht⟩ := exists_bounded_profile_subsequence b hb
  have hanti' : Antitone a := fun i j hij =>
    le_of_tendsto_of_tendsto (ht j) (ht i) (Eventually.of_forall fun n => hanti _ hij)
  have hbelow : BddBelow (range a) := ⟨0, by rintro _ ⟨m, rfl⟩; exact (ha m).1⟩
  refine ⟨a, ⨅ m, a m, r, hr, ha, hanti', fun m => ciInf_le hbelow m,
    le_ciInf (fun m => (ha m).1), tendsto_atTop_ciInf hanti' hbelow, ht⟩

theorem exists_profile_diagonal_choice (b : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ht : ∀ m, Tendsto (fun n => b n m) atTop (𝓝 (a m)))
    (L : ℕ → ℕ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ k m, m ≤ k → |b (r k) m - a m| < ε k) ∧
      ∀ k, |b (r k) (L k) - a (L k)| < ε k := by
  have he (k m : ℕ) : ∀ᶠ n in atTop, |b n m - a m| < ε k := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (ht m) (ε k) (hε k))
  have hall (k : ℕ) : ∀ᶠ n in atTop,
      (∀ m ≤ k, |b n m - a m| < ε k) ∧ |b n (L k) - a (L k)| < ε k := by
    have hf : ∀ᶠ n in atTop, ∀ m ∈ Finset.range (k + 1), |b n m - a m| < ε k :=
      (Finset.eventually_all _).mpr fun m _ => he k m
    filter_upwards [hf, he k (L k)] with n hn hnL
    exact ⟨fun m hm => hn m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)), hnL⟩
  obtain ⟨r, hr, hs⟩ := exists_strictMono_eventually_rows _ hall
  exact ⟨r, hr, fun k => (hs k).1, fun k => (hs k).2⟩

end ThesisCommon
