import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Finite.Range
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith

/-! Coordinatewise compactness for nonnegative matrices with bounded row sums.
This is the compactness step in Rosenthal's selection lemma. -/
noncomputable section
open Filter Set Topology
namespace ThesisCommon

theorem positive_matrix_cluster (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 ≤ w n m)
    (hbound : ∀ n (F : Finset ℕ), ∑ m ∈ F, w n m ≤ 1)
    (C : Set ℕ) (hC : C.Infinite) :
    ∃ (q : ℕ → ℕ) (v : ℕ → ℝ), StrictMono q ∧ (∀ n, q n ∈ C) ∧
      (∀ m, 0 ≤ v m) ∧ Summable v ∧
      (∀ m, Tendsto (fun n => w (q n) m) atTop (𝓝 (v m))) := by
  classical
  obtain ⟨a, ha, haC⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨n, hnC, hn⟩ := hC.exists_notMem_finset (Finset.range (N + 1))
    exact ⟨n, Nat.lt_of_succ_le (by simpa only [Finset.mem_range, not_lt] using hn), hnC⟩)
  let W : ℕ → ℕ → Set.Icc (0 : ℝ) 1 := fun n m =>
    ⟨w (a n) m, hw _ _, by simpa using hbound (a n) {m}⟩
  obtain ⟨v, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq W
  have hcoord (m : ℕ) : Tendsto (fun n => w (a (φ n)) m) atTop (𝓝 (v m).val) := by
    exact (continuous_subtype_val.tendsto (v m)).comp ((tendsto_pi_nhds.mp hlim) m)
  have hvsum (F : Finset ℕ) : ∑ m ∈ F, (v m).val ≤ 1 := by
    have hsum : Tendsto (fun n => ∑ m ∈ F, w (a (φ n)) m) atTop
        (𝓝 (∑ m ∈ F, (v m).val)) := tendsto_finset_sum F (fun m _ => hcoord m)
    exact le_of_tendsto hsum (Eventually.of_forall (fun n => hbound (a (φ n)) F))
  exact ⟨a ∘ φ, fun m => (v m).val, ha.comp hφ, fun n => haC _,
    fun m => (v m).property.1, summable_of_sum_le (fun m => (v m).property.1) hvsum, hcoord⟩

/-- Beyond one cutoff, every finite subsum of a summable real sequence is small. -/
theorem summable_small_tail {f : ℕ → ℝ} (hf : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ F : Finset ℕ, (∀ m ∈ F, N ≤ m) → ∑ m ∈ F, f m < ε := by
  classical
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hf ε hε
  refine ⟨s.sup id + 1, fun F hF => ?_⟩
  have hdisj : Disjoint F s := Finset.disjoint_left.mpr (by
    intro m hmF hms
    have hm : m ≤ s.sup id := Finset.le_sup (f := id) hms
    exact (not_lt_of_ge hm) (lt_of_lt_of_le (Nat.lt_succ_self _) (hF m hmF)))
  exact (le_abs_self _).trans_lt (by simpa only [Real.norm_eq_abs] using hs F hdisj)

/-- A new row can have small mass on a finite history while avoiding all its cutoffs. -/
theorem positive_matrix_next_row (w : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (q : ℕ → ℕ) (hq : StrictMono q) (C : Set ℕ) (hqC : ∀ n, q n ∈ C)
    (hlim : ∀ m, Tendsto (fun n => w (q n) m) atTop (𝓝 (v m)))
    (ε : ℝ) (N : ℕ)
    (htail : ∀ F : Finset ℕ, (∀ m ∈ F, N ≤ m) → ∑ m ∈ F, v m < ε)
    (cut : ℕ → ℕ) (F : Finset ℕ) (hF : ∀ m ∈ F, N ≤ m) :
    ∃ n ∈ C, N ≤ n ∧ (∀ m ∈ F, m < n ∧ cut m ≤ n) ∧ ∑ m ∈ F, w n m < ε := by
  have hsum : Tendsto (fun k => ∑ m ∈ F, w (q k) m) atTop (𝓝 (∑ m ∈ F, v m)) :=
    tendsto_finset_sum F (fun m _ => hlim m)
  have hsmall : ∀ᶠ k in atTop, ∑ m ∈ F, w (q k) m < ε :=
    hsum.eventually (gt_mem_nhds (htail F hF))
  have hlarge : ∀ᶠ k in atTop, max N (F.sup (fun m => max (m + 1) (cut m))) ≤ q k :=
    hq.tendsto_atTop.eventually (eventually_ge_atTop _)
  obtain ⟨k, hk, hks⟩ := (hlarge.and hsmall).exists
  refine ⟨q k, hqC k, (le_max_left _ _).trans hk, ?_, hks⟩
  intro m hm
  have hm' := (Finset.le_sup (f := fun m => max (m + 1) (cut m)) hm).trans
    ((le_max_right _ _).trans hk)
  exact ⟨Nat.lt_of_succ_le ((le_max_left _ _).trans hm'), (le_max_right _ _).trans hm'⟩

end ThesisCommon
