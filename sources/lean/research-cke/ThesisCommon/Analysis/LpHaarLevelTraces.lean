import ThesisCommon.Analysis.LpHaarDyadicRefinement
import ThesisCommon.Analysis.HaarCountableTraceCluster

/-! Bounded level traces on the countable dyadic algebra. A common
subsequence defines a bounded finitely additive scalar trace, without
assuming a Radon--Nikodym density. Scalars may be real or complex. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

abbrev LpHaarDyadicSetIndex := Σ n : ℕ, Finset (Fin (2 ^ n))

def lpHaarDyadicSet (i : LpHaarDyadicSetIndex) : Set ℝ := lpHaarBlockParent i.1 i.2

theorem lpHaarDyadicSet_measurable (i : LpHaarDyadicSetIndex) :
    MeasurableSet (lpHaarDyadicSet i) :=
  i.2.measurableSet_biUnion (fun _ _ => measurableSet_Ioc)

def lpHaarLevelTrace (d : ∀ n, Fin (2 ^ n) → 𝕜) (n : ℕ) (s : Set ℝ) : 𝕜 :=
  ∑ k : Fin (2 ^ n),
    ((volume.restrict (Icc (0 : ℝ) 1)).real (s ∩ lpHaarCell n k) : 𝕜) * d n k

theorem lpHaarLevelTrace_norm_le (d : ∀ n, Fin (2 ^ n) → 𝕜) {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ n k, ‖d n k‖ ≤ M)
    (n : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    ‖lpHaarLevelTrace d n s‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real s := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hdis : Pairwise (fun i j : Fin (2 ^ n) =>
      Disjoint (s ∩ lpHaarCell n i) (s ∩ lpHaarCell n j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel n
      (fun h => hij (Fin.ext h))) hx.2 hy.2
  have hsum : (∑ k : Fin (2 ^ n), μ.real (s ∩ lpHaarCell n k)) ≤ μ.real s := by
    rw [← measureReal_iUnion_fintype hdis (fun _ => hs.inter measurableSet_Ioc)]
    exact measureReal_mono (iUnion_subset (fun _ => inter_subset_left)) (measure_ne_top μ s)
  calc
    _ ≤ ∑ k : Fin (2 ^ n), ‖(μ.real (s ∩ lpHaarCell n k) : 𝕜) * d n k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k : Fin (2 ^ n), M * μ.real (s ∩ lpHaarCell n k) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg measureReal_nonneg, mul_comm]
      exact mul_le_mul_of_nonneg_right (hd n k) measureReal_nonneg
    _ = M * ∑ k : Fin (2 ^ n), μ.real (s ∩ lpHaarCell n k) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hM

theorem lpHaarLevelTrace_union (d : ∀ n, Fin (2 ^ n) → 𝕜)
    (n : ℕ) (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    lpHaarLevelTrace d n (s ∪ t) = lpHaarLevelTrace d n s + lpHaarLevelTrace d n t := by
  unfold lpHaarLevelTrace
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hdis : Disjoint (s ∩ lpHaarCell n k) (t ∩ lpHaarCell n k) :=
    hst.mono inter_subset_left inter_subset_left
  rw [union_inter_distrib_right, measureReal_union hdis (ht.inter measurableSet_Ioc)]
  push_cast
  ring

theorem lpHaarLevelTrace_cluster (d : ∀ n, Fin (2 ^ n) → 𝕜) {M : ℝ}
    (hM : 0 ≤ M) (hd : ∀ n k, ‖d n k‖ ≤ M) :
    ∃ a : LpHaarDyadicSetIndex → 𝕜, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i)) ∧
      ∀ i, Tendsto (fun n => lpHaarLevelTrace d (r n) (lpHaarDyadicSet i)) atTop (𝓝 (a i)) := by
  have hv (n : ℕ) (i : LpHaarDyadicSetIndex) :
      ‖lpHaarLevelTrace d n (lpHaarDyadicSet i)‖ ≤ M := by
    have h := lpHaarLevelTrace_norm_le d hM hd n (lpHaarDyadicSet i) (lpHaarDyadicSet_measurable i)
    have hmeasure : (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i) ≤ 1 := by
      simpa using (measureReal_mono (μ := volume.restrict (Icc (0 : ℝ) 1)) (subset_univ (lpHaarDyadicSet i)))
    exact h.trans (by nlinarith)
  obtain ⟨a, r, hr, _, ha⟩ := haar_countable_trace_cluster
    (fun n i => lpHaarLevelTrace d n (lpHaarDyadicSet i)) hv
  refine ⟨a, r, hr, fun i => ?_, ha⟩
  exact le_of_tendsto (ha i).norm (Eventually.of_forall
    (fun n => lpHaarLevelTrace_norm_le d hM hd (r n) _ (lpHaarDyadicSet_measurable i)))

end ThesisCommon
