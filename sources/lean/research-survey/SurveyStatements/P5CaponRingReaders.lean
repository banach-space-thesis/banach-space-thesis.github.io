import SurveyStatements.P5RademacherReaders
import SurveyStatements.P5MixedSetReaders
import SurveyStatements.P5CaponLeafTests

/-! Contractive readers on the actual mixed space, selecting one outer
Rademacher level on each disjoint inner dyadic ring. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def caponRingReader (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) : MixedNorm ℝ p →L[ℝ] ℝ :=
  mixedSetReader (Finset.range N) (fun i => leftDyadicBranch.annulus (i + 1))
    (dyadicRademacherFunction ℝ) dyadicRademacherFunction_stronglyMeasurable
    norm_dyadicRademacherFunction_le

theorem norm_caponRingReader_le (N : ℕ) : ‖caponRingReader p N‖ ≤ 1 := by
  unfold caponRingReader
  apply norm_mixedSetReader_le (p := p)
  · intro i _
    exact leftDyadicBranch.annulus_measurable _
  · intro i _ j _ hij
    exact leftDyadicBranch.annulus_disjoint (by omega : i + 1 ≠ j + 1)

theorem caponRingReader_tensor_level (N : ℕ)
    (g : Lp ℝ 1 unitIntervalMeasure) (n : ℕ) :
    caponRingReader p N (tensorWith g (dyadicRademacherLp ℝ p n)) =
      if n < N then l1SetReader (leftDyadicBranch.annulus (n + 1)) g else 0 := by
  rw [caponRingReader, mixedSetReader_tensor]
  change (∑ i ∈ Finset.range N,
    l1SetReader (leftDyadicBranch.annulus (i + 1)) g *
      rademacherReader p i (dyadicRademacherLp ℝ p n)) = _
  simp_rw [rademacherReader_level]
  by_cases hn : n < N
  · simp [hn, Finset.mem_range]
  · simp [hn, Finset.mem_range]

theorem caponRingReader_haar_level (N k n : ℕ) :
    caponRingReader p N (tensorWith (dyadicHaar ℝ 1 (leftDyadicIndex k))
      (dyadicRademacherLp ℝ p n)) =
      if n < N then unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) *
        (if k < n + 1 then 1 else if k = n + 1 then -1 else 0) else 0 := by
  rw [caponRingReader_tensor_level]
  split
  · exact l1SetReader_leftDyadicHaar _ _
  · rfl

theorem sum_two_pow_range (N : ℕ) :
    (∑ k ∈ Finset.range N, (2 : ℝ) ^ k) = (2 : ℝ) ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem capon_ring_contribution_le (n : ℕ) :
    (1 / 4 : ℝ) ≤ unitIntervalMeasure.real (leftDyadicBranch.annulus (n + 1)) *
      ((2 : ℝ) ^ (n + 1) - 1) := by
  have hm := leftDyadicBranch.annulus_real_measure (n + 1)
  change unitIntervalMeasure.real _ = _ at hm
  rw [hm, Nat.zero_add, P5Support.intervalLpDyadicRadius, one_div_pow]
  have hpow : (2 : ℝ) ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)]
  have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  field_simp
  nlinarith

end SurveyStatements.P5
