import ThesisCommon.Analysis.MeasurePuncturedBalls
import ThesisCommon.Analysis.KernelProductRestriction
import Mathlib.Topology.MetricSpace.Sequences

/-! A finite measurable kernel has arbitrarily small off-diagonal mass on
some positive-measure subset of every positive-measure set. This is an actual
localization step: measurability, shrinking punctured balls, and a countable
small-ball cover produce the subset, with no operator or factorization premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

theorem measurable_kernel_diagonal (κ : Kernel X X) [IsFiniteKernel κ] :
    Measurable (fun x => κ x {x}) := by
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ)
    (show MeasurableSet {z : X × X | z.1 = z.2} from
      (isClosed_eq continuous_fst continuous_snd).measurableSet)
  convert h using 1
  ext x
  congr 1
  ext y
  simp [eq_comm]

theorem measurable_kernel_punctured_ball (κ : Kernel X X) [IsFiniteKernel κ] (r : ℝ) :
    Measurable (fun x => κ x (Metric.ball x r \ {x})) := by
  have hs : MeasurableSet {z : X × X | dist z.2 z.1 < r ∧ z.2 ≠ z.1} :=
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet.inter
      (isClosed_eq continuous_snd continuous_fst).measurableSet.compl
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ) hs
  convert h using 1

theorem measurable_kernel_real_punctured_ball (κ : Kernel X X) [IsFiniteKernel κ] (r : ℝ) :
    Measurable (fun x => (κ x).real (Metric.ball x r \ {x})) :=
  (measurable_kernel_punctured_ball κ r).ennreal_toReal

omit [SecondCountableTopology X] in
theorem kernel_real_punctured_ball_tendsto (κ : Kernel X X) [IsFiniteKernel κ] (x : X) :
    Tendsto (fun n : ℕ => (κ x).real (Metric.ball x (1 / (n + 1 : ℝ)) \ {x})) atTop (𝓝 0) :=
  tendsto_measureReal_puncturedBalls (κ x) x

theorem exists_kernel_uniform_punctured_ball_bound
    (κ : Kernel X X) [IsFiniteKernel κ] (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) (hpos : 0 < μ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (E : Set X), E ⊆ A ∧ MeasurableSet E ∧ 0 < μ E ∧
      ∀ x ∈ E, (κ x).real (Metric.ball x (1 / (n + 1 : ℝ)) \ {x}) < ε := by
  let E (n : ℕ) := A ∩ {x | (κ x).real (Metric.ball x (1 / (n + 1 : ℝ)) \ {x}) < ε}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (measurableSet_lt (measurable_kernel_real_punctured_ball κ _) measurable_const)
  have hcover : A ⊆ ⋃ n, E n := by
    intro x hx
    obtain ⟨n, hn⟩ := ((kernel_real_punctured_ball_tendsto κ x).eventually (gt_mem_nhds hε)).exists
    exact mem_iUnion.mpr ⟨n, hx, hn⟩
  have hmass : μ (⋃ n, E n) ≠ 0 := (hpos.trans_le (measure_mono hcover)).ne'
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hmass
  exact ⟨n, E n, inter_subset_left, hE n, hn, fun _ hx => hx.2⟩

theorem exists_positive_measure_subset_small_diameter
    (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (hpos : 0 < μ E)
    {r : ℝ} (hr : 0 < r) :
    ∃ A ⊆ E, MeasurableSet A ∧ 0 < μ A ∧ ∀ x ∈ A, ∀ y ∈ A, dist y x < r := by
  have hne : E.Nonempty := nonempty_of_measure_ne_zero hpos.ne'
  letI : Nonempty X := ⟨hne.choose⟩
  let A (n : ℕ) := E ∩ Metric.ball (denseSeq X n) (r / 2)
  have hcover : E ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨n, hn⟩ := (denseRange_denseSeq X).exists_dist_lt x (half_pos hr)
    exact mem_iUnion.mpr ⟨n, hx, by simpa [dist_comm] using hn⟩
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (hpos.trans_le (measure_mono hcover)).ne'
  refine ⟨A n, inter_subset_left, hE.inter measurableSet_ball, hn, ?_⟩
  intro x hx y hy
  have h := dist_triangle y (denseSeq X n) x
  have hx' := hx.2
  have hy' := hy.2
  rw [Metric.mem_ball] at hx' hy'
  rw [dist_comm (denseSeq X n) x] at h
  linarith

theorem exists_kernel_offDiagonal_small_set
    (κ : Kernel X X) [IsFiniteKernel κ] (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) (hpos : 0 < μ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ D ⊆ A, MeasurableSet D ∧ 0 < μ D ∧
      ∀ x ∈ D, (κ x).real (D \ {x}) < ε := by
  obtain ⟨n, E, hEA, hE, hposE, hbound⟩ :=
    exists_kernel_uniform_punctured_ball_bound κ μ hA hpos hε
  obtain ⟨D, hDE, hD, hposD, hdiam⟩ :=
    exists_positive_measure_subset_small_diameter μ hE hposE
      (show 0 < 1 / (n + 1 : ℝ) by positivity)
  refine ⟨D, hDE.trans hEA, hD, hposD, fun x hx => ?_⟩
  apply lt_of_le_of_lt (measureReal_mono ?_) (hbound x (hDE hx))
  intro y hy
  exact ⟨hdiam x hx y hy.1, hy.2⟩

end ThesisCommon
