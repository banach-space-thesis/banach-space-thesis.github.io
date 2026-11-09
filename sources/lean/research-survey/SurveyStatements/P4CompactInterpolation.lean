import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.RCLike.Basic

/-! Finite point-evaluation approximations on compact metric spaces. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Metric Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {𝕜 W P : Type*} [RCLike 𝕜] [MetricSpace W] [CompactSpace W]

theorem exists_finite_metric_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset W, ∃ ρ : s → C(W, ℝ),
      (∀ x, ∑ i : s, ρ i x = 1) ∧
      (∀ i x, 0 ≤ ρ i x) ∧
      (∀ i x, ρ i x ≠ 0 → dist i.val x < δ) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun w : W => ball w δ)
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self hδ⟩)
  have hcover : (univ : Set W) ⊆ ⋃ i : s, ball i.val δ := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hxw⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : s => ball i.val δ) (fun _ => isOpen_ball) hcover
  refine ⟨s, fun i => ρ i, ?_, ρ.nonneg, ?_⟩
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  · intro i x hx
    simpa only [dist_comm] using mem_ball.mp (hρ i (subset_closure hx))

def realWeightMap (g : C(W, ℝ)) : C(W, 𝕜) :=
  ⟨fun x => (g x : 𝕜), RCLike.continuous_ofReal.comp g.continuous⟩

def finiteMetricSample (s : Finset W) (ρ : s → C(W, ℝ)) (f : C(W, 𝕜)) : C(W, 𝕜) :=
  ∑ i : s, f i.val • realWeightMap (ρ i)

theorem finiteMetricSample_error_le (s : Finset W) (ρ : s → C(W, ℝ))
    (hsum : ∀ x, ∑ i : s, ρ i x = 1) (hnonneg : ∀ i x, 0 ≤ ρ i x)
    (f : C(W, 𝕜)) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ i x, ρ i x ≠ 0 → ‖f i.val - f x‖ ≤ ε) :
    ‖finiteMetricSample s ρ f - f‖ ≤ ε := by
  classical
  apply (ContinuousMap.norm_le _ hε).mpr
  intro x
  have hsum' : (∑ i : s, (ρ i x : 𝕜)) = 1 := by
    exact_mod_cast hsum x
  have heq : (finiteMetricSample s ρ f - f) x =
      ∑ i : s, (ρ i x : 𝕜) * (f i.val - f x) := by
    simp only [finiteMetricSample, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, realWeightMap, ContinuousMap.coe_mk, smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum', one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [heq]
  calc
    ‖∑ i : s, (ρ i x : 𝕜) * (f i.val - f x)‖ ≤
        ∑ i : s, ‖(ρ i x : 𝕜) * (f i.val - f x)‖ := norm_sum_le _ _
    _ ≤ ∑ i : s, ρ i x * ε := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : ρ i x = 0
      · simp [h]
      · rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hnonneg i x)]
        exact mul_le_mul_of_nonneg_left (hclose i x h) (hnonneg i x)
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

theorem continuous_finiteMetricSample [TopologicalSpace P]
    (s : Finset W) (ρ : s → C(W, ℝ)) (F : P → C(W, 𝕜))
    (hF : ∀ w, Continuous (fun p => F p w)) :
    Continuous (fun p => finiteMetricSample s ρ (F p)) := by
  classical
  apply continuous_finset_sum
  intro i hi
  exact (hF i.val).smul continuous_const

/-- Pointwise scalar continuity into `C(W)` implies a sequence of continuous
maps into its norm topology, converging in norm at every parameter. -/
theorem exists_continuous_pointwise_norm_approximants [TopologicalSpace P]
    (F : P → C(W, 𝕜)) (hF : ∀ w, Continuous (fun p => F p w)) :
    ∃ u : ℕ → C(P, C(W, 𝕜)), ∀ p,
      Tendsto (fun n => u n p) atTop (𝓝 (F p)) := by
  classical
  have hpart (n : ℕ) := exists_finite_metric_partition (W := W)
    (δ := (1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)
  choose s ρ hsum hnonneg hnear using hpart
  refine ⟨fun n => ⟨fun p => finiteMetricSample (s n) (ρ n) (F p),
    continuous_finiteMetricSample (s n) (ρ n) F hF⟩, ?_⟩
  intro p
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (F p).continuous) (ε / 2)
    (half_pos hε)
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (finiteMetricSample_error_le (s n) (ρ n) (hsum n)
    (hnonneg n) (F p) (half_pos hε).le ?_) (half_lt_self hε)
  intro i x hx
  have hdist := hcont ((hnear n i x hx).trans (hN n hn))
  exact (by simpa only [dist_eq_norm] using hdist :
    ‖F p i.val - F p x‖ < ε / 2).le

end SurveyStatements.P4
