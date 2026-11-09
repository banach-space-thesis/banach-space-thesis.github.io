import PL1CD.PartitionNorms
import PL1CD.SumSeries
import PL1CD.RealInputVariation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators

namespace PL1CD.PartitionNorms
open PL1CD.Entropy PL1.FiniteCoordinateKernels
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem level_coordinate_summable (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y)
    (M : ℕ → ℕ) (n : ℕ) :
    Summable (fun i => Variation.levelSeminorm ℝ Y M n (coordinateOperator U i)) := by
  change Summable (fun i => (Fintype.card (Assignments (Finset.range (M (n + 1)))) : ℝ)⁻¹ *
    ∑ a : Assignments (Finset.range (M (n + 1))),
      ‖(U (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a) -
        PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend _ a))) i‖)
  exact (summable_sum (fun a _ => PL1.L1Sum.summable_norm _)).mul_left _

theorem level_eq_tsum_coordinates (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y)
    (M : ℕ → ℕ) (n : ℕ) :
    Variation.levelSeminorm ℝ (PL1.L1Sum Y) M n U =
      ∑' i, Variation.levelSeminorm ℝ Y M n (coordinateOperator U i) := by
  change finiteAverage (fun a : Assignments (Finset.range (M (n + 1))) =>
    ‖U (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1)) (extend _ a) -
      PL1.ExplicitMartingale.kernelL1 ℝ (M n) (extend _ a))‖) = _
  simp_rw [PL1.L1Sum.norm_eq_tsum]
  exact finiteAverage_tsum _ (fun _ => PL1.L1Sum.summable_norm _)

theorem endpoint_eq_tsum_coordinates (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y)
    (M N : ℕ → ℕ) (s : ℕ) :
    Variation.endpointSeminorm ℝ (PL1.L1Sum Y) M N s U =
      ∑' i, Variation.endpointSeminorm ℝ Y M N s (coordinateOperator U i) := by
  simp only [Variation.endpointSeminorm, Variation.averageSeminorm_apply,
    level_eq_tsum_coordinates]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun n _ => level_coordinate_summable U M n)]

theorem endpoint_le_of_level_le (B : Variation.HaarL1 ℝ →L[ℝ] Y)
    (M N : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hlevel : ∀ n, Variation.levelSeminorm ℝ Y M n B ≤ C) (s : ℕ) :
    Variation.endpointSeminorm ℝ Y M N s B ≤ C := by
  rw [Variation.endpointSeminorm, Variation.averageSeminorm_apply]
  by_cases hz : N s = 0
  · simpa [hz] using hC
  · have hn : (N s : ℝ) ≠ 0 := by exact_mod_cast hz
    calc
      _ ≤ (N s : ℝ)⁻¹ * ∑ _n ∈ Finset.range (N s), C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n _ => hlevel n)) (by positivity)
      _ = C := by simp [hn]

theorem endpoint_tendsto_zero_of_coordinates
    (U : Variation.HaarL1 ℝ →L[ℝ] PL1.L1Sum Y) (M N : ℕ → ℕ)
    (hM : Monotone M) (H : Set ℕ)
    (ht : ∀ i, Tendsto (fun s =>
      Variation.endpointSeminorm ℝ Y M N s (coordinateOperator U i)) (atTop ⊓ 𝓟 H) (𝓝 0)) :
    Tendsto (fun s => Variation.endpointSeminorm ℝ (PL1.L1Sum Y) M N s U)
      (atTop ⊓ 𝓟 H) (𝓝 0) := by
  obtain ⟨b, hb, hb0, hmajor⟩ := exists_coordinate_majorant U
  have hbound (s i : ℕ) :
      ‖Variation.endpointSeminorm ℝ Y M N s (coordinateOperator U i)‖ ≤ 2 * b i := by
    rw [Real.norm_of_nonneg (apply_nonneg _ _)]
    apply endpoint_le_of_level_le _ M N _ (mul_nonneg (by norm_num) (hb0 i)) _ s
    intro n
    exact (level_le_partitionNorm _ M hM n).trans (by
      nlinarith [hmajor (M (n + 1)) i, hmajor (M n) i])
  have h := tendsto_tsum_of_dominated_convergence (hb.mul_left 2) ht
    (Eventually.of_forall (fun s i => hbound s i))
  simpa only [tsum_zero, ← endpoint_eq_tsum_coordinates] using h

end PL1CD.PartitionNorms

namespace PL1CD.Variation
variable (K : Type*) [RCLike K]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]
  [NormedSpace ℝ Y] [IsScalarTower ℝ K Y]

theorem sum_averagedVariation_eq_zero_of_coordinates
    (T : HaarL1 K →L[K] PL1.L1Sum Y) (M N : ℕ → ℕ)
    (hM : Monotone M) (H : Set ℕ) (hH : H.Infinite)
    (hz : ∀ i, averagedVariation K Y M N H hH
      ((lp.evalCLM K (fun _ : ℕ => Y) 1 i).comp T) = 0) :
    averagedVariation K (PL1.L1Sum Y) M N H hH T = 0 := by
  have ht := PartitionNorms.endpoint_tendsto_zero_of_coordinates
    (realInputOperator K T) M N hM H (fun i => ?_)
  · have ht' : Tendsto (fun s => endpointSeminorm K (PL1.L1Sum Y) M N s T)
        (atTop ⊓ 𝓟 H) (𝓝 0) := by
      simpa only [endpointSeminorm_realInput] using ht
    let := alongInfinite_neBot hH
    exact ht'.limsup_eq
  · have h := endpoint_tendsto_zero_of_averagedVariation_eq_zero M N H hH _ (hz i)
    apply h.congr'
    exact Eventually.of_forall (fun s => (endpointSeminorm_realInput K M N s
      ((lp.evalCLM K (fun _ : ℕ => Y) 1 i).comp T)).symm)

end PL1CD.Variation
