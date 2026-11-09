import PL1CD.BlockConcentration

noncomputable section
open Filter
open scoped Topology

namespace PL1CD.StageParameters

theorem filtration_stage_inclusive {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) ≤ n) (hupper : n ≤ levels s) :
    filtration n = dimension (s - 1) + (n - levels (s - 1)) * blockSize s := by
  by_cases hn : n = levels (s - 1)
  · subst n
    simp [filtration_levels]
  · exact filtration_stage hs (by omega) hupper

theorem filtration_step {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) :
    filtration (n + 1) = filtration n + blockSize s := by
  rw [filtration_stage_inclusive hs hlower hupper.le,
    filtration_stage_inclusive hs (by omega) hupper]
  have hsub : n + 1 - levels (s - 1) = (n - levels (s - 1)) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem filtration_strictMono : StrictMono filtration := by
  apply strictMono_nat_of_lt_succ
  intro n
  let s := levelStage (n + 1)
  have hs : 0 < s := levelStage_pos (by omega)
  have hlower : levels (s - 1) ≤ n := by
    have h := levelStage_previous (by omega : 0 < n + 1)
    change levels (s - 1) < n + 1 at h
    omega
  have hupper : n < levels s := levelStage_spec (n + 1)
  rw [filtration_step hs hlower hupper]
  exact Nat.lt_add_of_pos_right (blockSize_pos hs)

theorem filtration_block_start_ge {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) :
    dimension (s - 1) ≤ filtration n := by
  rw [filtration_stage_inclusive hs hlower hupper.le]
  omega

theorem filtration_block_end_le {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) :
    filtration n + blockSize s ≤ dimension s := by
  rw [← filtration_step hs hlower hupper, ← filtration_levels]
  exact filtration_strictMono.monotone hupper

theorem blockCoordinates_subset_next {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) ≤ n) (hupper : n < levels s) :
    blockCoordinates (filtration n) (blockSize s) ⊆ Finset.range (filtration (n + 1)) := by
  classical
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  have hi' := Finset.mem_range.mp hi
  rw [filtration_step hs hlower hupper]
  exact Finset.mem_range.mpr (by omega)

theorem blockCoordinates_disjoint_previous (d k : ℕ) :
    Disjoint (blockCoordinates d k) (Finset.range d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
  have h := Finset.mem_range.mp hj'
  omega

theorem previous_levels_ratio_tendsto :
    Tendsto (fun s => (levels (s - 1) : ℝ) / levels s) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun s => by positivity))
    (Eventually.of_forall (fun s => div_le_div_of_nonneg_right
      (by exact_mod_cast levels_le_dimension (s - 1)) (Nat.cast_nonneg _)))
    previous_dimension_ratio_tendsto

theorem final_stage_proportion_tendsto :
    Tendsto (fun s => (repetitions s : ℝ) / levels s) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub previous_levels_ratio_tendsto
  apply (show Tendsto (fun s => 1 - (levels (s - 1) : ℝ) / levels s) atTop (𝓝 1) by
    simpa only [sub_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hN : (levels s : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (levels_strictMono hs)
  have hrec : levels s = levels (s - 1) + repetitions s := by
    simpa [Nat.sub_add_cancel hs] using levels_succ (s - 1)
  have hrec' : (levels s : ℝ) = levels (s - 1) + repetitions s := by exact_mod_cast hrec
  field_simp
  linarith

end PL1CD.StageParameters
