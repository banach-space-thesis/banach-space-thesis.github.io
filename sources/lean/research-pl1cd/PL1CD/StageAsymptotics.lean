import PL1CD.StageFiltration
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology NNReal

namespace PL1CD.StageParameters

theorem blockSize_lower (s : ℕ) :
    64 * (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)) ≤ blockSize s :=
  Nat.le_ceil _

theorem blockSize_upper {s : ℕ} (hs : 0 < s) :
    (blockSize s : ℝ) ≤ 65 * (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have he : 1 ≤ Real.exp (2 * (s : ℝ) * (low s : ℝ)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hbase : 1 ≤ (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)) := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)) :=
        mul_le_mul (by nlinarith) he (by norm_num) (sq_nonneg _)
  have hceil := Nat.ceil_lt_add_one (show
      0 ≤ 64 * (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)) by positivity)
  change (blockSize s : ℝ) < _ at hceil
  linarith

theorem blockSize_times_exp_high_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun s => (blockSize s : ℝ) * Real.exp (-ε * (high s : ℝ)))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ s : ℕ in atTop,
      (blockSize s : ℝ) * Real.exp (-ε * (high s : ℝ)) ≤
        65 * ((s : ℝ) ^ 2 * Real.exp (-(s : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1,
      hnat.eventually (eventually_ge_atTop (3 / ε))] with s hs hsε
    have hs' : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hεs : 3 ≤ ε * (s : ℝ) := by
      have h := (div_le_iff₀ hε).mp hsε
      nlinarith
    have hpoly : 2 * (s : ℝ) - ε * ((s : ℝ) + 1) ^ 2 ≤ -(s : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hεs hs'
      nlinarith
    have hlow : (1 : ℝ) ≤ low s := by exact_mod_cast low_pos s
    have hexp : (2 * (s : ℝ) - ε * ((s : ℝ) + 1) ^ 2) * (low s : ℝ) ≤ -(s : ℝ) := by
      calc
        _ ≤ -(s : ℝ) * (low s : ℝ) := mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ ≤ -(s : ℝ) * 1 := mul_le_mul_of_nonpos_left hlow (by linarith)
        _ = -(s : ℝ) := mul_one _
    calc
      _ ≤ (65 * (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ))) *
          Real.exp (-ε * (high s : ℝ)) :=
        mul_le_mul_of_nonneg_right (blockSize_upper hs) (Real.exp_pos _).le
      _ = 65 * (s : ℝ) ^ 2 *
          Real.exp ((2 * (s : ℝ) - ε * ((s : ℝ) + 1) ^ 2) * (low s : ℝ)) := by
        simp only [high, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 65 * (s : ℝ) ^ 2 * Real.exp (-(s : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ = _ := by ring
  apply squeeze_zero' (Eventually.of_forall (fun s => by positivity)) hbound
  have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hnat).const_mul 65
  simpa only [Function.comp_def, mul_zero] using ht

theorem previous_dimension_ratio_tendsto :
    Tendsto (fun s => (dimension (s - 1) : ℝ) / levels s) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun s => by positivity))
    (by filter_upwards [eventually_ge_atTop 1] with s hs;
        exact previous_dimension_ratio_le hs)
  have ht : Tendsto (fun s : ℕ => (s : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using ht.pow 2

theorem dimension_ratio_times_exp_high_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun s => ((dimension s : ℝ) / levels s) * Real.exp (-ε * (high s : ℝ)))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun s => by positivity))
    (by filter_upwards [eventually_ge_atTop 1] with s hs;
        exact mul_le_mul_of_nonneg_right (dimension_ratio_le_blockSize hs) (Real.exp_pos _).le)
    (blockSize_times_exp_high_tendsto hε)

theorem coordinateStage_of_stage {s j : ℕ} (hs : 0 < s)
    (hlower : dimension (s - 1) ≤ j) (hupper : j < dimension s) :
    coordinateStage j = s := by
  apply le_antisymm
  · exact Nat.find_le hupper
  · by_contra h
    have hle : coordinateStage j ≤ s - 1 := by omega
    have hd := dimension_strictMono.monotone hle
    have hspec := coordinateStage_spec j
    omega

theorem rates_at_stage_start {s : ℕ} (hs : 0 < s) (A : Set ℕ) :
    rates A (dimension (s - 1)) = stageRate A s := by
  have hd : dimension (s - 1) < dimension s := dimension_strictMono (by omega)
  simp [rates, coordinateStage_of_stage hs le_rfl hd]

theorem high_le_rates_after {s : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∉ A)
    {j : ℕ} (hj : dimension (s - 1) ≤ j) :
    (high s : ℝ≥0) ≤ rates A j := by
  have h := rates_monotone A hj
  rw [rates_at_stage_start hs A] at h
  simpa [stageRate, hsA] using h

end PL1CD.StageParameters
