import PL1CD.AlmostDisjoint
import PL1CD.ProjectionFamily
import PL1CD.DunfordPettisIdeals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open Filter
open scoped NNReal

namespace PL1CD.StageParameters

def low (s : ℕ) : ℕ := (Nat.factorial s) ^ 4

def high (s : ℕ) : ℕ := (s + 1) ^ 2 * low s

def blockSize (s : ℕ) : ℕ :=
  Nat.ceil (64 * (s : ℝ) ^ 2 * Real.exp (2 * (s : ℝ) * (low s : ℝ)))

def endpoints : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | s + 1 =>
      let previous := endpoints s
      let r := (s + 1) ^ 2 * (previous.2 + 1)
      (previous.1 + r, previous.2 + r * blockSize (s + 1))

def levels (s : ℕ) : ℕ := (endpoints s).1

def dimension (s : ℕ) : ℕ := (endpoints s).2

def repetitions (s : ℕ) : ℕ := s ^ 2 * (dimension (s - 1) + 1)

theorem low_pos (s : ℕ) : 0 < low s := pow_pos (Nat.factorial_pos s) 4

theorem low_le_high (s : ℕ) : low s ≤ high s := by
  have h : 1 ≤ (s + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simpa [high] using Nat.mul_le_mul_right (low s) h

theorem high_le_low_succ (s : ℕ) : high s ≤ low (s + 1) := by
  have h : (s + 1) ^ 2 ≤ (s + 1) ^ 4 :=
    pow_le_pow_right₀ (by omega : 1 ≤ s + 1) (by decide : 2 ≤ 4)
  calc
    high s ≤ (s + 1) ^ 4 * low s := Nat.mul_le_mul_right _ h
    _ = low (s + 1) := by rw [low, low, Nat.factorial_succ, mul_pow]

theorem blockSize_pos {s : ℕ} (hs : 0 < s) : 0 < blockSize s := by
  apply Nat.ceil_pos.mpr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  positivity

@[simp] theorem levels_zero : levels 0 = 0 := rfl
@[simp] theorem dimension_zero : dimension 0 = 0 := rfl

theorem levels_succ (s : ℕ) : levels (s + 1) = levels s + repetitions (s + 1) := by
  simp [levels, repetitions, dimension, endpoints]

theorem dimension_succ (s : ℕ) :
    dimension (s + 1) = dimension s + repetitions (s + 1) * blockSize (s + 1) := by
  simp [dimension, repetitions, endpoints]

theorem repetitions_pos {s : ℕ} (hs : 0 < s) : 0 < repetitions s := by
  unfold repetitions
  positivity

theorem levels_strictMono : StrictMono levels := by
  apply strictMono_nat_of_lt_succ
  intro s
  rw [levels_succ]
  exact Nat.lt_add_of_pos_right (repetitions_pos (Nat.succ_pos s))

theorem dimension_strictMono : StrictMono dimension := by
  apply strictMono_nat_of_lt_succ
  intro s
  rw [dimension_succ]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos (repetitions_pos (Nat.succ_pos s)) (blockSize_pos (Nat.succ_pos s)))

theorem exists_stage (j : ℕ) : ∃ s, j < dimension s :=
  ⟨j + 1, (Nat.lt_succ_self j).trans_le (dimension_strictMono.id_le (j + 1))⟩

def coordinateStage (j : ℕ) : ℕ := Nat.find (exists_stage j)

theorem coordinateStage_spec (j : ℕ) : j < dimension (coordinateStage j) :=
  Nat.find_spec (exists_stage j)

theorem coordinateStage_pos (j : ℕ) : 0 < coordinateStage j := by
  by_contra h
  have hz : coordinateStage j = 0 := by omega
  have hlt := coordinateStage_spec j
  rw [hz, dimension_zero] at hlt
  omega

theorem coordinateStage_monotone : Monotone coordinateStage := by
  intro j k hjk
  exact Nat.find_le (hjk.trans_lt (coordinateStage_spec k))

def stageRate (A : Set ℕ) (s : ℕ) : ℕ := by
  classical
  exact if s ∈ A then low s else high s

theorem low_le_stageRate (A : Set ℕ) (s : ℕ) : low s ≤ stageRate A s := by
  unfold stageRate
  split_ifs
  · exact le_rfl
  · exact low_le_high s

theorem stageRate_le_high (A : Set ℕ) (s : ℕ) : stageRate A s ≤ high s := by
  unfold stageRate
  split_ifs
  · exact low_le_high s
  · exact le_rfl

theorem stageRate_monotone (A : Set ℕ) : Monotone (stageRate A) := by
  apply monotone_nat_of_le_succ
  intro s
  exact (stageRate_le_high A s).trans
    ((high_le_low_succ s).trans (low_le_stageRate A (s + 1)))

def rates (A : Set ℕ) (j : ℕ) : ℝ≥0 := stageRate A (coordinateStage j)

theorem rates_monotone (A : Set ℕ) : Monotone (rates A) := by
  intro j k hjk
  change (stageRate A (coordinateStage j) : ℝ≥0) ≤ stageRate A (coordinateStage k)
  exact_mod_cast stageRate_monotone A (coordinateStage_monotone hjk)

theorem coordinateStage_tendsto : Tendsto coordinateStage atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  filter_upwards [eventually_ge_atTop (dimension s)] with j hj
  by_contra h
  have hsd : dimension (coordinateStage j) ≤ dimension s :=
    dimension_strictMono.monotone (by omega)
  have hjs := (coordinateStage_spec j).trans_le hsd
  omega

theorem self_le_low (s : ℕ) : s ≤ low s := by
  have hfact : s ≤ Nat.factorial s := Nat.self_le_factorial s
  have hpow : Nat.factorial s ≤ (Nat.factorial s) ^ 4 := by
    have h := pow_le_pow_right₀ (by have := Nat.factorial_pos s; omega : 1 ≤ Nat.factorial s)
      (by decide : 1 ≤ 4)
    simpa using h
  exact hfact.trans hpow

theorem rates_tendsto (A : Set ℕ) :
    Tendsto (fun j => (rates A j : ℝ)) cofinite atTop := by
  rw [Nat.cofinite_eq_atTop]
  apply tendsto_atTop_mono (fun j => ?_)
    ((tendsto_natCast_atTop_atTop : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop).comp
      coordinateStage_tendsto)
  change (coordinateStage j : ℝ) ≤ (stageRate A (coordinateStage j) : ℝ≥0)
  exact_mod_cast (self_le_low (coordinateStage j)).trans
    (low_le_stageRate A (coordinateStage j))

end PL1CD.StageParameters

namespace PL1CD

variable (𝕜 : Type) [RCLike 𝕜]

def stageProjectionFamily (a : ContinuumIndex) : L1Operator 𝕜 :=
  intervalProjection 𝕜 (StageParameters.rates (AlmostDisjoint.family a))

theorem stageProjectionFamily_isProjection (a : ContinuumIndex) :
    PL1.IsProjection (stageProjectionFamily 𝕜 a) := intervalProjection_isProjection 𝕜 _

theorem stageProjectionFamily_norm_le (a : ContinuumIndex) :
    ‖stageProjectionFamily 𝕜 a‖ ≤ PL1.projectionBound := intervalProjection_norm_le 𝕜 _

theorem stageProjectionFamily_range_schur (a : ContinuumIndex) :
    PL1.HasSchurProperty 𝕜 (stageProjectionFamily 𝕜 a).range :=
  intervalProjection_range_schur_of_rates_tendsto 𝕜 _ (StageParameters.rates_tendsto _)

theorem stageProjectionFamily_range_infiniteDimensional (a : ContinuumIndex) :
    ¬ FiniteDimensional 𝕜 (stageProjectionFamily 𝕜 a).range :=
  intervalProjection_range_infiniteDimensional 𝕜 _

theorem stageProjectionFamily_idealAdditionalSpec :
    TheoremDAdditionalSpec 𝕜 (stageProjectionFamily 𝕜)
      (generatedIdeal 𝕜 (stageProjectionFamily 𝕜)) :=
  generatedIdeal_additionalSpec 𝕜 _ (stageProjectionFamily_isProjection 𝕜)
    (stageProjectionFamily_range_schur 𝕜) (stageProjectionFamily_range_infiniteDimensional 𝕜)

end PL1CD
