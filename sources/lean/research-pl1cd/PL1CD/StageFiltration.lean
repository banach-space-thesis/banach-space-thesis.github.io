import PL1CD.StageParameters
import Mathlib.Tactic.GCongr

noncomputable section
open Filter
open scoped Topology

namespace PL1CD.StageParameters

theorem low_monotone : Monotone low := by
  apply monotone_nat_of_le_succ
  intro s
  exact (low_le_high s).trans (high_le_low_succ s)

theorem blockSize_monotone : Monotone blockSize := by
  intro s t hst
  unfold blockSize
  apply Nat.ceil_mono
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hlow : (low s : ℝ) ≤ low t := by exact_mod_cast low_monotone hst
  gcongr

theorem levels_le_dimension (s : ℕ) : levels s ≤ dimension s := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [levels_succ, dimension_succ]
      have hk : 1 ≤ blockSize (s + 1) := blockSize_pos (Nat.succ_pos s)
      have h := Nat.mul_le_mul_left (repetitions (s + 1)) hk
      omega

theorem dimension_le_levels_mul_blockSize (s : ℕ) :
    dimension s ≤ levels s * blockSize s := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [dimension_succ, levels_succ, add_mul]
      have hm := Nat.mul_le_mul_left (levels s) (blockSize_monotone (Nat.le_succ s))
      exact Nat.add_le_add_right (ih.trans hm) _

theorem previous_dimension_ratio_le {s : ℕ} (hs : 0 < s) :
    (dimension (s - 1) : ℝ) / levels s ≤ (s : ℝ)⁻¹ ^ 2 := by
  have hrec : levels s = levels (s - 1) + repetitions s := by
    simpa [Nat.sub_add_cancel hs] using levels_succ (s - 1)
  have hN : (0 : ℝ) < levels s := by
    exact_mod_cast (levels_strictMono hs : levels 0 < levels s)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : (repetitions s : ℝ) = (s : ℝ) ^ 2 * (dimension (s - 1) + 1) := by
    simp [repetitions]
  have hNrec : (levels s : ℝ) = levels (s - 1) + repetitions s := by exact_mod_cast hrec
  have hmul : (dimension (s - 1) : ℝ) * (s : ℝ) ^ 2 ≤ levels s := by
    rw [hNrec, hr]
    nlinarith [Nat.cast_nonneg (α := ℝ) (levels (s - 1)), sq_nonneg (s : ℝ)]
  rw [inv_pow, ← one_div]
  apply (div_le_div_iff₀ hN (sq_pos_of_pos hs')).mpr
  simpa using hmul

theorem final_stage_proportion_ge {s : ℕ} (hs : 0 < s) :
    (s : ℝ) ^ 2 / ((s : ℝ) ^ 2 + 1) ≤ (repetitions s : ℝ) / levels s := by
  have hrec : levels s = levels (s - 1) + repetitions s := by
    simpa [Nat.sub_add_cancel hs] using levels_succ (s - 1)
  have hN : (0 : ℝ) < levels s := by exact_mod_cast (levels_strictMono hs)
  have hden : (0 : ℝ) < (s : ℝ) ^ 2 + 1 := by positivity
  have hprev : (levels (s - 1) : ℝ) ≤ dimension (s - 1) :=
    by exact_mod_cast levels_le_dimension (s - 1)
  have hr : (repetitions s : ℝ) = (s : ℝ) ^ 2 * (dimension (s - 1) + 1) := by
    simp [repetitions]
  have hNrec : (levels s : ℝ) = levels (s - 1) + repetitions s := by exact_mod_cast hrec
  apply (div_le_div_iff₀ hden hN).mpr
  rw [hNrec, hr]
  nlinarith [mul_le_mul_of_nonneg_left hprev (sq_nonneg (s : ℝ)),
    sq_nonneg (s : ℝ)]

theorem dimension_ratio_le_blockSize {s : ℕ} (hs : 0 < s) :
    (dimension s : ℝ) / levels s ≤ blockSize s := by
  have hN : (0 : ℝ) < levels s := by exact_mod_cast (levels_strictMono hs)
  apply (div_le_iff₀ hN).mpr
  have h := dimension_le_levels_mul_blockSize s
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

theorem exists_levelStage (n : ℕ) : ∃ s, n ≤ levels s :=
  ⟨n, levels_strictMono.id_le n⟩

def levelStage (n : ℕ) : ℕ := Nat.find (exists_levelStage n)

theorem levelStage_spec (n : ℕ) : n ≤ levels (levelStage n) :=
  Nat.find_spec (exists_levelStage n)

@[simp] theorem levelStage_levels (s : ℕ) : levelStage (levels s) = s := by
  apply le_antisymm
  · exact Nat.find_le (le_refl (levels s))
  · exact levels_strictMono.le_iff_le.mp (levelStage_spec (levels s))

@[simp] theorem levelStage_zero : levelStage 0 = 0 := by
  simpa using levelStage_levels 0

theorem levelStage_pos {n : ℕ} (hn : 0 < n) : 0 < levelStage n := by
  by_contra h
  have hz : levelStage n = 0 := by omega
  have hspec := levelStage_spec n
  rw [hz, levels_zero] at hspec
  omega

theorem levelStage_previous {n : ℕ} (hn : 0 < n) :
    levels (levelStage n - 1) < n := by
  have hs := levelStage_pos hn
  have hm : levelStage n - 1 < levelStage n := by omega
  exact lt_of_not_ge (Nat.find_min (m := levelStage n - 1) (exists_levelStage n) hm)

def filtration (n : ℕ) : ℕ :=
  let s := levelStage n
  dimension (s - 1) + (n - levels (s - 1)) * blockSize s

@[simp] theorem filtration_zero : filtration 0 = 0 := by
  simp [filtration]

theorem filtration_levels (s : ℕ) : filtration (levels s) = dimension s := by
  cases s with
  | zero => simp
  | succ s =>
      simp only [filtration, levelStage_levels, Nat.add_sub_cancel]
      rw [levels_succ, Nat.add_sub_cancel_left, dimension_succ]

theorem filtration_stage {s n : ℕ} (hs : 0 < s)
    (hlower : levels (s - 1) < n) (hupper : n ≤ levels s) :
    filtration n = dimension (s - 1) + (n - levels (s - 1)) * blockSize s := by
  have heq : levelStage n = s := by
    apply le_antisymm
    · exact Nat.find_le hupper
    · have hspec := levelStage_spec n
      by_contra h
      have hle : levelStage n ≤ s - 1 := by omega
      have hd := levels_strictMono.monotone hle
      omega
  simp [filtration, heq]

end PL1CD.StageParameters
