import ThesisCommon.Analysis.IntervalRetractions
import Mathlib.Topology.UrysohnsLemma

/-! Explicit disjoint interval windows converging to zero. Each window
contains a nondegenerate closed interval, and Urysohn's lemma supplies a
continuous cutoff equal to one on that interval and zero off its window. -/
noncomputable section
open Filter Topology
namespace ThesisCommon

def intervalRadius (n : ℕ) : ℝ := (1/2 : ℝ)^n

theorem intervalRadius_pos (n : ℕ) : 0 < intervalRadius n := by unfold intervalRadius; positivity

theorem intervalRadius_le_one (n : ℕ) : intervalRadius n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem intervalRadius_tendsto_zero : Tendsto intervalRadius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def intervalWindowLeft (n : ℕ) : UnitInterval :=
  ⟨(5/8 : ℝ)*intervalRadius n, by
    have hp := intervalRadius_pos n
    have hle := intervalRadius_le_one n
    constructor <;> nlinarith⟩

def intervalWindowRight (n : ℕ) : UnitInterval :=
  ⟨(7/8 : ℝ)*intervalRadius n, by
    have hp := intervalRadius_pos n
    have hle := intervalRadius_le_one n
    constructor <;> nlinarith⟩

def intervalWindow (n : ℕ) : NondegenerateUnitSubinterval :=
  ⟨(intervalWindowLeft n, intervalWindowRight n), by
    change (5/8 : ℝ)*intervalRadius n < (7/8 : ℝ)*intervalRadius n
    have h := intervalRadius_pos n
    nlinarith⟩

def intervalWindowOpen (n : ℕ) : Set UnitInterval :=
  {t | intervalRadius n / 2 < (t : ℝ) ∧ (t : ℝ) < intervalRadius n}

theorem isOpen_intervalWindowOpen (n : ℕ) : IsOpen (intervalWindowOpen n) :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

theorem intervalWindow_subset_open (n : ℕ) :
    Set.Icc (intervalWindowLeft n) (intervalWindowRight n) ⊆ intervalWindowOpen n := by
  intro t ht
  have h := intervalRadius_pos n
  change (5/8 : ℝ)*intervalRadius n ≤ (t : ℝ) ∧ (t : ℝ) ≤ (7/8 : ℝ)*intervalRadius n at ht
  constructor <;> dsimp <;> nlinarith [ht.1, ht.2]

theorem intervalRadius_le_half {i j : ℕ} (hij : i < j) : intervalRadius j ≤ intervalRadius i / 2 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) (Nat.succ_le_of_lt hij)
  simpa only [intervalRadius, pow_succ, mul_one_div] using h

theorem intervalWindowOpen_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (intervalWindowOpen i) (intervalWindowOpen j) := by
  apply Set.disjoint_left.2
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle := intervalRadius_le_half h
    exact (not_lt_of_ge (hj.2.le.trans hle)) hi.1
  · have hle := intervalRadius_le_half h
    exact (not_lt_of_ge (hi.2.le.trans hle)) hj.1

theorem zero_not_mem_intervalWindowOpen (n : ℕ) : (0 : UnitInterval) ∉ intervalWindowOpen n := by
  intro h
  have hp := intervalRadius_pos n
  have hlt : intervalRadius n / 2 < (0 : ℝ) := h.1
  linarith

theorem exists_intervalWindowCutoff (n : ℕ) : ∃ φ : C(UnitInterval, ℝ),
    Set.EqOn φ 0 (intervalWindowOpen n)ᶜ ∧
    Set.EqOn φ 1 (Set.Icc (intervalWindowLeft n) (intervalWindowRight n)) ∧
    ∀ t, φ t ∈ Set.Icc (0 : ℝ) 1 := by
  apply exists_continuous_zero_one_of_isClosed (isOpen_intervalWindowOpen n).isClosed_compl isClosed_Icc
  apply Set.disjoint_left.2
  intro t ht hs
  exact ht (intervalWindow_subset_open n hs)

def intervalWindowCutoff (n : ℕ) : C(UnitInterval, ℝ) := (exists_intervalWindowCutoff n).choose

theorem intervalWindowCutoff_zero (n : ℕ) {t : UnitInterval} (ht : t ∉ intervalWindowOpen n) :
    intervalWindowCutoff n t = 0 := (exists_intervalWindowCutoff n).choose_spec.1 ht

theorem intervalWindowCutoff_one (n : ℕ) {t : UnitInterval}
    (ht : t ∈ Set.Icc (intervalWindowLeft n) (intervalWindowRight n)) :
    intervalWindowCutoff n t = 1 := (exists_intervalWindowCutoff n).choose_spec.2.1 ht

theorem intervalWindowCutoff_bounds (n : ℕ) (t : UnitInterval) :
    0 ≤ intervalWindowCutoff n t ∧ intervalWindowCutoff n t ≤ 1 :=
  (exists_intervalWindowCutoff n).choose_spec.2.2 t

end ThesisCommon
