import SurveyStatements.P5HaarBase
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic

/-! The finite dyadic grids used in the Haar-density argument. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

def haarDensityCell (I : DyadicIndex) : Set ℝ :=
  Ico (dyadicStart I) (dyadicEnd I)

theorem haarDensityCell_subset (I : DyadicIndex) :
    haarDensityCell I ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨(dyadicEndpoints I).1.trans hx.1,
    hx.2.le.trans (dyadicEndpoints I).2.2.2⟩

theorem haarDensityCell_width (I : DyadicIndex) :
    dyadicEnd I - dyadicStart I = (1 / 2 : ℝ) ^ I.1 := by
  simp only [dyadicEnd, dyadicStart, one_div_pow]
  ring

theorem haarDensityCell_dist (I : DyadicIndex) {x : ℝ}
    (hx : x ∈ haarDensityCell I) :
    dist x (dyadicStart I) < (1 / 2 : ℝ) ^ I.1 := by
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1), ← haarDensityCell_width]
  exact sub_lt_sub_right hx.2 _

theorem haarDensityCell_unique (n : ℕ) (i j : Fin (2 ^ n)) {x : ℝ}
    (hi : x ∈ haarDensityCell ⟨n, i⟩) (hj : x ∈ haarDensityCell ⟨n, j⟩) : i = j := by
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hil : (i.val : ℝ) ≤ x * (2 : ℝ) ^ n := (div_le_iff₀ hN).mp hi.1
  have hiu : x * (2 : ℝ) ^ n < (i.val : ℝ) + 1 := (lt_div_iff₀ hN).mp hi.2
  have hjl : (j.val : ℝ) ≤ x * (2 : ℝ) ^ n := (div_le_iff₀ hN).mp hj.1
  have hju : x * (2 : ℝ) ^ n < (j.val : ℝ) + 1 := (lt_div_iff₀ hN).mp hj.2
  have hij : i.val < j.val + 1 := by exact_mod_cast hil.trans_lt hju
  have hji : j.val < i.val + 1 := by exact_mod_cast hjl.trans_lt hiu
  apply Fin.ext
  omega

theorem exists_haarDensityCell (n : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    ∃ i : Fin (2 ^ n), x ∈ haarDensityCell ⟨n, i⟩ := by
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hxN : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx.1 hN.le
  have hk : Nat.floor (x * (2 : ℝ) ^ n) < 2 ^ n := by
    apply (Nat.floor_lt hxN).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using
      mul_lt_mul_of_pos_right hx.2 hN
  refine ⟨⟨Nat.floor (x * (2 : ℝ) ^ n), hk⟩, ?_, ?_⟩
  · exact (div_le_iff₀ hN).mpr (Nat.floor_le hxN)
  · exact (lt_div_iff₀ hN).mpr (Nat.lt_floor_add_one _)

theorem ae_mem_unitInterval_Ico :
    ∀ᵐ x ∂unitIntervalMeasure, x ∈ Ico (0 : ℝ) 1 := by
  unfold unitIntervalMeasure
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (1 : ℝ)))]
      with x hx hne
  exact ⟨hx.1, lt_of_le_of_ne hx.2 (by simpa using hne)⟩

end SurveyStatements.P5
