import ThesisCommon.Analysis.LpHaarSplit
import ThesisCommon.Analysis.IntervalLpFunctionPartition

/-! Concrete dyadic Haar vectors in `IntervalLp`, with exact support measures,
norms, and cancellation.  Half-open intervals are `(a,b]`; their endpoint
convention differs from the usual `[a,b)` only on null sets. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace ThesisCommon

def lpHaarCell (n k : ℕ) : Set ℝ :=
  Ioc ((k : ℝ) * intervalLpDyadicRadius n) (((k : ℝ) + 1) * intervalLpDyadicRadius n)

theorem lpHaarRadius_succ (n : ℕ) :
    intervalLpDyadicRadius (n + 1) = intervalLpDyadicRadius n / 2 := by
  simp [intervalLpDyadicRadius, pow_succ, div_eq_mul_inv]

theorem lpHaarRadius_cancel (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n = 1 := by
  simp [intervalLpDyadicRadius, one_div_pow, Nat.cast_pow]

theorem lpHaarCell_subset (n k : ℕ) (hk : k < 2 ^ n) : lpHaarCell n k ⊆ Icc 0 1 := by
  intro x hx
  have hr := intervalLpDyadicRadius_pos n
  have hk' : (k : ℝ) + 1 ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  have hl : 0 ≤ (k : ℝ) * intervalLpDyadicRadius n := mul_nonneg (Nat.cast_nonneg _) hr.le
  refine ⟨hl.trans hx.1.le, hx.2.trans ?_⟩
  calc
    ((k : ℝ) + 1) * intervalLpDyadicRadius n ≤
        ((2 ^ n : ℕ) : ℝ) * intervalLpDyadicRadius n := mul_le_mul_of_nonneg_right hk' hr.le
    _ = 1 := lpHaarRadius_cancel n

theorem lpHaarCell_measure_volume (n k : ℕ) :
    volume (lpHaarCell n k) = ENNReal.ofReal (intervalLpDyadicRadius n) := by
  rw [lpHaarCell, Real.volume_Ioc]
  congr 1
  ring

theorem lpHaarCell_measure (n k : ℕ) (hk : k < 2 ^ n) :
    (volume.restrict (Icc (0 : ℝ) 1)) (lpHaarCell n k) =
      ENNReal.ofReal (intervalLpDyadicRadius n) := by
  rw [Measure.restrict_apply (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc),
    Set.inter_eq_left.mpr (lpHaarCell_subset n k hk), lpHaarCell_measure_volume]

theorem lpHaarCell_disjoint_sameLevel (n : ℕ) :
    Pairwise (fun k j => Disjoint (lpHaarCell n k) (lpHaarCell n j)) := by
  intro k j hkj
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hr := intervalLpDyadicRadius_pos n
  rcases lt_or_gt_of_ne hkj with h | h
  · have h' : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hz := mul_le_mul_of_nonneg_right h' hr.le
    exact (not_lt_of_ge (hx.2.trans hz)) hy.1
  · have h' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hz := mul_le_mul_of_nonneg_right h' hr.le
    exact (not_lt_of_ge (hy.2.trans hz)) hx.1

theorem lpHaarCell_children (n k : ℕ) :
    lpHaarCell (n + 1) (2 * k) ∪ lpHaarCell (n + 1) (2 * k + 1) = lpHaarCell n k := by
  have hr := (intervalLpDyadicRadius_pos n).le
  have h₁ : ((2 * k : ℕ) : ℝ) * intervalLpDyadicRadius (n + 1) =
      (k : ℝ) * intervalLpDyadicRadius n := by rw [lpHaarRadius_succ]; push_cast; ring
  have h₂ : (((2 * k + 1 : ℕ) : ℝ) + 1) * intervalLpDyadicRadius (n + 1) =
      ((k : ℝ) + 1) * intervalLpDyadicRadius n := by rw [lpHaarRadius_succ]; push_cast; ring
  have h₃ : (((2 * k : ℕ) : ℝ) + 1) * intervalLpDyadicRadius (n + 1) =
      ((2 * k + 1 : ℕ) : ℝ) * intervalLpDyadicRadius (n + 1) := by push_cast; rfl
  unfold lpHaarCell
  rw [h₁, h₂, h₃]
  apply Ioc_union_Ioc_eq_Ioc
  · rw [lpHaarRadius_succ]
    push_cast
    nlinarith
  · rw [lpHaarRadius_succ]
    push_cast
    nlinarith

def lpHaarDyadic (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) : IntervalLp 𝕜 p :=
  lpHaarVector 𝕜 p.val (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
    measurableSet_Ioc measurableSet_Ioc

theorem lpHaarDyadic_norm (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n k : ℕ) (hk : k < 2 ^ n) :
    ‖lpHaarDyadic 𝕜 p n k‖ = intervalLpDyadicRadius n ^ (1 / p.val.toReal) := by
  rw [lpHaarDyadic, lpHaarVector_norm hp
    (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
    measurableSet_Ioc measurableSet_Ioc
    (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)), lpHaarCell_children,
    measureReal_def, lpHaarCell_measure n k hk,
    ENNReal.toReal_ofReal (intervalLpDyadicRadius_pos n).le]

theorem lpHaarDyadic_integral_zero (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k : ℕ) (hk : k < 2 ^ n) :
    ∫ x, lpHaarDyadic 𝕜 p n k x ∂(volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  apply lpHaarVector_integral_zero
  have hk₁ : 2 * k < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hk₂ : 2 * k + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  rw [lpHaarCell_measure (n + 1) (2 * k) hk₁,
    lpHaarCell_measure (n + 1) (2 * k + 1) hk₂]

theorem lpHaarDyadic_zero_off (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∉ lpHaarCell n k → lpHaarDyadic 𝕜 p n k x = 0 := by
  simpa only [lpHaarCell_children] using
    (lpHaarVector_zero_off (𝕜 := 𝕜) (p := p.val) (μ := volume.restrict (Icc (0 : ℝ) 1))
      (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
      measurableSet_Ioc measurableSet_Ioc)

end ThesisCommon
