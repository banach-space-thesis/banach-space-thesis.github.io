import ThesisCommon.Analysis.LpHaarCoefficient
import ThesisCommon.Analysis.LpHaarDyadic

/-! Concrete Haar coefficient maps and finite dyadic biorthogonality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical
namespace ThesisCommon

theorem lpHaarCoefficient_disjoint {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]
    (s t u v : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hu : MeasurableSet u) (hv : MeasurableSet v)
    (hst : Disjoint s t) (hd : Disjoint (s ∪ t) (u ∪ v)) :
    lpHaarCoefficient s t hs ht hst (lpHaarVector (μ := μ) 𝕜 p u v hu hv) = 0 := by
  rw [lpHaarCoefficient_apply]
  have heq : (fun x => lpHaarFunction 𝕜 s t x * lpHaarVector (μ := μ) 𝕜 p u v hu hv x)
      =ᵐ[μ] 0 := by
    filter_upwards [lpHaarVector_zero_off (𝕜 := 𝕜) (μ := μ) (p := p) u v hu hv] with x hx
    by_cases h : x ∈ s ∪ t
    · rw [hx (fun h' => Set.disjoint_left.mp hd h h'), mul_zero]
      rfl
    · simp only [mem_union, not_or] at h
      simp [lpHaarFunction, h.1, h.2]
  rw [integral_congr_ae heq]
  simp

theorem lpHaarCoefficient_constant_on {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (hm : μ s = μ t) (f : Lp 𝕜 p μ) (c : 𝕜)
    (hc : ∀ᵐ x ∂μ, x ∈ s ∪ t → f x = c) :
    lpHaarCoefficient s t hs ht hst f = 0 := by
  rw [lpHaarCoefficient_apply]
  have heq : (fun x => lpHaarFunction 𝕜 s t x * f x)
      =ᵐ[μ] fun x => lpHaarFunction 𝕜 s t x * c := by
    filter_upwards [hc] with x hx
    by_cases h : x ∈ s ∪ t
    · rw [hx h]
    · simp only [mem_union, not_or] at h
      simp [lpHaarFunction, h.1, h.2]
  rw [integral_congr_ae heq, integral_mul_const, lpHaarFunction_integral s t hs ht]
  simp only [measureReal_def, hm, sub_self, zero_mul, mul_zero]

local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

def lpHaarDyadicCoefficient (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) :
    IntervalLp 𝕜 p →L[𝕜] 𝕜 :=
  lpHaarCoefficient (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1))
    measurableSet_Ioc measurableSet_Ioc (lpHaarCell_disjoint_sameLevel (n + 1) (by omega))

theorem lpHaarDyadicCoefficient_self (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k : ℕ) (hk : k < 2 ^ n) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarDyadic 𝕜 p n k) = 1 := by
  apply lpHaarCoefficient_self
  rw [lpHaarCell_children, lpHaarCell_measure n k hk]
  exact (ENNReal.ofReal_pos.mpr (intervalLpDyadicRadius_pos n)).ne'

theorem lpHaarDyadicCoefficient_other (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k j : ℕ) (hkj : k ≠ j) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarDyadic 𝕜 p n j) = 0 := by
  apply lpHaarCoefficient_disjoint
  rw [lpHaarCell_children, lpHaarCell_children]
  exact lpHaarCell_disjoint_sameLevel n hkj

theorem lpHaarDyadicCoefficient_apply_level (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (k j : Fin (2 ^ n)) :
    lpHaarDyadicCoefficient 𝕜 p n k (lpHaarDyadic 𝕜 p n j) = if k = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact lpHaarDyadicCoefficient_self 𝕜 p n k k.isLt
  · exact lpHaarDyadicCoefficient_other 𝕜 p n k j (fun h' => h (Fin.ext h'))

theorem lpHaarDyadic_diagonal_dichotomy (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) (n k : ℕ) (hk : k < 2 ^ n) :
    (1 / 2 : ℝ) ≤ ‖lpHaarDyadicCoefficient 𝕜 p n k (T (lpHaarDyadic 𝕜 p n k))‖ ∨
    (1 / 2 : ℝ) ≤ ‖lpHaarDyadicCoefficient 𝕜 p n k
      ((ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - T) (lpHaarDyadic 𝕜 p n k))‖ := by
  have hsum : lpHaarDyadicCoefficient 𝕜 p n k (T (lpHaarDyadic 𝕜 p n k)) +
      lpHaarDyadicCoefficient 𝕜 p n k
        ((ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - T) (lpHaarDyadic 𝕜 p n k)) = 1 := by
    rw [← map_add]
    simpa using lpHaarDyadicCoefficient_self 𝕜 p n k hk
  have hn := norm_add_le
    (lpHaarDyadicCoefficient 𝕜 p n k (T (lpHaarDyadic 𝕜 p n k)))
    (lpHaarDyadicCoefficient 𝕜 p n k
      ((ContinuousLinearMap.id 𝕜 (IntervalLp 𝕜 p) - T) (lpHaarDyadic 𝕜 p n k)))
  rw [hsum, norm_one] at hn
  by_contra h
  push_neg at h
  linarith [h.1, h.2]

end ThesisCommon
