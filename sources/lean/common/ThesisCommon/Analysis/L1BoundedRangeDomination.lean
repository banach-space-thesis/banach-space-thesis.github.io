import ThesisCommon.Analysis.IntegralKernelWeakCompact
import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.Analysis.LatticeSignLift
import ThesisCommon.Analysis.WeakCalkinNorm

/-! Positive approximation by operators with uniformly bounded pointwise ranges
gives weak compactness of every dominated real L1 operator. No finiteness
assumption is made on the input measure. -/
noncomputable section
open MeasureTheory Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def HasPositiveBoundedRangeApproximants (H : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν,
    0 ≤ B ∧ B ≤ H ∧ ‖H - B‖ < ε ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ C * ‖f‖

theorem lOneOperator_bounded_range_of_abs_le
    {W B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hWB : |W| ≤ B)
    {C : ℝ} (hB : ∀ f, ∀ᵐ y ∂ν, ‖B f y‖ ≤ C * ‖f‖) :
    ∀ f, ∀ᵐ y ∂ν, ‖W f y‖ ≤ C * ‖f‖ := by
  intro f
  have hdom : |W f| ≤ B |f| := by
    exact (lOneOperatorModulus_dominates W f).trans
      (by simpa only [abs_lOneOperator_eq] using hWB |f| (abs_nonneg f))
  filter_upwards [(Lp.coeFn_le _ _).mpr hdom, Lp.coeFn_abs (W f), hB |f|]
    with y hd ha hb
  change |W f| y ≤ B |f| y at hd
  rw [ha] at hd
  calc
    ‖W f y‖ = |W f y| := Real.norm_eq_abs _
    _ ≤ B |f| y := hd
    _ ≤ ‖B |f| y‖ := le_abs_self _
    _ ≤ C * ‖f‖ := by simpa only [norm_abs_eq_norm] using hb

theorem norm_sub_latticeSignLift_inf_le
    {W H B : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hWH : |W| ≤ H) (hB : 0 ≤ B) (hBH : B ≤ H) :
    ‖W - latticeSignLift W (|W| ⊓ B)‖ ≤ ‖H - B‖ := by
  apply norm_le_norm_of_abs_le_abs
  rw [abs_sub_latticeSignLift W (le_inf (abs_nonneg W) hB) inf_le_left,
    abs_of_nonneg (sub_nonneg.mpr hBH), sub_inf, sub_self]
  exact sup_le (sub_nonneg.mpr hBH) (sub_le_sub_right hWH B)

theorem HasPositiveBoundedRangeApproximants.weaklyCompact_of_abs_le
    [IsFiniteMeasure ν] {H W : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}
    (hH : HasPositiveBoundedRangeApproximants H) (hWH : |W| ≤ H) :
    IsWeaklyCompactOperator W := by
  apply (weakEssentialNorm_eq_zero_iff W).mp
  apply le_antisymm _ (weakEssentialNorm_nonneg W)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨B, hB, hBH, herr, C, hC, hbound⟩ := hH ε hε
  let V := latticeSignLift W (|W| ⊓ B)
  have hVB : |V| ≤ B := by
    dsimp only [V]
    rw [abs_latticeSignLift W (le_inf (abs_nonneg W) hB) inf_le_left]
    exact inf_le_right
  have hV : IsWeaklyCompactOperator V :=
    weaklyCompact_of_bounded_range V (lOneOperator_bounded_range_of_abs_le hVB hbound) hC
  have hn : ‖W - V‖ < ε :=
    (norm_sub_latticeSignLift_inf_le hWH hB hBH).trans_lt herr
  simpa only [zero_add] using (weakEssentialNorm_le W hV).trans hn.le

end ThesisCommon
