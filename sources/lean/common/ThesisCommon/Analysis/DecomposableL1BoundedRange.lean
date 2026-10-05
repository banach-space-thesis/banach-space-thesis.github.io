import ThesisCommon.Analysis.DecomposableL1WeakCompact
import ThesisCommon.Analysis.DecomposableL1Order
import ThesisCommon.Analysis.L1AdjointOne

/-! A uniform pointwise range bound survives the actual arbitrary-index
L1 gluing. The proof uses the absolutely summable family of input norms. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

theorem decomposableL1Operator_apply_norm_le_of_bound
    (s : I → Set X) (hμ : Measure.sum (fun i => μ.restrict (s i)) = μ)
    (A : ∀ i, Lp ℝ 1 (μ.restrict (s i)) →L[ℝ] Lp ℝ 1 ν)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    {D : ℝ}
    (hbound : ∀ i f, ∀ᵐ y ∂ν, ‖A i f y‖ ≤ D * ‖f‖)
    (f : Lp ℝ 1 μ) :
    ∀ᵐ y ∂ν, ‖decomposableL1Operator s hμ A C hC hA f y‖ ≤ D * ‖f‖ := by
  let T := decomposableL1Operator s hμ A C hC hA
  let one := lOneIndicator ν univ MeasurableSet.univ
  have hle (f : Lp ℝ 1 μ) : T f ≤ (D * ‖f‖) • one := by
    let e := decomposableLpPartition (𝕜 := ℝ) (E := ℝ)
      (by norm_num : (1 : ENNReal) ≠ ⊤) s hμ
    have hr := ((lpOneFamily_hasSum_norm (e f)).mul_left D).smul_const one
    have hl := (summable_norm_lpOneFamily_operators A C hC hA (e f)).of_norm
    have hterm (i : I) : A i (e f i) ≤ (D * ‖e f i‖) • one := by
      apply (Lp.coeFn_le _ _).mp
      filter_upwards [hbound i (e f i), Lp.coeFn_smul (D * ‖e f i‖) one,
        lOneIndicator_coe (μ := ν) univ MeasurableSet.univ] with y hb he ho
      rw [he]
      change A i (e f i) y ≤ (D * ‖e f i‖) * one y
      rw [show one y = 1 by simpa only [indicator_univ, Pi.one_apply] using ho]
      exact (le_abs_self _).trans (by simpa only [mul_one] using hb)
    have ht := hl.tsum_le_tsum hterm hr.summable
    rw [hr.tsum_eq, e.norm_map] at ht
    exact ht
  have habs : |T f| ≤ (D * ‖f‖) • one := by
    change T f ⊔ -T f ≤ _
    exact sup_le (hle f) (by simpa only [map_neg, norm_neg] using hle (-f))
  filter_upwards [(Lp.coeFn_le _ _).mpr habs, Lp.coeFn_abs (T f),
    Lp.coeFn_smul (D * ‖f‖) one, lOneIndicator_coe (μ := ν) univ MeasurableSet.univ]
    with y hb ha hs ho
  rw [ha, hs] at hb
  change ‖T f y‖ ≤ D * ‖f‖
  change |T f y| ≤ (D * ‖f‖) * one y at hb
  rw [show one y = 1 by simpa only [indicator_univ, Pi.one_apply] using ho, mul_one] at hb
  exact hb

end ThesisCommon
