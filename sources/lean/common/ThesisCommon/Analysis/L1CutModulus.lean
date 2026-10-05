import ThesisCommon.Analysis.L1OperatorLattice
import ThesisCommon.LpCut

/-! Output multiplication by a measurable indicator commutes with the actual
real L1 operator modulus. The proof uses the least dominating positive
operator and the complementary measurable projection. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem lOneCut_mono (B : Set Y) (hB : MeasurableSet B) :
    Monotone (lpCut (𝕜 := ℝ) (p := 1) (μ := ν) B hB) := by
  intro f g hfg
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lpCut_coe B hB f, lpCut_coe B hB g, (Lp.coeFn_le _ _).mpr hfg]
    with y hf hg hfg
  rw [hf, hg]
  by_cases hy : y ∈ B <;> simp [hy, hfg]

theorem lOneCut_abs (B : Set Y) (hB : MeasurableSet B) (f : Lp ℝ 1 ν) :
    lpCut B hB |f| = |lpCut B hB f| := by
  apply Lp.ext
  filter_upwards [lpCut_coe B hB |f|, Lp.coeFn_abs f, Lp.coeFn_abs (lpCut B hB f),
    lpCut_coe B hB f] with y hc hf ha hf'
  rw [hc, ha, hf']
  by_cases hy : y ∈ B <;> simp [hy, hf]

theorem lOneCut_le_self (B : Set Y) (hB : MeasurableSet B)
    {f : Lp ℝ 1 ν} (hf : 0 ≤ f) : lpCut B hB f ≤ f := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [lpCut_coe B hB f, (Lp.coeFn_nonneg f).mpr hf] with y hc hf
  change 0 ≤ f y at hf
  rw [hc]
  by_cases hy : y ∈ B <;> simp [hy, hf]

theorem lOneCut_add_compl (B : Set Y) (hB : MeasurableSet B) (f : Lp ℝ 1 ν) :
    lpCut B hB f + lpCut Bᶜ hB.compl f = f := by
  apply Lp.ext
  filter_upwards [lpCut_coe B hB f, lpCut_coe Bᶜ hB.compl f,
    Lp.coeFn_add (lpCut B hB f) (lpCut Bᶜ hB.compl f)] with y hc hd ha
  rw [ha, Pi.add_apply, hc, hd]
  by_cases hy : y ∈ B <;> simp [hy]

theorem lOneCut_compl_eq_zero (B : Set Y) (hB : MeasurableSet B) (f : Lp ℝ 1 ν) :
    lpCut B hB (lpCut Bᶜ hB.compl f) = 0 := by
  apply Lp.ext
  filter_upwards [lpCut_coe B hB (lpCut Bᶜ hB.compl f), lpCut_coe Bᶜ hB.compl f,
    Lp.coeFn_zero ℝ 1 ν] with y hc hd hz
  rw [hc, hz]
  by_cases hy : y ∈ B <;> simp [hy, hd]

theorem lOneOperatorModulus_outputCut_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    lOneOperatorModulus ((lpCutL B hB).comp T) ≤
      (lpCutL B hB).comp (lOneOperatorModulus T) := by
  intro f hf
  apply lOneOperatorModulus_least _ _ _ f hf
  intro g hg
  change |lpCut B hB (T g)| ≤ lpCut B hB (lOneOperatorModulus T g)
  rw [← lOneCut_abs]
  apply lOneCut_mono
  simpa only [abs_of_nonneg hg] using lOneOperatorModulus_dominates T g

theorem lOneOperatorModulus_outputCut
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    lOneOperatorModulus ((lpCutL B hB).comp T) =
      (lpCutL B hB).comp (lOneOperatorModulus T) := by
  apply le_antisymm (lOneOperatorModulus_outputCut_le T B hB)
  let M := lOneOperatorModulus ((lpCutL B hB).comp T)
  have hdom : ∀ f : Lp ℝ 1 μ, 0 ≤ f → |T f| ≤
      (M + (lpCutL Bᶜ hB.compl).comp (lOneOperatorModulus T)) f := by
    intro f hf
    change |T f| ≤ M f + lpCut Bᶜ hB.compl (lOneOperatorModulus T f)
    calc
      |T f| = lpCut B hB |T f| + lpCut Bᶜ hB.compl |T f| :=
        (lOneCut_add_compl B hB |T f|).symm
      _ ≤ M f + lpCut Bᶜ hB.compl (lOneOperatorModulus T f) := by
        apply add_le_add
        · rw [lOneCut_abs]
          simpa only [abs_of_nonneg hf] using
            lOneOperatorModulus_dominates ((lpCutL B hB).comp T) f
        · apply lOneCut_mono
          simpa only [abs_of_nonneg hf] using lOneOperatorModulus_dominates T f
  intro f hf
  have h := lOneCut_mono B hB (lOneOperatorModulus_least T _ hdom f hf)
  change lpCut B hB (lOneOperatorModulus T f) ≤ M f
  calc
    lpCut B hB (lOneOperatorModulus T f) ≤
        lpCut B hB (M f + lpCut Bᶜ hB.compl (lOneOperatorModulus T f)) := h
    _ = lpCut B hB (M f) := by rw [lpCut_add, lOneCut_compl_eq_zero, add_zero]
    _ ≤ M f := lOneCut_le_self B hB (lOneOperatorModulus_nonneg _ f hf)

theorem abs_outputCut_lOneOperator
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    |(lpCutL B hB).comp T| = (lpCutL B hB).comp |T| := by
  simp only [abs_lOneOperator_eq, lOneOperatorModulus_outputCut]

theorem norm_outputCut_abs_lOneOperator
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    ‖(lpCutL B hB).comp |T|‖ = ‖(lpCutL B hB).comp T‖ := by
  rw [← abs_outputCut_lOneOperator, norm_abs_lOneOperator]

end ThesisCommon
