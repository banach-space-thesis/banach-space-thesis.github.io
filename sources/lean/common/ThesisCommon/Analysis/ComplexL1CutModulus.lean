import ThesisCommon.Analysis.ComplexL1OperatorModulus
import ThesisCommon.Analysis.L1CutModulus

/-! Measurable output cuts commute with the actual complex operator modulus.
The complementary-cut argument uses its least domination property and
works for arbitrary input and output measures. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem complexL1Modulus_cut (B : Set Y) (hB : MeasurableSet B) (f : Lp ℂ 1 ν) :
    complexL1Modulus (lpCut B hB f) = lpCut B hB (complexL1Modulus f) := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (lpCut B hB f), lpCut_coe B hB f,
    lpCut_coe B hB (complexL1Modulus f), complexL1Modulus_coe f] with y hm hc hc' hm'
  rw [hm, hc, hc']
  by_cases hy : y ∈ B <;> simp [hy, hm']

theorem complexL1OperatorModulus_outputCut_le
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    complexL1OperatorModulus ((lpCutL B hB).comp T) ≤
      (lpCutL B hB).comp (complexL1OperatorModulus T) := by
  apply complexL1OperatorModulus_least
  intro f hf
  change complexL1Modulus (lpCut B hB (T (complexL1OfReal μ f))) ≤
    lpCut B hB (complexL1OperatorModulus T f)
  rw [complexL1Modulus_cut]
  apply lOneCut_mono
  simpa only [complexL1Modulus_ofReal, abs_of_nonneg hf] using
    complexL1OperatorModulus_dominates T (complexL1OfReal μ f)

theorem complexL1OperatorModulus_outputCut
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    complexL1OperatorModulus ((lpCutL B hB).comp T) =
      (lpCutL B hB).comp (complexL1OperatorModulus T) := by
  apply le_antisymm (complexL1OperatorModulus_outputCut_le T B hB)
  let M := complexL1OperatorModulus ((lpCutL B hB).comp T)
  have hdom : ∀ f : Lp ℝ 1 μ, 0 ≤ f → complexL1Modulus (T (complexL1OfReal μ f)) ≤
      (M + (lpCutL Bᶜ hB.compl).comp (complexL1OperatorModulus T)) f := by
    intro f hf
    change complexL1Modulus (T (complexL1OfReal μ f)) ≤
      M f + lpCut Bᶜ hB.compl (complexL1OperatorModulus T f)
    calc
      complexL1Modulus (T (complexL1OfReal μ f)) =
          lpCut B hB (complexL1Modulus (T (complexL1OfReal μ f))) +
            lpCut Bᶜ hB.compl (complexL1Modulus (T (complexL1OfReal μ f))) :=
        (lOneCut_add_compl B hB _).symm
      _ ≤ M f + lpCut Bᶜ hB.compl (complexL1OperatorModulus T f) := by
        apply add_le_add
        · rw [← complexL1Modulus_cut]
          simpa only [complexL1Modulus_ofReal, abs_of_nonneg hf] using
            complexL1OperatorModulus_dominates ((lpCutL B hB).comp T) (complexL1OfReal μ f)
        · apply lOneCut_mono
          simpa only [complexL1Modulus_ofReal, abs_of_nonneg hf] using
            complexL1OperatorModulus_dominates T (complexL1OfReal μ f)
  intro f hf
  have h := lOneCut_mono B hB (complexL1OperatorModulus_least T _ hdom f hf)
  change lpCut B hB (complexL1OperatorModulus T f) ≤ M f
  calc
    lpCut B hB (complexL1OperatorModulus T f) ≤
        lpCut B hB (M f + lpCut Bᶜ hB.compl (complexL1OperatorModulus T f)) := h
    _ = lpCut B hB (M f) := by rw [lpCut_add, lOneCut_compl_eq_zero, add_zero]
    _ ≤ M f := lOneCut_le_self B hB (complexL1OperatorModulus_nonneg _ f hf)

theorem norm_outputCut_complexL1OperatorModulus
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 ν) (B : Set Y) (hB : MeasurableSet B) :
    ‖(lpCutL B hB).comp (complexL1OperatorModulus T)‖ = ‖(lpCutL B hB).comp T‖ := by
  rw [← complexL1OperatorModulus_outputCut, norm_complexL1OperatorModulus]

end ThesisCommon
