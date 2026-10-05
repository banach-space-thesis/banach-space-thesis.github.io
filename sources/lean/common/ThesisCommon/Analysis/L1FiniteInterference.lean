import ThesisCommon.Analysis.SigmaL1CoordinateCuts
import ThesisCommon.Analysis.L1SmallAverageLocalization
import ThesisCommon.Analysis.ComplexL1CutModulus

/-! Finite interference for actual L1 operators into arbitrary coproducts.
The positive modulus and its adjoint density localize a finite output tail. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Z I : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  {μ : Measure X} [IsFiniteMeasure μ] (ν : Measure Z)

theorem positiveL1_sigma_finite_interference
    (M : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (sigmaMeasure (fun _ : I => ν)))
    (hM : 0 ≤ M) (A : Set X) (hA : MeasurableSet A) (ha : 0 < μ A)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset I, ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D,
      0 < μ D ∧
      ‖(lpCutL (sigmaIndexSet (↑F : Set I)ᶜ) (sigmaIndexSet_measurable _)).comp
        (M.comp (lpCutL D hD))‖ ≤ η := by
  let e := sigmaL1PartitionEquiv (𝕜 := ℝ) (fun _ : I => ν)
  have hp : 0 < μ.real A := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  obtain ⟨F, hF⟩ := ellOne_finite_tail_small (𝕜 := ℝ)
    (e (M (lOneIndicator μ A hA))) (η * μ.real A) (mul_pos hη hp)
  let B := sigmaIndexSet (Z := Z) (↑F : Set I)ᶜ
  have hB : MeasurableSet B := sigmaIndexSet_measurable _
  let R := (lpCutL (𝕜 := ℝ) (p := 1) B hB).comp M
  have hR : 0 ≤ R := positive_outputCut_nonneg hM B hB
  have hs : ‖R (lOneIndicator μ A hA)‖ < η * μ.real A := by
    rw [← e.norm_map]
    exact (sigmaL1PartitionEquiv_cut (𝕜 := ℝ) ν (↑F : Set I)ᶜ _).symm ▸ hF
  obtain ⟨D, hDA, hD, hd, hnorm⟩ :=
    positiveL1_small_average_localization R hR A hA ha η hη.le hs
  exact ⟨F, D, hDA, hD, hd, hnorm⟩

theorem realL1_sigma_finite_interference
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (sigmaMeasure (fun _ : I => ν)))
    (A : Set X) (hA : MeasurableSet A) (ha : 0 < μ A)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset I, ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D,
      0 < μ D ∧
      ‖(lpCutL (sigmaIndexSet (↑F : Set I)ᶜ) (sigmaIndexSet_measurable _)).comp
        (T.comp (lpCutL D hD))‖ ≤ η := by
  obtain ⟨F, D, hDA, hD, hd, hn⟩ := positiveL1_sigma_finite_interference ν
    (lOneOperatorModulus T) (lOneOperatorModulus_nonneg T) A hA ha η hη
  refine ⟨F, D, hDA, hD, hd, ?_⟩
  let B := sigmaIndexSet (Z := Z) (↑F : Set I)ᶜ
  have hB : MeasurableSet B := sigmaIndexSet_measurable _
  let M := (lpCutL (𝕜 := ℝ) (p := 1) B hB).comp
    ((lOneOperatorModulus T).comp (lpCutL D hD))
  apply ContinuousLinearMap.opNorm_le_bound _ hη.le
  intro f
  have hdom := lOneCut_mono B hB (lOneOperatorModulus_dominates T (lpCut D hD f))
  rw [lOneCut_abs, ← lOneCut_abs D hD f] at hdom
  have hnonneg : 0 ≤ M |f| := positive_outputCut_nonneg
    (positive_inputCut_nonneg (lOneOperatorModulus_nonneg T) D hD) B hB _ (abs_nonneg f)
  calc
    _ ≤ ‖M |f|‖ := norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg hnonneg]; exact hdom)
    _ ≤ ‖M‖ * ‖|f|‖ := M.le_opNorm _
    _ ≤ η * ‖f‖ := by
      rw [norm_abs_eq_norm]
      exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

theorem complexL1_sigma_finite_interference
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 (sigmaMeasure (fun _ : I => ν)))
    (A : Set X) (hA : MeasurableSet A) (ha : 0 < μ A)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset I, ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D,
      0 < μ D ∧
      ‖(lpCutL (𝕜 := ℂ) (sigmaIndexSet (↑F : Set I)ᶜ) (sigmaIndexSet_measurable _)).comp
        (T.comp (lpCutL D hD))‖ ≤ η := by
  obtain ⟨F, D, hDA, hD, hd, hn⟩ := positiveL1_sigma_finite_interference ν
    (complexL1OperatorModulus T) (complexL1OperatorModulus_nonneg T) A hA ha η hη
  refine ⟨F, D, hDA, hD, hd, ?_⟩
  let B := sigmaIndexSet (Z := Z) (↑F : Set I)ᶜ
  have hB : MeasurableSet B := sigmaIndexSet_measurable _
  let M := (lpCutL (𝕜 := ℝ) (p := 1) B hB).comp
    ((complexL1OperatorModulus T).comp (lpCutL D hD))
  apply ContinuousLinearMap.opNorm_le_bound _ hη.le
  intro f
  have hdom := lOneCut_mono B hB (complexL1OperatorModulus_dominates T (lpCut D hD f))
  rw [← complexL1Modulus_cut, complexL1Modulus_cut D hD f] at hdom
  have hnonneg : 0 ≤ M (complexL1Modulus f) := positive_outputCut_nonneg
    (positive_inputCut_nonneg (complexL1OperatorModulus_nonneg T) D hD) B hB _
      (complexL1Modulus_nonneg f)
  calc
    _ = ‖complexL1Modulus (lpCut B hB (T (lpCut D hD f)))‖ :=
      (norm_complexL1Modulus _).symm
    _ ≤ ‖M (complexL1Modulus f)‖ := norm_le_norm_of_abs_le_abs (by
      rw [abs_of_nonneg (complexL1Modulus_nonneg _), abs_of_nonneg hnonneg]
      exact hdom)
    _ ≤ ‖M‖ * ‖complexL1Modulus f‖ := M.le_opNorm _
    _ ≤ η * ‖f‖ := by
      rw [norm_complexL1Modulus]
      exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

end ThesisCommon
