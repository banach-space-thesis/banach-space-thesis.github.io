import ThesisCommon.Analysis.L1FiniteInterference
import ThesisCommon.Analysis.AtomlessStandardBorelL1Equiv
import ThesisCommon.Analysis.EllOneFiniteInterferenceReduction

/-! The measurable coproduct estimate gives finite interference in the
actual arbitrary-index ell1 sum, with genuine localized model retractions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Z I : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  {μ : Measure X} [IsFiniteMeasure μ] (ν : Measure Z)

theorem realL1_ellOne_finite_interference
    (T : Lp ℝ 1 μ →L[ℝ] EllOneSum I (Lp ℝ 1 ν))
    (A : Set X) (hA : MeasurableSet A) (ha : 0 < μ A) (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset I, ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D,
      0 < μ D ∧ ‖(lpCoordinateProjection (𝕜 := ℝ) 1 (↑F : Set I)ᶜ).comp
        (T.comp (lpCutL D hD))‖ ≤ η := by
  let e := sigmaL1PartitionEquiv (𝕜 := ℝ) (fun _ : I => ν)
  let S := e.symm.toLinearIsometry.toContinuousLinearMap.comp T
  obtain ⟨F, D, hDA, hD, hd, hn⟩ := realL1_sigma_finite_interference ν S A hA ha η hη
  refine ⟨F, D, hDA, hD, hd, ?_⟩
  let B := sigmaIndexSet (Z := Z) (↑F : Set I)ᶜ
  have hB : MeasurableSet B := sigmaIndexSet_measurable _
  let Q := (lpCutL (𝕜 := ℝ) (p := 1) B hB).comp (S.comp (lpCutL D hD))
  apply ContinuousLinearMap.opNorm_le_bound _ hη.le
  intro f
  have heq : e (Q f) = lpCoordinateProjection (𝕜 := ℝ) 1 (↑F : Set I)ᶜ
      (T (lpCut D hD f)) := by
    change e (lpCut B hB (S (lpCut D hD f))) = _
    rw [sigmaL1PartitionEquiv_cut]
    change lpCoordinateProjection (𝕜 := ℝ) 1 (↑F : Set I)ᶜ
      (e (e.symm (T (lpCut D hD f)))) = _
    rw [e.apply_symm_apply]
  calc
    _ = ‖Q f‖ := (congrArg norm heq).symm.trans (e.norm_map _)
    _ ≤ ‖Q‖ * ‖f‖ := Q.le_opNorm f
    _ ≤ η * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg f)

theorem complexL1_ellOne_finite_interference
    (T : Lp ℂ 1 μ →L[ℂ] EllOneSum I (Lp ℂ 1 ν))
    (A : Set X) (hA : MeasurableSet A) (ha : 0 < μ A) (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset I, ∃ D : Set X, D ⊆ A ∧ ∃ hD : MeasurableSet D,
      0 < μ D ∧ ‖(lpCoordinateProjection (𝕜 := ℂ) 1 (↑F : Set I)ᶜ).comp
        (T.comp (lpCutL D hD))‖ ≤ η := by
  let e := sigmaL1PartitionEquiv (𝕜 := ℂ) (fun _ : I => ν)
  let S := e.symm.toLinearIsometry.toContinuousLinearMap.comp T
  obtain ⟨F, D, hDA, hD, hd, hn⟩ := complexL1_sigma_finite_interference ν S A hA ha η hη
  refine ⟨F, D, hDA, hD, hd, ?_⟩
  let B := sigmaIndexSet (Z := Z) (↑F : Set I)ᶜ
  have hB : MeasurableSet B := sigmaIndexSet_measurable _
  let Q := (lpCutL (𝕜 := ℂ) (p := 1) B hB).comp (S.comp (lpCutL D hD))
  apply ContinuousLinearMap.opNorm_le_bound _ hη.le
  intro f
  have heq : e (Q f) = lpCoordinateProjection (𝕜 := ℂ) 1 (↑F : Set I)ᶜ
      (T (lpCut D hD f)) := by
    change e (lpCut B hB (S (lpCut D hD f))) = _
    rw [sigmaL1PartitionEquiv_cut]
    change lpCoordinateProjection (𝕜 := ℂ) 1 (↑F : Set I)ᶜ
      (e (e.symm (T (lpCut D hD f)))) = _
    rw [e.apply_symm_apply]
  calc
    _ = ‖Q f‖ := (congrArg norm heq).symm.trans (e.norm_map _)
    _ ≤ ‖Q‖ * ‖f‖ := Q.le_opNorm f
    _ ≤ η * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg f)

theorem atomlessL1_has_finite_interference_of_capture
    {𝕜 : Type*} [RCLike 𝕜] [StandardBorelSpace X] [NoAtoms μ] (hμ : μ ≠ 0)
    (hcapture : ∀ (T : Lp 𝕜 1 μ →L[𝕜] EllOneSum I (Lp 𝕜 1 μ)) (η : ℝ), 0 < η →
      ∃ F : Finset I, ∃ D : Set X, ∃ hD : MeasurableSet D, 0 < μ D ∧
        ‖(lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set I)ᶜ).comp
          (T.comp (lpCutL D hD))‖ ≤ η) :
    HasEllOneFiniteInterference (𝕜 := 𝕜) (Γ := I) (X := Lp 𝕜 1 μ) := by
  intro T η hη
  obtain ⟨F, D, hD, hd, hn⟩ := hcapture T η hη
  let e : Lp 𝕜 1 μ ≃ₗᵢ[𝕜] Lp 𝕜 1 (μ.restrict D) :=
    (atomlessStandardBorelL1Equiv 𝕜 μ hμ).trans (atomlessRestrictedL1Equiv 𝕜 μ D hd).symm
  let E := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := μ) D hD).toContinuousLinearMap
  let P := lebesgueLpRestrict (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := μ) D
  let J := E.comp e.toLinearIsometry.toContinuousLinearMap
  let R := e.symm.toLinearIsometry.toContinuousLinearMap.comp P
  have hnE : ‖E‖ ≤ 1 := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := 1) (μ := μ) D hD).norm_toContinuousLinearMap_le
  have hnP : ‖P‖ ≤ 1 := norm_lebesgueLpRestrict_le D
  have hnJ : ‖J‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul hnE e.toLinearIsometry.norm_toContinuousLinearMap_le
      (norm_nonneg _) zero_le_one)
  have hnR : ‖R‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul e.symm.toLinearIsometry.norm_toContinuousLinearMap_le hnP
      (norm_nonneg _) zero_le_one)
  have hRJ : R.comp J = ContinuousLinearMap.id 𝕜 _ := by
    apply ContinuousLinearMap.ext
    intro f
    change e.symm (lebesgueLpRestrict (𝕜 := 𝕜) D (lebesgueLpExtend (𝕜 := 𝕜) D hD (e f))) = f
    rw [lebesgueLpRestrict_extend, e.symm_apply_apply]
  have hcutJ : (lpCutL (𝕜 := 𝕜) (p := 1) D hD).comp J = J := by
    apply ContinuousLinearMap.ext
    intro f
    change lpCut D hD (lebesgueLpExtend (𝕜 := 𝕜) D hD (e f)) = _
    have he := DFunLike.congr_fun (lebesgueLpExtend_comp_restrict (𝕜 := 𝕜)
      (p := 1) (μ := μ) D hD) (lebesgueLpExtend (𝕜 := 𝕜) D hD (e f))
    change lebesgueLpExtend (𝕜 := 𝕜) D hD
      (lebesgueLpRestrict (𝕜 := 𝕜) D (lebesgueLpExtend (𝕜 := 𝕜) D hD (e f))) = _ at he
    rw [lebesgueLpRestrict_extend] at he
    exact he.symm
  refine ⟨F, J, R, hnJ, hnR, hRJ, ?_⟩
  have he : (lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set I)ᶜ).comp (T.comp J) =
      ((lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set I)ᶜ).comp
        (T.comp (lpCutL D hD))).comp J := by
    simp only [ContinuousLinearMap.comp_assoc, hcutJ]
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [mul_one] using mul_le_mul hn hnJ (norm_nonneg _) hη.le)

theorem real_atomlessL1_hasEllOneFiniteInterference [StandardBorelSpace X] [NoAtoms μ]
    (hμ : μ ≠ 0) : HasEllOneFiniteInterference (𝕜 := ℝ) (Γ := I) (X := Lp ℝ 1 μ) := by
  apply atomlessL1_has_finite_interference_of_capture hμ
  intro T η hη
  obtain ⟨F, D, _, hD, hd, hn⟩ := realL1_ellOne_finite_interference μ T univ
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hμ) η hη
  exact ⟨F, D, hD, hd, hn⟩

theorem complex_atomlessL1_hasEllOneFiniteInterference [StandardBorelSpace X] [NoAtoms μ]
    (hμ : μ ≠ 0) : HasEllOneFiniteInterference (𝕜 := ℂ) (Γ := I) (X := Lp ℂ 1 μ) := by
  apply atomlessL1_has_finite_interference_of_capture hμ
  intro T η hη
  obtain ⟨F, D, _, hD, hd, hn⟩ := complexL1_ellOne_finite_interference μ T univ
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hμ) η hη
  exact ⟨F, D, hD, hd, hn⟩

end ThesisCommon
