import PEMS.L1WeakNoncompactnessGeneral
import ThesisCommon.Analysis.ComplexL1WeakUniformIntegrable

/-! Actual complex weak compactness forces vanishing localized small-set
value, including arbitrary output measures. Perturbation invariance and
the lower bound by the genuine weak essential norm follow. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem alphaTheta_univ_eq_zero_of_complex_weaklyCompact
    {W : LOne ℂ μ →L[ℂ] LOne ℂ ν} (hW : IsWeaklyCompactOperator W) :
    alphaTheta W univ = 0 := by
  apply le_antisymm _ (alphaTheta_bounds W univ MeasurableSet.univ).1
  by_contra hn
  have hε : 0 < alphaTheta W univ / 2 := by linarith
  obtain ⟨δ, hδ, hcut⟩ := hW.exists_small_cut_norm_le_complex hε
  have hs : smallSetSup W univ δ ≤ alphaTheta W univ / 2 := by
    apply csSup_le
    · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
      simpa using ENNReal.ofReal_pos.mpr hδ
    · rintro q ⟨B, hB, _, hνB, rfl⟩
      simpa only [compl_univ, empty_union, cutOperatorNorm_eq W B hB] using hcut B hB hνB.le
  have hh := (alphaTheta_le_smallSetSup W univ MeasurableSet.univ hδ).trans hs
  linarith

theorem localizedWeakNoncompactness_eq_zero_of_complex_weaklyCompact
    {W : LOne ℂ μ →L[ℂ] LOne ℂ ν} (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness W = 0 := by
  apply le_antisymm _ (localizedWeakNoncompactness_bounds W).1
  by_contra hn
  have hε : 0 < localizedWeakNoncompactness W / 3 := by linarith
  obtain ⟨Θ, hΘ, hνΘ, htail⟩ := hW.exists_finite_measure_cut_compl_norm_le_complex hε
  obtain ⟨δ, hδ, hsmall⟩ := hW.exists_small_cut_norm_le_complex hε
  have hs : smallSetSup W Θ δ ≤ 2 * (localizedWeakNoncompactness W / 3) := by
    apply csSup_le
    · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
      simpa using ENNReal.ofReal_pos.mpr hδ
    · rintro q ⟨B, hB, hsub, hνB, rfl⟩
      have hd : Disjoint Θᶜ B := Set.disjoint_left.mpr fun x hx hxB => hx (hsub hxB)
      have hb := hsmall B hB hνB.le
      have hh := cutOperatorNorm_disjoint_union_le W hΘ.compl hB hd
      rw [cutOperatorNorm_eq W _ hΘ.compl, cutOperatorNorm_eq W _ hB] at hh
      linarith
  have hh := (localizedWeakNoncompactness_le_alphaTheta W hΘ hνΘ).trans
    ((alphaTheta_le_smallSetSup W Θ hΘ hδ).trans hs)
  linarith

theorem localizedWeakNoncompactness_add_complex_weaklyCompact
    (T W : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T + W) = localizedWeakNoncompactness T := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℂ)
  apply le_antisymm
  · simpa only [localizedWeakNoncompactness_eq_zero_of_complex_weaklyCompact hW, add_zero] using
      localizedWeakNoncompactness_add_le T W
  · have hh := localizedWeakNoncompactness_add_le (T + W) (-W)
    simpa only [add_neg_cancel_right, localizedWeakNoncompactness_eq_zero_of_complex_weaklyCompact hnW,
      add_zero] using hh

theorem localizedWeakNoncompactness_sub_complex_weaklyCompact
    (T W : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T - W) = localizedWeakNoncompactness T := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℂ)
  simpa only [sub_eq_add_neg] using
    localizedWeakNoncompactness_add_complex_weaklyCompact T (-W) hnW

theorem localizedWeakNoncompactness_le_complex_weakEssentialNorm
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) :
    localizedWeakNoncompactness T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    rw [← localizedWeakNoncompactness_sub_complex_weaklyCompact T W hW]
    exact (localizedWeakNoncompactness_bounds (T - W)).2

end PEMS
