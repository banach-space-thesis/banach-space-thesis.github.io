import PEMS.ComplexL1WeakNoncompactnessGeneral
import ThesisCommon.Analysis.SupportedWeakEssentialNorm

/-! Source Definition 4.15 and Proposition 4.16 use the genuine supported
weak-essential distance. The lower bound below in fact holds on every
measurable localization, without finiteness or localizability assumptions. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem alphaTheta_eq_zero_of_supported_small_cuts
    (W : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hs : L1OperatorSupportedOn Θ W)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ B, ∀ hB : MeasurableSet B, ν B ≤ ENNReal.ofReal δ →
        ‖(lpCutL B hB).comp W‖ ≤ ε) : alphaTheta W Θ = 0 := by
  apply le_antisymm _ (alphaTheta_bounds W Θ hΘ).1
  by_contra hn
  have hε : 0 < alphaTheta W Θ / 2 := by linarith
  obtain ⟨δ, hδ, hcut⟩ := hsmall _ hε
  have htail : cutOperatorNorm W Θᶜ = 0 := by
    rw [cutOperatorNorm_eq W _ hΘ.compl,
      (l1OperatorSupportedOn_iff_cut_compl_eq_zero Θ hΘ W).mp hs, norm_zero]
  have hsup : smallSetSup W Θ δ ≤ alphaTheta W Θ / 2 := by
    apply csSup_le
    · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
      simpa using ENNReal.ofReal_pos.mpr hδ
    · rintro q ⟨B, hB, hsub, hνB, rfl⟩
      have hd : Disjoint Θᶜ B := disjoint_left.mpr fun y hy hyB => hy (hsub hyB)
      have h := cutOperatorNorm_disjoint_union_le W hΘ.compl hB hd
      rw [htail, zero_add, cutOperatorNorm_eq W _ hB] at h
      exact h.trans (hcut B hB hνB.le)
  have h := (alphaTheta_le_smallSetSup W Θ hΘ hδ).trans hsup
  linarith

theorem alphaTheta_eq_zero_of_real_supported_weaklyCompact
    {W : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hW : IsWeaklyCompactOperator W)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (hs : L1OperatorSupportedOn Θ W) :
    alphaTheta W Θ = 0 :=
  alphaTheta_eq_zero_of_supported_small_cuts W Θ hΘ hs
    (fun _ hε => hW.exists_small_cut_norm_le hε)

theorem alphaTheta_eq_zero_of_complex_supported_weaklyCompact
    {W : LOne ℂ μ →L[ℂ] LOne ℂ ν} (hW : IsWeaklyCompactOperator W)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (hs : L1OperatorSupportedOn Θ W) :
    alphaTheta W Θ = 0 :=
  alphaTheta_eq_zero_of_supported_small_cuts W Θ hΘ hs
    (fun _ hε => hW.exists_small_cut_norm_le_complex hε)

theorem alphaTheta_add_eq_of_zero
    (T W : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hW : alphaTheta W Θ = 0) (hnW : alphaTheta (-W) Θ = 0) :
    alphaTheta (T + W) Θ = alphaTheta T Θ := by
  apply le_antisymm
  · simpa only [hW, add_zero] using alphaTheta_add_le T W Θ hΘ
  · simpa only [add_neg_cancel_right, hnW, add_zero] using
      alphaTheta_add_le (T + W) (-W) Θ hΘ

theorem alphaTheta_add_real_supported_weaklyCompact
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (hs : L1OperatorSupportedOn Θ W) :
    alphaTheta (T + W) Θ = alphaTheta T Θ := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℝ)
  exact alphaTheta_add_eq_of_zero T W Θ hΘ
    (alphaTheta_eq_zero_of_real_supported_weaklyCompact hW Θ hΘ hs)
    (alphaTheta_eq_zero_of_real_supported_weaklyCompact hnW Θ hΘ hs.neg)

theorem alphaTheta_add_complex_supported_weaklyCompact
    (T W : LOne ℂ μ →L[ℂ] LOne ℂ ν) (hW : IsWeaklyCompactOperator W)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) (hs : L1OperatorSupportedOn Θ W) :
    alphaTheta (T + W) Θ = alphaTheta T Θ := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℂ)
  exact alphaTheta_add_eq_of_zero T W Θ hΘ
    (alphaTheta_eq_zero_of_complex_supported_weaklyCompact hW Θ hΘ hs)
    (alphaTheta_eq_zero_of_complex_supported_weaklyCompact hnW Θ hΘ hs.neg)

theorem alphaTheta_le_supportedWeakEssentialNorm_of_zero_on_supported
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hzero : ∀ W : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν, IsWeaklyCompactOperator W →
      L1OperatorSupportedOn Θ W → alphaTheta W Θ = 0) :
    alphaTheta T Θ ≤ supportedWeakEssentialNorm Θ T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, l1OperatorSupportedOn_zero Θ, rfl⟩
  · rintro r ⟨W, hW, hs, rfl⟩
    have h := alphaTheta_add_le (T - W) W Θ hΘ
    rw [sub_add_cancel, hzero W hW hs, add_zero] at h
    exact h.trans (alphaTheta_bounds (T - W) Θ hΘ).2

theorem proposition_4_16_real
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    alphaTheta T Θ ≤ supportedWeakEssentialNorm Θ T :=
  alphaTheta_le_supportedWeakEssentialNorm_of_zero_on_supported T Θ hΘ
    (fun _ hW hs => alphaTheta_eq_zero_of_real_supported_weaklyCompact hW Θ hΘ hs)

theorem proposition_4_16_complex
    (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    alphaTheta T Θ ≤ supportedWeakEssentialNorm Θ T :=
  alphaTheta_le_supportedWeakEssentialNorm_of_zero_on_supported T Θ hΘ
    (fun _ hW hs => alphaTheta_eq_zero_of_complex_supported_weaklyCompact hW Θ hΘ hs)

end PEMS
