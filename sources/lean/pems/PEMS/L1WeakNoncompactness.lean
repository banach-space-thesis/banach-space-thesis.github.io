import PEMS.MeasureChecks
import ThesisCommon.Analysis.L1WeakUniformIntegrable
import ThesisCommon.WeakCompact

/-! The localized small-set functional is bounded by the actual weak essential
norm when the output measure is finite. The proof uses the necessary
Dunford--Pettis estimate in the genuine weak topology. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem cutOperatorNorm_mono (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {A B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    cutOperatorNorm T A ≤ cutOperatorNorm T B := by
  rw [cutOperatorNorm_eq T A hA, cutOperatorNorm_eq T B hB]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply le_trans (b := ‖lpCut B hB (T f)‖) _ (((lpCutL B hB).comp T).le_opNorm f)
  change ‖lpCut A hA (T f)‖ ≤ _
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpCut_coe A hA (T f), lpCut_coe B hB (T f)] with y hyA hyB
  rw [hyA, hyB]
  by_cases hy : y ∈ A
  · simp [hy, hAB hy]
  · simp [hy]

theorem cutOperatorNorm_add_le (S T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (A : Set Y) (hA : MeasurableSet A) :
    cutOperatorNorm (S + T) A ≤ cutOperatorNorm S A + cutOperatorNorm T A := by
  simp only [cutOperatorNorm_eq _ A hA, ContinuousLinearMap.comp_add]
  exact norm_add_le _ _

theorem cutOperatorNorm_le_smallSetSup (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ : ℝ}
    {B : Set Y} (hB : MeasurableSet B) (hsub : B ⊆ Θ) (hμB : ν B < ENNReal.ofReal δ) :
    cutOperatorNorm T (Θᶜ ∪ B) ≤ smallSetSup T Θ δ := by
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    rintro q ⟨A, hA, _, _, rfl⟩
    exact cutOperatorNorm_le_norm T _ (hΘ.compl.union hA)
  · exact ⟨B, hB, hsub, hμB, rfl⟩

theorem smallSetSup_mono_delta (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ η : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η) :
    smallSetSup T Θ δ ≤ smallSetSup T Θ η := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, hsub, hμB, rfl⟩
    exact cutOperatorNorm_le_smallSetSup T Θ hΘ hB hsub
      (hμB.trans_le (ENNReal.ofReal_le_ofReal hδη))

theorem smallSetSup_add_le (S T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ : ℝ} (hδ : 0 < δ) :
    smallSetSup (S + T) Θ δ ≤ smallSetSup S Θ δ + smallSetSup T Θ δ := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, hsub, hμB, rfl⟩
    exact (cutOperatorNorm_add_le S T _ (hΘ.compl.union hB)).trans
      (add_le_add (cutOperatorNorm_le_smallSetSup S Θ hΘ hB hsub hμB)
        (cutOperatorNorm_le_smallSetSup T Θ hΘ hB hsub hμB))

theorem alphaTheta_le_smallSetSup (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ : ℝ} (hδ : 0 < δ) :
    alphaTheta T Θ ≤ smallSetSup T Θ δ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨η, hη, rfl⟩
    exact (smallSetSup_bounds T Θ hΘ η hη).1
  · exact ⟨δ, hδ, rfl⟩

theorem alphaTheta_add_le (S T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) :
    alphaTheta (S + T) Θ ≤ alphaTheta S Θ + alphaTheta T Θ := by
  by_contra hn
  have hg : 0 < (alphaTheta (S + T) Θ - (alphaTheta S Θ + alphaTheta T Θ)) / 3 := by
    linarith
  let ε := (alphaTheta (S + T) Θ - (alphaTheta S Θ + alphaTheta T Θ)) / 3
  have happrox : ∀ U : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν,
      ∃ δ : ℝ, 0 < δ ∧ smallSetSup U Θ δ < alphaTheta U Θ + ε := by
    intro U
    obtain ⟨r, ⟨δ, hδ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
      (s := {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup U Θ δ})
      ⟨_, 1, zero_lt_one, rfl⟩
      (show alphaTheta U Θ < alphaTheta U Θ + ε by dsimp [ε]; linarith)
    exact ⟨δ, hδ, hr⟩
  obtain ⟨δ, hδ, hS⟩ := happrox S
  obtain ⟨η, hη, hT⟩ := happrox T
  have hm : 0 < min δ η := lt_min hδ hη
  have hh := (alphaTheta_le_smallSetSup (S + T) Θ hΘ hm).trans
    ((smallSetSup_add_le S T Θ hΘ hm).trans
      (add_le_add (smallSetSup_mono_delta S Θ hΘ hm (min_le_left _ _))
        (smallSetSup_mono_delta T Θ hΘ hm (min_le_right _ _))))
  dsimp [ε] at hS hT
  linarith

theorem smallSetSup_univ_le (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) {δ : ℝ} (hδ : 0 < δ) :
    smallSetSup T univ δ ≤ smallSetSup T Θ δ := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, _, hμB, rfl⟩
    simp only [compl_univ, empty_union]
    apply (cutOperatorNorm_mono T hB (hΘ.compl.union (hB.inter hΘ)) ?_).trans
      (cutOperatorNorm_le_smallSetSup T Θ hΘ (hB.inter hΘ) inter_subset_right
        ((measure_mono inter_subset_left).trans_lt hμB))
    intro x hx
    by_cases hxΘ : x ∈ Θ
    · exact Or.inr ⟨hx, hxΘ⟩
    · exact Or.inl hxΘ

theorem alphaTheta_univ_le (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    (Θ : Set Y) (hΘ : MeasurableSet Θ) : alphaTheta T univ ≤ alphaTheta T Θ := by
  change alphaTheta T univ ≤ sInf {r : ℝ | ∃ δ : ℝ, 0 < δ ∧ r = smallSetSup T Θ δ}
  apply le_csInf
  · exact ⟨smallSetSup T Θ 1, 1, zero_lt_one, rfl⟩
  · rintro r ⟨δ, hδ, rfl⟩
    exact (alphaTheta_le_smallSetSup T univ MeasurableSet.univ hδ).trans
      (smallSetSup_univ_le T Θ hΘ hδ)

theorem localizedWeakNoncompactness_eq_alphaTheta_univ [IsFiniteMeasure ν]
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    localizedWeakNoncompactness T = alphaTheta T univ := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨Θ, hΘ, _, rfl⟩
      exact (alphaTheta_bounds T Θ hΘ).1
    · exact ⟨univ, MeasurableSet.univ, measure_lt_top _ _, rfl⟩
  · apply le_csInf
    · exact ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
    · rintro r ⟨Θ, hΘ, _, rfl⟩
      exact alphaTheta_univ_le T Θ hΘ

theorem alphaTheta_univ_eq_zero_of_weaklyCompact
    {T : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hT : IsWeaklyCompactOperator T) :
    alphaTheta T univ = 0 := by
  apply le_antisymm _ (alphaTheta_bounds T univ MeasurableSet.univ).1
  by_contra hn
  have hpos : 0 < alphaTheta T univ / 2 := by linarith
  obtain ⟨δ, hδ, hcut⟩ := hT.exists_small_cut_norm_le hpos
  have hs : smallSetSup T univ δ ≤ alphaTheta T univ / 2 := by
    apply csSup_le
    · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
      simpa using ENNReal.ofReal_pos.mpr hδ
    · rintro q ⟨B, hB, _, hμB, rfl⟩
      simpa only [compl_univ, empty_union, cutOperatorNorm_eq T B hB] using hcut B hB hμB.le
  have hh := (alphaTheta_le_smallSetSup T univ MeasurableSet.univ hδ).trans hs
  linarith

theorem alphaTheta_univ_add_weaklyCompact
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W) :
    alphaTheta (T + W) univ = alphaTheta T univ := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℝ)
  apply le_antisymm
  · simpa only [alphaTheta_univ_eq_zero_of_weaklyCompact hW, add_zero] using
      alphaTheta_add_le T W univ MeasurableSet.univ
  · have hh := alphaTheta_add_le (T + W) (-W) univ MeasurableSet.univ
    simpa only [add_neg_cancel_right, alphaTheta_univ_eq_zero_of_weaklyCompact hnW,
      add_zero] using hh

theorem localizedWeakNoncompactness_add_weaklyCompact [IsFiniteMeasure ν]
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T + W) = localizedWeakNoncompactness T := by
  simpa only [localizedWeakNoncompactness_eq_alphaTheta_univ] using
    alphaTheta_univ_add_weaklyCompact T W hW

theorem localizedWeakNoncompactness_sub_weaklyCompact [IsFiniteMeasure ν]
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T - W) = localizedWeakNoncompactness T := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℝ)
  simpa only [sub_eq_add_neg] using localizedWeakNoncompactness_add_weaklyCompact T (-W) hnW

theorem localizedWeakNoncompactness_le_weakEssentialNorm [IsFiniteMeasure ν]
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    localizedWeakNoncompactness T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    rw [← localizedWeakNoncompactness_sub_weaklyCompact T W hW]
    exact (localizedWeakNoncompactness_bounds (T - W)).2

end PEMS
