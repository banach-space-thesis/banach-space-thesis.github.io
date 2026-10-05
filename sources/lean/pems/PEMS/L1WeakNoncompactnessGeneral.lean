import PEMS.L1WeakNoncompactness
import ThesisCommon.Analysis.L1WeakUniformTight

/-! The localized weak-noncompactness functional on arbitrary measure
spaces. Uniform tightness and small-set control are proved consequences
of actual real weak compactness; no finite-output or sigma-finiteness
assumption is used in the lower bound or perturbation invariance. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace PEMS
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem smallSetSup_antitone_localization (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {Θ Λ : Set Y} (hΘ : MeasurableSet Θ) (hΛ : MeasurableSet Λ) (hsub : Θ ⊆ Λ)
    {δ : ℝ} (hδ : 0 < δ) : smallSetSup T Λ δ ≤ smallSetSup T Θ δ := by
  apply csSup_le
  · refine ⟨_, ∅, MeasurableSet.empty, empty_subset _, ?_, rfl⟩
    simpa using ENNReal.ofReal_pos.mpr hδ
  · rintro q ⟨B, hB, _, hμB, rfl⟩
    apply (cutOperatorNorm_mono T (hΛ.compl.union hB) (hΘ.compl.union (hB.inter hΘ)) ?_).trans
      (cutOperatorNorm_le_smallSetSup T Θ hΘ (hB.inter hΘ) inter_subset_right
        ((measure_mono inter_subset_left).trans_lt hμB))
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl fun hxΘ => hx (hsub hxΘ)
    · by_cases hxΘ : x ∈ Θ
      · exact Or.inr ⟨hx, hxΘ⟩
      · exact Or.inl hxΘ

theorem alphaTheta_antitone_localization (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {Θ Λ : Set Y} (hΘ : MeasurableSet Θ) (hΛ : MeasurableSet Λ) (hsub : Θ ⊆ Λ) :
    alphaTheta T Λ ≤ alphaTheta T Θ := by
  apply le_csInf
  · exact ⟨_, 1, zero_lt_one, rfl⟩
  · rintro r ⟨δ, hδ, rfl⟩
    exact (alphaTheta_le_smallSetSup T Λ hΛ hδ).trans
      (smallSetSup_antitone_localization T hΘ hΛ hsub hδ)

theorem localizedWeakNoncompactness_le_alphaTheta (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {Θ : Set Y} (hΘ : MeasurableSet Θ) (hνΘ : ν Θ < ∞) :
    localizedWeakNoncompactness T ≤ alphaTheta T Θ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨Λ, hΛ, _, rfl⟩
    exact (alphaTheta_bounds T Λ hΛ).1
  · exact ⟨Θ, hΘ, hνΘ, rfl⟩

theorem localizedWeakNoncompactness_add_le (S T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    localizedWeakNoncompactness (S + T) ≤
      localizedWeakNoncompactness S + localizedWeakNoncompactness T := by
  by_contra hn
  let ε := (localizedWeakNoncompactness (S + T) -
    (localizedWeakNoncompactness S + localizedWeakNoncompactness T)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have happrox : ∀ U : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν,
      ∃ Θ : Set Y, MeasurableSet Θ ∧ ν Θ < ∞ ∧
        alphaTheta U Θ < localizedWeakNoncompactness U + ε := by
    intro U
    obtain ⟨r, ⟨Θ, hΘ, hνΘ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
      (s := {r : ℝ | ∃ Θ : Set Y, MeasurableSet Θ ∧ ν Θ < ∞ ∧ r = alphaTheta U Θ})
      ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
      (show localizedWeakNoncompactness U < localizedWeakNoncompactness U + ε by linarith)
    exact ⟨Θ, hΘ, hνΘ, hr⟩
  obtain ⟨Θ, hΘ, hνΘ, hS⟩ := happrox S
  obtain ⟨Λ, hΛ, hνΛ, hT⟩ := happrox T
  have hfin : ν (Θ ∪ Λ) < ∞ := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hνΘ, hνΛ⟩)
  have hh := (localizedWeakNoncompactness_le_alphaTheta (S + T) (hΘ.union hΛ) hfin).trans
    ((alphaTheta_add_le S T _ (hΘ.union hΛ)).trans (add_le_add
      (alphaTheta_antitone_localization S hΘ (hΘ.union hΛ) subset_union_left)
      (alphaTheta_antitone_localization T hΛ (hΘ.union hΛ) subset_union_right)))
  dsimp [ε] at hS hT
  linarith

theorem cutOperatorNorm_disjoint_union_le (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {A B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B) :
    cutOperatorNorm T (A ∪ B) ≤ cutOperatorNorm T A + cutOperatorNorm T B := by
  have hcut : (lpCutL (𝕜 := 𝕜) (p := 1) (μ := ν) (A ∪ B) (hA.union hB)) =
      lpCutL A hA + lpCutL B hB := by
    apply ContinuousLinearMap.ext
    intro f
    change lpCut (A ∪ B) (hA.union hB) f = lpCut A hA f + lpCut B hB f
    apply Lp.ext
    filter_upwards [lpCut_coe (A ∪ B) (hA.union hB) f, lpCut_coe A hA f,
      lpCut_coe B hB f, Lp.coeFn_add (lpCut A hA f) (lpCut B hB f)] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    exact congrFun (Set.indicator_union_of_disjoint hd f) x
  rw [cutOperatorNorm_eq T _ (hA.union hB), cutOperatorNorm_eq T _ hA,
    cutOperatorNorm_eq T _ hB, hcut, ContinuousLinearMap.add_comp]
  exact norm_add_le _ _

theorem localizedWeakNoncompactness_eq_zero_of_weaklyCompact
    {W : LOne ℝ μ →L[ℝ] LOne ℝ ν} (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness W = 0 := by
  apply le_antisymm _ (localizedWeakNoncompactness_bounds W).1
  by_contra hn
  have hε : 0 < localizedWeakNoncompactness W / 3 := by linarith
  obtain ⟨Θ, hΘ, hνΘ, htail⟩ := hW.exists_finite_measure_cut_compl_norm_le hε
  obtain ⟨δ, hδ, hsmall⟩ := hW.exists_small_cut_norm_le hε
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

theorem localizedWeakNoncompactness_add_weaklyCompact_arbitrary_output
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T + W) = localizedWeakNoncompactness T := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℝ)
  apply le_antisymm
  · simpa only [localizedWeakNoncompactness_eq_zero_of_weaklyCompact hW, add_zero] using
      localizedWeakNoncompactness_add_le T W
  · have hh := localizedWeakNoncompactness_add_le (T + W) (-W)
    simpa only [add_neg_cancel_right, localizedWeakNoncompactness_eq_zero_of_weaklyCompact hnW,
      add_zero] using hh

theorem localizedWeakNoncompactness_sub_weaklyCompact_arbitrary_output
    (T W : LOne ℝ μ →L[ℝ] LOne ℝ ν) (hW : IsWeaklyCompactOperator W) :
    localizedWeakNoncompactness (T - W) = localizedWeakNoncompactness T := by
  have hnW : IsWeaklyCompactOperator (-W) := by simpa using hW.smul (-1 : ℝ)
  simpa only [sub_eq_add_neg] using
    localizedWeakNoncompactness_add_weaklyCompact_arbitrary_output T (-W) hnW

theorem localizedWeakNoncompactness_le_weakEssentialNorm_arbitrary_output
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    localizedWeakNoncompactness T ≤ weakEssentialNorm T := by
  apply le_csInf
  · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    rw [← localizedWeakNoncompactness_sub_weaklyCompact_arbitrary_output T W hW]
    exact (localizedWeakNoncompactness_bounds (T - W)).2

end PEMS
