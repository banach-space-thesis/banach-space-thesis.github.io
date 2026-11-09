import PEMS.L1WeakNoncompactnessGeneral
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! The actual truncation integrals in Corollary 5.14. On a fixed measurable
localization, the pointwise excess above c is bounded by the small-cut
profile, using Markov's inequality. In the other direction a small cut
captures at most the excess plus c times its measure. -/

noncomputable section
open Set MeasureTheory ThesisCommon
open scoped ENNReal

namespace PEMS

variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

def section5TruncationTail (A : Set Y) (c : ℝ) (f : LOne 𝕜 ν) : ℝ :=
  ∫ y, max (‖f y‖ - A.indicator (fun _ => c) y) 0 ∂ν

def section5TruncationProfile (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (A : Set Y) (c : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ f : LOne 𝕜 μ, ‖f‖ ≤ 1 ∧ r = section5TruncationTail A c (T f)}

def section5LocalizedTruncationInf (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) : ℝ :=
  sInf {r : ℝ | ∃ A : Set Y, MeasurableSet A ∧ ν A < ⊤ ∧
    ∃ c : ℝ, 0 < c ∧ r = section5TruncationProfile T A c}

def section5UnivTruncationInf (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) : ℝ :=
  sInf {r : ℝ | ∃ c : ℝ, 0 < c ∧ r = section5TruncationProfile T univ c}

private theorem section5_tail_integrable {A : Set Y} (hA : MeasurableSet A) {c : ℝ}
    (hc : 0 ≤ c) (f : LOne 𝕜 ν) :
    Integrable (fun y => max (‖f y‖ - A.indicator (fun _ => c) y) 0) ν := by
  have hfi := (L1.integrable_coeFn f).norm
  apply hfi.mono'
  · exact ((hfi.aemeasurable.sub
      ((measurable_const (a := c)).indicator hA).aemeasurable).max
      aemeasurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (sub_le_self _ (indicator_nonneg (fun _ _ => hc) _)) (norm_nonneg _)

private theorem section5_tail_bounds {A : Set Y} (hA : MeasurableSet A) {c : ℝ}
    (hc : 0 ≤ c) (f : LOne 𝕜 ν) :
    0 ≤ section5TruncationTail A c f ∧ section5TruncationTail A c f ≤ ‖f‖ := by
  constructor
  · exact integral_nonneg (fun _ => le_max_right _ _)
  · rw [L1.norm_eq_integral_norm]
    exact integral_mono (section5_tail_integrable hA hc f) (L1.integrable_coeFn f).norm
      (fun y => max_le (sub_le_self _ (indicator_nonneg (fun _ _ => hc) _)) (norm_nonneg _))

private theorem section5_profile_bddAbove (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) {A : Set Y}
    (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c) :
    BddAbove {r : ℝ | ∃ f : LOne 𝕜 μ, ‖f‖ ≤ 1 ∧ r = section5TruncationTail A c (T f)} := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact (section5_tail_bounds hA hc _).2.trans <|
    (T.le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg _) hf)

private theorem section5_tail_le_profile (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) {A : Set Y}
    (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c) {f : LOne 𝕜 μ} (hf : ‖f‖ ≤ 1) :
    section5TruncationTail A c (T f) ≤ section5TruncationProfile T A c :=
  le_csSup (section5_profile_bddAbove T hA hc) ⟨f, hf, rfl⟩

private theorem section5_profile_nonneg (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) {A : Set Y}
    (hA : MeasurableSet A) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ section5TruncationProfile T A c :=
  (section5_tail_bounds hA hc (T 0)).1.trans (section5_tail_le_profile T hA hc (by simp))

private theorem section5_norm_cut_eq_integral (A : Set Y) (hA : MeasurableSet A)
    (f : LOne 𝕜 ν) :
    ‖lpCut A hA f‖ = ∫ y, A.indicator (fun y => ‖f y‖) y ∂ν := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [lpCut_coe A hA f] with y hy
  rw [hy]
  by_cases h : y ∈ A <;> simp [h]

private theorem section5_profile_le_smallSetSup (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {A : Set Y} (hA : MeasurableSet A) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hsize : ‖T‖ < c * δ) : section5TruncationProfile T A c ≤ smallSetSup T A δ := by
  apply csSup_le
  · exact ⟨_, 0, by simp, rfl⟩
  rintro _ ⟨f, hf, rfl⟩
  let g := (Lp.aestronglyMeasurable (T f)).mk (T f)
  have hfg : (T f : Y → 𝕜) =ᵐ[ν] g := (Lp.aestronglyMeasurable (T f)).ae_eq_mk
  have hg : Measurable g := (Lp.aestronglyMeasurable (T f)).stronglyMeasurable_mk.measurable
  let B := A ∩ {y | c ≤ ‖g y‖}
  have hB : MeasurableSet B := hA.inter (measurableSet_le measurable_const hg.norm)
  have hmark := mul_meas_ge_le_lintegral (μ := ν) hg.enorm (ENNReal.ofReal c)
  have hsub : B ⊆ {y | ENNReal.ofReal c ≤ ‖g y‖ₑ} := by
    intro y hy
    change ENNReal.ofReal c ≤ ‖g y‖ₑ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hy.2
  have hlin : (∫⁻ y, ‖g y‖ₑ ∂ν) = ENNReal.ofReal ‖T f‖ := by
    rw [lintegral_congr_ae (hfg.symm.mono fun _ he => congrArg (fun z => ‖z‖ₑ) he),
      ← ofReal_integral_norm_eq_lintegral_enorm (L1.integrable_coeFn (T f)),
      ← L1.norm_eq_integral_norm]
  have hνB : ν B < ENNReal.ofReal δ := by
    by_contra! h
    have hh := (mul_le_mul' le_rfl (h.trans (measure_mono hsub))).trans hmark
    rw [hlin, ← ENNReal.ofReal_mul hc.le] at hh
    have hn : ‖T f‖ ≤ ‖T‖ :=
      (T.le_opNorm f).trans (mul_le_of_le_one_right (norm_nonneg _) hf)
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hδ)).2
      (hn.trans_lt hsize))) hh
  have hcut := cutOperatorNorm_le_smallSetSup T A hA hB inter_subset_left hνB
  rw [cutOperatorNorm_eq T _ (hA.compl.union hB)] at hcut
  have hnorm : ‖lpCut (Aᶜ ∪ B) (hA.compl.union hB) (T f)‖ ≤ smallSetSup T A δ :=
    (((lpCutL (Aᶜ ∪ B) (hA.compl.union hB)).comp T).le_opNorm f).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hf).trans hcut)
  apply le_trans _ hnorm
  rw [section5TruncationTail, L1.norm_eq_integral_norm]
  apply integral_mono_ae (section5_tail_integrable hA hc.le _) (L1.integrable_coeFn _).norm
  filter_upwards [hfg, lpCut_coe (Aᶜ ∪ B) (hA.compl.union hB) (T f)] with y hy hcuty
  rw [hcuty]
  by_cases hyA : y ∈ A
  · by_cases hyc : c ≤ ‖g y‖
    · have hyAB : y ∈ Aᶜ ∪ B := Or.inr ⟨hyA, hyc⟩
      simp only [hyA, hyAB, indicator_of_mem]
      exact max_le (sub_le_self _ hc.le) (norm_nonneg _)
    · have hynAB : y ∉ Aᶜ ∪ B := by simp [B, hyA, hyc]
      have hle : ‖T f y‖ ≤ c := by rw [hy]; exact (lt_of_not_ge hyc).le
      simp [hyA, hynAB, max_eq_right (sub_nonpos.mpr hle)]
  · have hyAB : y ∈ Aᶜ ∪ B := Or.inl hyA
    simp [hyA, hyAB]

private theorem section5_alpha_le_profile (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    {A : Set Y} (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c) :
    alphaTheta T A ≤ section5TruncationProfile T A c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / c
  have hδ : 0 < δ := div_pos hε hc
  refine (alphaTheta_le_smallSetSup T A hA hδ).trans ?_
  apply csSup_le
  · exact ⟨_, ∅, MeasurableSet.empty, empty_subset _, by
      simpa using ENNReal.ofReal_pos.mpr hδ, rfl⟩
  · rintro _ ⟨B, hB, hBA, hνB, rfl⟩
    have hBfinite : ν B ≠ ⊤ := (hνB.trans_le le_top).ne
    have hBsmall : (ν B).toReal ≤ δ := by
      simpa only [ENNReal.toReal_ofReal hδ.le] using
        (ENNReal.toReal_le_toReal hBfinite ENNReal.ofReal_ne_top).mpr hνB.le
    have hBmass : c * (ν B).toReal ≤ ε := by
      exact (mul_le_mul_of_nonneg_left hBsmall hc.le).trans_eq
        (by dsimp [δ]; field_simp)
    rw [cutOperatorNorm_eq T _ (hA.compl.union hB)]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
      (add_nonneg (section5_profile_nonneg T hA hc.le) hε.le)
    intro f hf
    change ‖lpCut (Aᶜ ∪ B) (hA.compl.union hB) (T f)‖ ≤ _
    rw [section5_norm_cut_eq_integral]
    let q : Y → ℝ := fun y => max (‖T f y‖ - A.indicator (fun _ => c) y) 0
    have hq : Integrable q ν := section5_tail_integrable hA hc.le _
    have hi : Integrable (B.indicator (fun _ => c)) ν := by
      rw [integrable_indicator_iff hB]
      exact integrableOn_const hBfinite
    have hj : Integrable ((Aᶜ ∪ B).indicator (fun y => ‖T f y‖)) ν :=
      (L1.integrable_coeFn (T f)).norm.indicator (hA.compl.union hB)
    have hintegral := integral_mono hj (hq.add hi) (fun y => by
      change (Aᶜ ∪ B).indicator (fun y => ‖T f y‖) y ≤ q y + B.indicator (fun _ => c) y
      by_cases hyA : y ∈ A
      · by_cases hyB : y ∈ B
        · have hyAB : y ∈ Aᶜ ∪ B := Or.inr hyB
          simp only [hyAB, hyB, hyA, indicator_of_mem, q]
          linarith [le_max_left (‖T f y‖ - c) 0]
        · simp [hyA, hyB, q]
      · have hyB : y ∉ B := fun h => hyA (hBA h)
        have hyAB : y ∈ Aᶜ ∪ B := Or.inl hyA
        simp [hyA, hyB, hyAB, q])
    calc
      _ ≤ ∫ y, q y + B.indicator (fun _ => c) y ∂ν := hintegral
      _ = section5TruncationTail A c (T f) + c * (ν B).toReal := by
        rw [integral_add hq hi, integral_indicator hB, setIntegral_const]
        simp [q, section5TruncationTail, measureReal_def, mul_comm]
      _ ≤ _ := add_le_add (section5_tail_le_profile T hA hc.le hf.le) hBmass

theorem section5LocalizedTruncationInf_eq_localized (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    section5LocalizedTruncationInf T = localizedWeakNoncompactness T := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, ∅, MeasurableSet.empty, by simp, rfl⟩
    rintro _ ⟨A, hA, hfin, rfl⟩
    apply le_csInf
    · exact ⟨_, 1, zero_lt_one, rfl⟩
    rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨c, hc⟩ := exists_gt (max 0 (‖T‖ / δ))
    have hc0 : 0 < c := (le_max_left _ _).trans_lt hc
    have hsize : ‖T‖ < c * δ := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hc)
    apply le_trans _ (section5_profile_le_smallSetSup T hA hc0 hδ hsize)
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨B, hB, _, d, hd, rfl⟩
      exact section5_profile_nonneg T hB hd.le
    · exact ⟨A, hA, hfin, c, hc0, rfl⟩
  · apply le_csInf
    · exact ⟨_, ∅, MeasurableSet.empty, by simp, 1, zero_lt_one, rfl⟩
    rintro _ ⟨A, hA, hfin, c, hc, rfl⟩
    exact (localizedWeakNoncompactness_le_alphaTheta T hA hfin).trans (section5_alpha_le_profile T hA hc)

theorem section5UnivTruncationInf_eq_alphaTheta (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    section5UnivTruncationInf T = alphaTheta T univ := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, 1, zero_lt_one, rfl⟩
    rintro _ ⟨δ, hδ, rfl⟩
    obtain ⟨c, hc⟩ := exists_gt (max 0 (‖T‖ / δ))
    have hc0 : 0 < c := (le_max_left _ _).trans_lt hc
    have hsize : ‖T‖ < c * δ := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hc)
    apply le_trans _ (section5_profile_le_smallSetSup T MeasurableSet.univ hc0 hδ hsize)
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      exact section5_profile_nonneg T MeasurableSet.univ hd.le
    · exact ⟨c, hc0, rfl⟩
  · apply le_csInf
    · exact ⟨_, 1, zero_lt_one, rfl⟩
    rintro _ ⟨c, hc, rfl⟩
    exact section5_alpha_le_profile T MeasurableSet.univ hc

theorem section5TruncationTail_univ (c : ℝ) (f : LOne 𝕜 ν) :
    section5TruncationTail univ c f = ∫ y, max (‖f y‖ - c) 0 ∂ν := by
  simp [section5TruncationTail]

end PEMS
