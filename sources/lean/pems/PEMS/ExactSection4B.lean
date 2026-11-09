import PEMS.RealStrictlyLocalizableWeis
import PEMS.WeakCompactSigmaFiniteRange

/-! Standalone statements in the real-scalar part of Section 4. -/

noncomputable section

open MeasureTheory Set ThesisCommon
open scoped ENNReal

namespace PEMS

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- Theorem 4.18: a weakly compact best approximant with support in the finite
localization, and equality of its error with the small-set functional. -/
theorem theorem_4_18_exact (hμ : StrictlyLocalizable μ) (_hν : StrictlyLocalizable ν)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (Θ : Set Y) (hΘ : MeasurableSet Θ)
    (hfin : ν Θ < ⊤) :
    ∃ H : LOne ℝ μ →L[ℝ] LOne ℝ ν, IsWeaklyCompactOperator H ∧
      L1OperatorSupportedOn Θ H ∧ ‖T - H‖ = supportedWeakEssentialNorm Θ T ∧
      supportedWeakEssentialNorm Θ T = alphaTheta T Θ := by
  letI : IsFiniteMeasure (ν.restrict Θ) := isFiniteMeasure_restrict.mpr hfin.ne
  obtain ⟨H, hH, hs, he⟩ := exists_real_finite_supported_bestApproximation hμ Θ hΘ T
  exact ⟨H, hH, hs, he, supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable
    hμ Θ hΘ T⟩

/-- Corollary 4.19: the small-set functional decreases as the localization grows. -/
theorem corollary_4_19_exact (hμ : StrictlyLocalizable μ) (_hν : StrictlyLocalizable ν)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) (P Θ : Set Y) (hP : MeasurableSet P)
    (hΘ : MeasurableSet Θ) (hPfin : ν P < ⊤) (hΘfin : ν Θ < ⊤) (hsub : P ⊆ Θ) :
    alphaTheta T Θ ≤ alphaTheta T P := by
  letI : IsFiniteMeasure (ν.restrict P) := isFiniteMeasure_restrict.mpr hPfin.ne
  letI : IsFiniteMeasure (ν.restrict Θ) := isFiniteMeasure_restrict.mpr hΘfin.ne
  rw [← supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable hμ Θ hΘ T,
    ← supportedWeakEssentialNorm_eq_alphaTheta_real_strictlyLocalizable hμ P hP T]
  exact supportedWeakEssentialNorm_antitone T hsub

/-- Lemma 4.24: the complement of the existing localization can be exhausted
in norm while the enlarged finite set contains both prescribed sets. -/
theorem lemma_4_24_exact (_hν : StrictlyLocalizable ν) (g : LOne ℝ ν)
    (P Θ : Set Y) (hP : MeasurableSet P) (hΘ : MeasurableSet Θ)
    (hPfin : ν P < ⊤) (hΘfin : ν Θ < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ Λ : Set Y, ∃ hΛ : MeasurableSet Λ, ν Λ < ⊤ ∧ P ∪ Θ ⊆ Λ ∧
      ‖lpCut (Λ \ Θ) (hΛ.diff hΘ) g - lpCut Θᶜ hΘ.compl g‖ < ε := by
  obtain ⟨A, hA, hAfin, hAc⟩ := lOneCut_exists_finite_measure g hε
  let Λ := (P ∪ Θ) ∪ A
  have hΛ : MeasurableSet Λ := (hP.union hΘ).union hA
  have hΛfin : ν Λ < ⊤ := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨(measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hPfin, hΘfin⟩), hAfin⟩)
  have hsubΘ : Θ ⊆ Λ := subset_union_right.trans subset_union_left
  have hsubA : A ⊆ Λ := subset_union_right
  refine ⟨Λ, hΛ, hΛfin, subset_union_left, ?_⟩
  have heq : lpCut (Λ \ Θ) (hΛ.diff hΘ) g - lpCut Θᶜ hΘ.compl g =
      -(lpCut Λᶜ hΛ.compl g) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (lpCut (Λ \ Θ) (hΛ.diff hΘ) g) (lpCut Θᶜ hΘ.compl g),
      Lp.coeFn_neg (lpCut Λᶜ hΛ.compl g), lpCut_coe (Λ \ Θ) (hΛ.diff hΘ) g,
      lpCut_coe Θᶜ hΘ.compl g, lpCut_coe Λᶜ hΛ.compl g] with y hsub hneg h1 h2 h3
    rw [hsub, hneg]
    simp only [Pi.sub_apply, Pi.neg_apply, h1, h2, h3]
    by_cases hyΛ : y ∈ Λ
    · by_cases hyΘ : y ∈ Θ <;> simp [hyΛ, hyΘ]
    · have hyΘ : y ∉ Θ := fun h => hyΛ (hsubΘ h)
      simp [hyΛ, hyΘ]
  rw [heq, norm_neg]
  apply lt_of_le_of_lt _ hAc
  rw [norm_lOneCut_eq_integral, norm_lOneCut_eq_integral]
  apply setIntegral_mono_set (L1.integrable_coeFn g).norm.integrableOn
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  exact Filter.Eventually.of_forall (compl_subset_compl.mpr hsubA)

end PEMS
