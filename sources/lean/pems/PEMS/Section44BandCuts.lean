import PEMS.LocalizedTruncationLowerBound
import ThesisCommon.Analysis.L1SupportedDomination

/-! Band restrictions and zero extensions for the piecewise decomposition of §4.4. -/
noncomputable section
open MeasureTheory Set Filter ThesisCommon
open scoped ENNReal ThesisCommon.PositiveOperatorOrder

namespace PEMS
set_option maxHeartbeats 1200000

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem section44_extend_abs (A : Set Y) (hA : MeasurableSet A)
    (f : LOne ℝ (ν.restrict A)) :
    lebesgueLpExtend (𝕜 := ℝ) A hA |f| = |lebesgueLpExtend (𝕜 := ℝ) A hA f| := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) A hA |f|,
    lebesgueLpExtend_coe (𝕜 := ℝ) A hA f,
    Lp.coeFn_abs (lebesgueLpExtend (𝕜 := ℝ) A hA f),
    (ae_restrict_iff' hA).mp (Lp.coeFn_abs f)] with y h₁ h₂ h₃ h₄
  rw [h₁, h₃, h₂]
  by_cases hy : y ∈ A <;> simp [hy, h₄]

theorem section44_abs_comp_extend (A : Set X) (hA : MeasurableSet A)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    |T.comp (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap| =
      |T|.comp (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap := by
  let J := (lebesgueLpExtend (𝕜 := ℝ) (μ := μ) (p := 1) (E := ℝ) A hA).toContinuousLinearMap
  change |T.comp J| = |T|.comp J
  apply le_antisymm
  · intro f hf
    rw [abs_lOneOperator_eq (T.comp J)]
    apply lOneOperatorModulus_least (T.comp J) (|T|.comp J) _ f hf
    intro g hg
    have hpos : 0 ≤ J g := lebesgueL1Extend_nonneg A hA g hg
    simpa only [ContinuousLinearMap.comp_apply, abs_lOneOperator_eq,
      abs_of_nonneg hpos] using
      lOneOperatorModulus_dominates T (J g)
  · intro f hf
    change |T| (J f) ≤ |T.comp J| f
    rw [abs_lOneOperator_eq T]
    apply (lOneOperatorModulus_rieszKantorovich T (J f)
      (lebesgueL1Extend_nonneg A hA f hf)).2
    rintro _ ⟨g, hg, rfl⟩
    let p := lebesgueLpRestrict (𝕜 := ℝ) A g
    have hJp : J p = g := by
      change lebesgueLpExtend (𝕜 := ℝ) A hA (lebesgueLpRestrict (𝕜 := ℝ) A g) = g
      rw [lebesgueL1Extend_restrict_eq_cut]
      have hzero : lpCut Aᶜ hA.compl g = 0 := by
        have hb : |g| ≤ J f := abs_le'.mpr ⟨hg.2, by simpa using neg_le_neg hg.1⟩
        have hle := lOneCut_mono Aᶜ hA.compl hb
        have hz : lpCut Aᶜ hA.compl (J f) = 0 := by
          apply Lp.ext
          filter_upwards [lpCut_coe Aᶜ hA.compl (J f),
            lebesgueLpExtend_coe (𝕜 := ℝ) A hA f, Lp.coeFn_zero ℝ 1 μ]
            with x hx he hz
          change J f x = A.indicator f x at he
          rw [hx, hz]
          by_cases h : x ∈ A <;> simp [h, he]
        rw [hz, lOneCut_abs] at hle
        have hz' : |lpCut Aᶜ hA.compl g| = 0 := le_antisymm hle (abs_nonneg _)
        apply norm_eq_zero.mp
        rw [← norm_abs_eq_norm, hz', norm_zero]
      simpa only [hzero, add_zero] using lOneCut_add_compl A hA g
    have hp : p ∈ Icc (-f) f := by
      have hlo := lebesgueL1Restrict_mono A hg.1
      have hhi := lebesgueL1Restrict_mono A hg.2
      change lebesgueLpRestrict (𝕜 := ℝ) A (-(lebesgueLpExtend (𝕜 := ℝ) A hA f)) ≤ p at hlo
      change p ≤ lebesgueLpRestrict (𝕜 := ℝ) A (lebesgueLpExtend (𝕜 := ℝ) A hA f) at hhi
      rw [map_neg, lebesgueLpRestrict_extend] at hlo
      rw [lebesgueLpRestrict_extend] at hhi
      exact ⟨hlo, hhi⟩
    have h := (lOneOperatorModulus_rieszKantorovich (T.comp J) f hf).1 ⟨p, hp, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, hJp, ← abs_lOneOperator_eq] using h

theorem section44_abs_extend_comp (A : Set Y) (hA : MeasurableSet A)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict A)) :
    |(lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp T| =
      (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp |T| := by
  let J := (lebesgueLpExtend (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A hA).toContinuousLinearMap
  let U := J.comp T
  change |U| = J.comp |T|
  have hu : |U| ≤ J.comp |T| := by
    intro f hf
    rw [abs_lOneOperator_eq U]
    apply lOneOperatorModulus_least U (J.comp |T|) _ f hf
    intro g hg
    change |lebesgueLpExtend (𝕜 := ℝ) A hA (T g)| ≤
      lebesgueLpExtend (𝕜 := ℝ) A hA (|T| g)
    rw [← section44_extend_abs]
    apply lebesgueL1Extend_mono
    simpa only [abs_of_nonneg hg, ← abs_lOneOperator_eq] using
      lOneOperatorModulus_dominates T g
  apply le_antisymm hu
  intro f hf
  have hle : |T| f ≤ lebesgueLpRestrict (𝕜 := ℝ) A (|U| f) := by
    rw [abs_lOneOperator_eq T]
    apply lOneOperatorModulus_least T
      ((lebesgueLpRestrict (𝕜 := ℝ) A).comp |U|) _ f hf
    intro g hg
    have h := lebesgueL1Restrict_mono A (lOneOperatorModulus_dominates U g)
    rw [abs_of_nonneg hg, lebesgueL1Restrict_abs] at h
    change |lebesgueLpRestrict (𝕜 := ℝ) A (lebesgueLpExtend (𝕜 := ℝ) A hA (T g))| ≤ _ at h
    rwa [lebesgueLpRestrict_extend, ← abs_lOneOperator_eq] at h
  exact (lebesgueL1Extend_mono A hA hle).trans
    (by rw [lebesgueL1Extend_restrict_eq_cut]; exact lOneCut_le_self A hA ((abs_nonneg U) f hf))

theorem section44_kernel_restrict {k : X × Y → ℝ} {K : LOne ℝ μ →L[ℝ] LOne ℝ ν}
    (hk : IsIntegralKernel k K) (A : Set Y) :
    IsIntegralKernel k ((lebesgueLpRestrict (𝕜 := ℝ) A).comp K) where
  measurable := hk.measurable
  integrable_section f := ae_restrict_of_ae (hk.integrable_section f)
  represents f := (lebesgueLpRestrict_coe (𝕜 := ℝ) A (K f)).trans (ae_restrict_of_ae (hk.represents f))

theorem section44_kernel_extend (A : Set Y) (hA : MeasurableSet A)
    {k : X × Y → ℝ} {K : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict A)}
    (hk : IsIntegralKernel k K) :
    IsIntegralKernel ((univ ×ˢ A).indicator k)
      ((lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp K) where
  measurable := hk.measurable.indicator (MeasurableSet.univ.prod hA)
  integrable_section f := by
    filter_upwards [(ae_restrict_iff' hA).mp (hk.integrable_section f)] with y hy
    by_cases hm : y ∈ A <;> simp [hm, hy]
  represents f := by
    filter_upwards [lebesgueLpExtend_coe (𝕜 := ℝ) A hA (K f),
      (ae_restrict_iff' hA).mp (hk.represents f)] with y hy hr
    change lebesgueLpExtend (𝕜 := ℝ) A hA (K f) y = _
    rw [hy]
    by_cases hm : y ∈ A <;> simp [hm, hr]

theorem section44_abs_restrict_comp (A : Set Y) (hA : MeasurableSet A)
    (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    |(lebesgueLpRestrict (𝕜 := ℝ) A).comp T| =
      (lebesgueLpRestrict (𝕜 := ℝ) A).comp |T| := by
  let J := lebesgueLpExtend (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A hA
  let P := lebesgueLpRestrict (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A
  have hcut (U : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
      J.toContinuousLinearMap.comp (P.comp U) = (lpCutL A hA).comp U := by
    ext f : 1
    exact lebesgueL1Extend_restrict_eq_cut A hA (U f)
  have h : J.toContinuousLinearMap.comp |P.comp T| =
      J.toContinuousLinearMap.comp (P.comp |T|) := by
    rw [← section44_abs_extend_comp A hA, hcut, abs_outputCut_lOneOperator, hcut]
  ext f : 1
  exact J.injective (DFunLike.congr_fun h f)

theorem section44_restrict_singular {S : LOne ℝ μ →L[ℝ] LOne ℝ ν}
    (hsing : IsSingularOperator S) (hS : 0 ≤ S) (A : Set Y) (hA : MeasurableSet A)
    [SigmaFinite μ] [SigmaFinite (ν.restrict A)] :
    IsSingularOperator ((lebesgueLpRestrict (𝕜 := ℝ) A).comp S) := by
  intro K hK
  let R := (lebesgueLpRestrict (𝕜 := ℝ) A).comp S
  have hR : 0 ≤ R := fun f hf => lebesgueL1Restrict_nonneg A (S f) (hS f hf)
  change |R| ⊓ |K| = 0
  rw [abs_of_nonneg hR]
  let D := R ⊓ |K|
  have hD : 0 ≤ D := le_inf hR (abs_nonneg K)
  let J := (lebesgueLpExtend (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A hA).toContinuousLinearMap
  have hJpos : 0 ≤ J.comp D := lebesgueL1Extend_comp_nonneg A hA hD
  have hDS : J.comp D ≤ S := by
    intro f hf
    have h := lebesgueL1Extend_mono A hA ((inf_le_left : D ≤ R) f hf)
    change J (D f) ≤ lebesgueLpExtend (𝕜 := ℝ) A hA (lebesgueLpRestrict (𝕜 := ℝ) A (S f)) at h
    rw [lebesgueL1Extend_restrict_eq_cut] at h
    exact h.trans (lOneCut_le_self A hA (hS f hf))
  obtain ⟨k, hk⟩ := hK
  have hJint : IsIntegralOperator (J.comp |K|) :=
    ⟨_, section44_kernel_extend A hA hk.abs⟩
  have hJzero : J.comp D = 0 := by
    apply le_antisymm _ hJpos
    have hb := hsing _ hJint
    rw [abs_of_nonneg hS, abs_of_nonneg (lebesgueL1Extend_comp_nonneg A hA (abs_nonneg K))] at hb
    rw [← hb]
    exact le_inf hDS (fun f hf => lebesgueL1Extend_mono A hA ((inf_le_right : D ≤ |K|) f hf))
  apply ContinuousLinearMap.ext
  intro f
  have hf := DFunLike.congr_fun hJzero f
  change lebesgueLpExtend (𝕜 := ℝ) A hA (D f) = 0 at hf
  have h := congrArg (lebesgueLpRestrict (𝕜 := ℝ) A) hf
  change D f = 0
  simpa only [lebesgueLpRestrict_extend, map_zero] using h

theorem section44_extend_singular (A : Set Y) (hA : MeasurableSet A)
    {S : LOne ℝ μ →L[ℝ] LOne ℝ (ν.restrict A)}
    (hsing : IsSingularOperator S) (hS : 0 ≤ S) :
    IsSingularOperator ((lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp S) := by
  intro K hK
  let J := lebesgueLpExtend (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A hA
  let P := lebesgueLpRestrict (𝕜 := ℝ) (μ := ν) (p := 1) (E := ℝ) A
  have hJS : 0 ≤ J.toContinuousLinearMap.comp S := lebesgueL1Extend_comp_nonneg A hA hS
  rw [abs_of_nonneg hJS]
  let D := J.toContinuousLinearMap.comp S ⊓ |K|
  have hD : 0 ≤ D := le_inf hJS (abs_nonneg K)
  have hD₁ : D ≤ J.toContinuousLinearMap.comp S := inf_le_left
  have hD₂ : D ≤ |K| := inf_le_right
  obtain ⟨k, hk⟩ := hK
  have hPzero : P.comp D = 0 := by
    apply le_antisymm _ (fun f hf => lebesgueL1Restrict_nonneg A (D f) (hD f hf))
    have hs := hsing (P.comp K) ⟨k, section44_kernel_restrict hk A⟩
    rw [abs_of_nonneg hS, section44_abs_restrict_comp A hA] at hs
    rw [← hs]
    apply le_inf
    · intro f hf
      have hb := lebesgueL1Restrict_mono A (hD₁ f hf)
      change P (D f) ≤ lebesgueLpRestrict (𝕜 := ℝ) A
        (lebesgueLpExtend (𝕜 := ℝ) A hA (S f)) at hb
      rwa [lebesgueLpRestrict_extend] at hb
    · exact fun f hf => lebesgueL1Restrict_mono A (hD₂ f hf)
  change D = 0
  apply le_antisymm _ hD
  intro f hf
  have hcut : lpCut A hA (D f) = 0 := by
    rw [← lebesgueL1Extend_restrict_eq_cut]
    change J ((P.comp D) f) = 0
    rw [hPzero, ContinuousLinearMap.zero_apply, map_zero]
  have hcutJ : lpCut A hA (J (S f)) = J (S f) := by
    rw [← lebesgueL1Extend_restrict_eq_cut]
    exact congrArg J (lebesgueLpRestrict_extend A hA (S f))
  have hc : lpCut Aᶜ hA.compl (D f) ≤ 0 := by
    have hb := lOneCut_mono Aᶜ hA.compl (hD₁ f hf)
    change lpCut Aᶜ hA.compl (D f) ≤ lpCut Aᶜ hA.compl (J (S f)) at hb
    have hz : lpCut Aᶜ hA.compl (lpCut A hA (J (S f))) = 0 := by
      simpa only [compl_compl] using lOneCut_compl_eq_zero Aᶜ hA.compl (J (S f))
    rw [← hcutJ, hz] at hb
    exact hb
  change D f ≤ 0
  rw [← lOneCut_add_compl A hA (D f), hcut, zero_add]
  exact hc

end PEMS
