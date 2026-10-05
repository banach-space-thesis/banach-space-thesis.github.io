import ThesisCommon.Analysis.ComplexL1CutModulus
import ThesisCommon.Analysis.L1LocalizedAdjointCuts

/-! Complexification and pointwise complex modulus commute with actual
restriction and zero extension. All measures are arbitrary. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem complexL1OfReal_restrict (A : Set X) (f : Lp ℝ 1 μ) :
    lebesgueLpRestrict (𝕜 := ℂ) A (complexL1OfReal μ f) =
      complexL1OfReal (μ.restrict A) (lebesgueLpRestrict (𝕜 := ℝ) A f) := by
  apply Lp.ext
  filter_upwards [lebesgueLpRestrict_coe (𝕜 := ℂ) A (complexL1OfReal μ f),
    complexL1OfReal_coe (lebesgueLpRestrict (𝕜 := ℝ) A f),
    lebesgueLpRestrict_coe (𝕜 := ℝ) A f, ae_restrict_of_ae (complexL1OfReal_coe f)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem complexL1OfReal_extend (A : Set X) (hA : MeasurableSet A) (f : Lp ℝ 1 (μ.restrict A)) :
    lebesgueLpExtend (𝕜 := ℂ) A hA (complexL1OfReal (μ.restrict A) f) =
      complexL1OfReal μ (lebesgueLpExtend (𝕜 := ℝ) A hA f) := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := ℂ) A hA (complexL1OfReal (μ.restrict A) f),
    complexL1OfReal_coe (lebesgueLpExtend (𝕜 := ℝ) A hA f),
    lebesgueLpExtend_coe (𝕜 := ℝ) A hA f, (ae_restrict_iff' hA).mp (complexL1OfReal_coe f)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ A <;> simp [hx, h4]

theorem complexL1Modulus_restrict (A : Set X) (f : Lp ℂ 1 μ) :
    complexL1Modulus (lebesgueLpRestrict (𝕜 := ℂ) A f) =
      lebesgueLpRestrict (𝕜 := ℝ) A (complexL1Modulus f) := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (lebesgueLpRestrict (𝕜 := ℂ) A f),
    lebesgueLpRestrict_coe (𝕜 := ℝ) A (complexL1Modulus f),
    lebesgueLpRestrict_coe (𝕜 := ℂ) A f, ae_restrict_of_ae (complexL1Modulus_coe f)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem complexL1Modulus_extend (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 1 (μ.restrict A)) :
    complexL1Modulus (lebesgueLpExtend (𝕜 := ℂ) A hA f) =
      lebesgueLpExtend (𝕜 := ℝ) A hA (complexL1Modulus f) := by
  apply Lp.ext
  filter_upwards [complexL1Modulus_coe (lebesgueLpExtend (𝕜 := ℂ) A hA f),
    lebesgueLpExtend_coe (𝕜 := ℝ) A hA (complexL1Modulus f),
    lebesgueLpExtend_coe (𝕜 := ℂ) A hA f, (ae_restrict_iff' hA).mp (complexL1Modulus_coe f)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hx : x ∈ A <;> simp [hx, h4]

theorem lpCut_add_compl_rclike {𝕜 : Type*} [RCLike 𝕜]
    (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 1 μ) :
    lpCut A hA f + lpCut Aᶜ hA.compl f = f := by
  apply Lp.ext
  filter_upwards [lpCut_coe A hA f, lpCut_coe Aᶜ hA.compl f,
    Lp.coeFn_add (lpCut A hA f) (lpCut Aᶜ hA.compl f)] with x h1 h2 h3
  rw [h3, Pi.add_apply, h1, h2]
  by_cases hx : x ∈ A <;> simp [hx]

theorem lebesgueLpExtend_restrict_eq_cut_rclike {𝕜 : Type*} [RCLike 𝕜]
    (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 1 μ) :
    lebesgueLpExtend (𝕜 := 𝕜) A hA (lebesgueLpRestrict (𝕜 := 𝕜) A f) = lpCut A hA f := by
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) A hA (lebesgueLpRestrict (𝕜 := 𝕜) A f),
    (ae_restrict_iff' hA).mp (lebesgueLpRestrict_coe (𝕜 := 𝕜) A f), lpCut_coe A hA f]
    with x he hr hc
  rw [he, hc]
  by_cases hx : x ∈ A <;> simp [hx, hr]

theorem lpCut_compl_extend {𝕜 : Type*} [RCLike 𝕜]
    (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 1 (μ.restrict A)) :
    lpCut Aᶜ hA.compl (lebesgueLpExtend (𝕜 := 𝕜) A hA f) = 0 := by
  apply Lp.ext
  filter_upwards [lpCut_coe Aᶜ hA.compl (lebesgueLpExtend (𝕜 := 𝕜) A hA f),
    lebesgueLpExtend_coe (𝕜 := 𝕜) A hA f, Lp.coeFn_zero 𝕜 1 μ] with x hc he hz
  rw [hc, hz]
  by_cases hx : x ∈ A <;> simp [hx, he]

theorem complexL1OfReal_cut (A : Set X) (hA : MeasurableSet A) (f : Lp ℝ 1 μ) :
    complexL1OfReal μ (lpCut A hA f) = lpCut A hA (complexL1OfReal μ f) := by
  rw [← lebesgueLpExtend_restrict_eq_cut_rclike (𝕜 := ℝ), ← complexL1OfReal_extend,
    ← complexL1OfReal_restrict, lebesgueLpExtend_restrict_eq_cut_rclike]

end ThesisCommon
