import ThesisCommon.Analysis.RCLikeL1DisjointCut
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Tail masses of actual scalar L1 elements, with a strictly positive
integer threshold. Nested tails have exactly subtractive L1 masses. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}

def lOneTailSet (f : Lp 𝕜 1 μ) (m : ℕ) : Set X := {x | (m : ℝ) + 1 ≤ ‖f x‖}

theorem measurableSet_lOneTailSet (f : Lp 𝕜 1 μ) (m : ℕ) :
    MeasurableSet (lOneTailSet f m) :=
  measurableSet_le measurable_const (Lp.stronglyMeasurable f).norm.measurable

def lOneTailMass (f : Lp 𝕜 1 μ) (m : ℕ) : ℝ :=
  ‖lpCut (lOneTailSet f m) (measurableSet_lOneTailSet f m) f‖

theorem lOneTailMass_bounds (f : Lp 𝕜 1 μ) (m : ℕ) :
    0 ≤ lOneTailMass f m ∧ lOneTailMass f m ≤ ‖f‖ :=
  ⟨norm_nonneg _, norm_lpCut_le _ _ _⟩

theorem lOneTailSet_antitone (f : Lp 𝕜 1 μ) : Antitone (lOneTailSet f) := by
  intro i j hij x hx
  change (i : ℝ) + 1 ≤ ‖f x‖
  change (j : ℝ) + 1 ≤ ‖f x‖ at hx
  exact (add_le_add_right (Nat.cast_le.mpr hij) 1).trans hx

theorem lOneTailMass_antitone (f : Lp 𝕜 1 μ) : Antitone (lOneTailMass f) := by
  intro i j hij
  simp only [lOneTailMass, norm_lOneCut_eq_integral_rclike]
  exact setIntegral_mono_set (L1.integrable_coeFn f).norm.integrableOn
    (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall (lOneTailSet_antitone f hij))

theorem eLpNorm_indicator_eq_ofReal_norm_lpCut (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) : eLpNorm (A.indicator f) 1 μ = ENNReal.ofReal ‖lpCut A hA f‖ := by
  change eLpNorm (A.indicator f) 1 μ =
    ENNReal.ofReal ‖((Lp.memLp f).indicator hA).toLp (A.indicator f)‖
  rw [Lp.norm_toLp]
  exact (ENNReal.ofReal_toReal ((Lp.memLp f).indicator hA).2.ne).symm

theorem lOneTailMass_cut_compl (f : Lp 𝕜 1 μ) {m l : ℕ} (hml : m ≤ l) :
    lOneTailMass (lpCut (lOneTailSet f l)ᶜ (measurableSet_lOneTailSet f l).compl f) m =
      lOneTailMass f m - lOneTailMass f l := by
  let g := lpCut (lOneTailSet f l)ᶜ (measurableSet_lOneTailSet f l).compl f
  have heq : lpCut (lOneTailSet g m) (measurableSet_lOneTailSet g m) g =
      lpCut (lOneTailSet f m \ lOneTailSet f l)
        ((measurableSet_lOneTailSet f m).diff (measurableSet_lOneTailSet f l)) f := by
    apply Lp.ext
    filter_upwards [lpCut_coe (lOneTailSet g m) (measurableSet_lOneTailSet g m) g,
      lpCut_coe (lOneTailSet f m \ lOneTailSet f l)
        ((measurableSet_lOneTailSet f m).diff (measurableSet_lOneTailSet f l)) f,
      lpCut_coe (lOneTailSet f l)ᶜ (measurableSet_lOneTailSet f l).compl f]
      with x h1 h2 h3
    change g x = _ at h3
    rw [h1, h2]
    by_cases hl : x ∈ lOneTailSet f l
    · have hg : g x = 0 := by simpa [hl] using h3
      have hn : x ∉ lOneTailSet g m := by
        simp only [lOneTailSet, mem_setOf_eq, hg, norm_zero, not_le]
        positivity
      simp [hn, hl]
    · have hg : g x = f x := by simpa [hl] using h3
      by_cases hm : x ∈ lOneTailSet f m
      · have hm' : x ∈ lOneTailSet g m := by simpa only [lOneTailSet, mem_setOf_eq, hg] using hm
        simp [hm, hm', hl, hg]
      · have hm' : x ∉ lOneTailSet g m := by simpa only [lOneTailSet, mem_setOf_eq, hg] using hm
        simp [hm, hm', hl]
  change ‖lpCut (lOneTailSet g m) (measurableSet_lOneTailSet g m) g‖ = _
  rw [heq]
  simp only [lOneTailMass, norm_lOneCut_eq_integral_rclike]
  exact integral_diff (measurableSet_lOneTailSet f l) (L1.integrable_coeFn f).norm.integrableOn
    (lOneTailSet_antitone f hml)

theorem measure_lOneTailSet_le [IsFiniteMeasure μ] (f : Lp 𝕜 1 μ) (m : ℕ) :
    μ (lOneTailSet f m) ≤ ENNReal.ofReal (‖f‖ / ((m : ℝ) + 1)) := by
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hint : μ.real (lOneTailSet f m) * ((m : ℝ) + 1) ≤ lOneTailMass f m := by
    rw [lOneTailMass, norm_lOneCut_eq_integral_rclike]
    calc
      _ = ∫ x in lOneTailSet f m, ((m : ℝ) + 1) ∂μ := by simp [Measure.real, integral_const]
      _ ≤ _ := integral_mono_ae (integrable_const _)
        (L1.integrable_coeFn f).norm.integrableOn
        ((ae_restrict_mem (measurableSet_lOneTailSet f m)).mono fun x hx => hx)
  have hreal : μ.real (lOneTailSet f m) ≤ ‖f‖ / ((m : ℝ) + 1) :=
    (le_div_iff₀ hpos).mpr (hint.trans (lOneTailMass_bounds f m).2)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (lOneTailSet f m))]
  exact ENNReal.ofReal_le_ofReal hreal

end ThesisCommon
