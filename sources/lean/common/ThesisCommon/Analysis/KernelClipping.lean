import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Continuous clipping and its residual mass. Unlike hard level-set cutoffs,
the residual mass varies continuously even when level sets have positive measure. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThesisCommon

/-- Symmetric real clipping at the nonnegative part of the level. -/
def scalarClip (t a : ℝ) : ℝ := max (-max t 0) (min a (max t 0))

/-- The absolute amount removed by clipping. -/
def clipResidual (t a : ℝ) : ℝ := max (‖a‖ - max t 0) 0

theorem norm_scalarClip (t a : ℝ) : ‖scalarClip t a‖ = min ‖a‖ (max t 0) := by
  have ht : 0 ≤ max t 0 := le_max_right _ _
  simp only [scalarClip, Real.norm_eq_abs, abs_eq_max_neg, min_def, max_def]
  split_ifs <;> linarith

theorem norm_sub_scalarClip (t a : ℝ) : ‖a - scalarClip t a‖ = clipResidual t a := by
  have ht : 0 ≤ max t 0 := le_max_right _ _
  simp only [scalarClip, clipResidual, Real.norm_eq_abs, abs_eq_max_neg, min_def, max_def]
  split_ifs <;> linarith

theorem norm_scalarClip_le (t a : ℝ) : ‖scalarClip t a‖ ≤ ‖a‖ := by
  rw [norm_scalarClip]
  exact min_le_left _ _

theorem norm_scalarClip_le_level (t a : ℝ) : ‖scalarClip t a‖ ≤ max t 0 := by
  rw [norm_scalarClip]
  exact min_le_right _ _

theorem clipResidual_nonneg (t a : ℝ) : 0 ≤ clipResidual t a := le_max_right _ _

theorem clipResidual_le_norm (t a : ℝ) : clipResidual t a ≤ ‖a‖ := by
  exact max_le (sub_le_self _ (le_max_right _ _)) (norm_nonneg _)

@[simp] theorem clipResidual_zero (a : ℝ) : clipResidual 0 a = ‖a‖ := by
  simp [clipResidual]

theorem clipResidual_antitone (a : ℝ) : Antitone (fun t => clipResidual t a) := by
  intro s t hst
  exact max_le_max (sub_le_sub_left (max_le_max_right 0 hst) _) le_rfl

theorem continuous_scalarClip : Continuous (fun p : ℝ × ℝ => scalarClip p.1 p.2) :=
  ((continuous_fst.max continuous_const).neg).max
    (continuous_snd.min (continuous_fst.max continuous_const))

theorem continuous_clipResidual : Continuous (fun p : ℝ × ℝ => clipResidual p.1 p.2) :=
  (continuous_snd.norm.sub (continuous_fst.max continuous_const)).max continuous_const

theorem clipResidual_scalarClip {n t : ℝ} (hn : 0 ≤ n) (hnt : n ≤ t) (a : ℝ) :
    clipResidual n (scalarClip t a) = clipResidual n a - clipResidual t a := by
  have ht : 0 ≤ t := hn.trans hnt
  simp only [clipResidual, norm_scalarClip, max_eq_left hn, max_eq_left ht]
  simp only [min_def, max_def]
  split_ifs <;> linarith

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {f : Y → ℝ}

theorem integrable_clipResidual (hf : Integrable f ν) (t : ℝ) :
    Integrable (fun y => clipResidual t (f y)) ν := by
  apply hf.norm.mono'
    (continuous_clipResidual.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hf.aestronglyMeasurable))
  exact Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (clipResidual_nonneg _ _)]
    exact clipResidual_le_norm _ _

theorem integrable_scalarClip (hf : Integrable f ν) (t : ℝ) :
    Integrable (fun y => scalarClip t (f y)) ν := by
  exact hf.norm.mono'
    (continuous_scalarClip.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hf.aestronglyMeasurable))
    (Eventually.of_forall fun y => norm_scalarClip_le t (f y))

/-- The column mass remaining after symmetric clipping. -/
def clipResidualMass (ν : Measure Y) (f : Y → ℝ) (t : ℝ) : ℝ :=
  ∫ y, clipResidual t (f y) ∂ν

theorem clipResidualMass_nonneg (t : ℝ) : 0 ≤ clipResidualMass ν f t :=
  integral_nonneg fun y => clipResidual_nonneg t (f y)

theorem clipResidualMass_antitone (hf : Integrable f ν) : Antitone (clipResidualMass ν f) := by
  intro s t hst
  exact integral_mono (integrable_clipResidual hf t) (integrable_clipResidual hf s)
    (fun y => clipResidual_antitone (f y) hst)

@[simp] theorem clipResidualMass_zero : clipResidualMass ν f 0 = ∫ y, ‖f y‖ ∂ν := by
  simp only [clipResidualMass, clipResidual_zero]

theorem continuous_clipResidualMass (hf : Integrable f ν) :
    Continuous (clipResidualMass ν f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
  · exact Eventually.of_forall fun s => (integrable_clipResidual hf s).aestronglyMeasurable
  · exact Eventually.of_forall fun s => Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (clipResidual_nonneg _ _)]
      exact clipResidual_le_norm _ _
  · exact hf.norm
  · exact Eventually.of_forall fun y =>
      (continuous_clipResidual.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem tendsto_clipResidualMass_atTop (hf : Integrable f ν) :
    Tendsto (clipResidualMass ν f) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (F := fun t y => clipResidual t (f y)) (f := fun _ => (0 : ℝ))
    (l := atTop) (fun y => ‖f y‖)
    (Eventually.of_forall fun t => (integrable_clipResidual hf t).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (clipResidual_nonneg _ _)]
      exact clipResidual_le_norm _ _)
    hf.norm ?_
  · simpa only [clipResidualMass, integral_zero] using h
  · exact Eventually.of_forall fun y => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ‖f y‖] with t ht
      simp only [clipResidual]
      rw [max_eq_left ((norm_nonneg _).trans ht), max_eq_right (sub_nonpos.mpr ht)]

/-- The exact residual identity used for controlling bounded approximants. -/
theorem clipResidualMass_scalarClip (hf : Integrable f ν) {n t : ℝ}
    (hn : 0 ≤ n) (hnt : n ≤ t) :
    clipResidualMass ν (fun y => scalarClip t (f y)) n =
      clipResidualMass ν f n - clipResidualMass ν f t := by
  simp only [clipResidualMass, clipResidual_scalarClip hn hnt]
  exact integral_sub (integrable_clipResidual hf n) (integrable_clipResidual hf t)

/-- The same identity without an ordering restriction on the two levels. -/
theorem clipResidualMass_scalarClip_eq (hf : Integrable f ν) {n t : ℝ}
    (hn : 0 ≤ n) (ht : 0 ≤ t) :
    clipResidualMass ν (fun y => scalarClip t (f y)) n =
      max (clipResidualMass ν f n - clipResidualMass ν f t) 0 := by
  rcases le_total n t with hnt | htn
  · rw [clipResidualMass_scalarClip hf hn hnt, max_eq_left]
    exact sub_nonneg.mpr (clipResidualMass_antitone hf hnt)
  · have heq : clipResidualMass ν (fun y => scalarClip t (f y)) n = 0 := by
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun y => by
        have hbound : ‖scalarClip t (f y)‖ ≤ n := by
          exact (norm_scalarClip_le_level t (f y)).trans (by simpa only [max_eq_left ht])
        simp only [clipResidual, max_eq_left hn, max_eq_right (sub_nonpos.mpr hbound), Pi.zero_apply]
    rw [heq, max_eq_right (sub_nonpos.mpr (clipResidualMass_antitone hf htn))]

variable {X : Type*} [MeasurableSpace X]

theorem measurable_scalarClip {k : X → ℝ} {t : X → ℝ}
    (hk : Measurable k) (ht : Measurable t) : Measurable (fun x => scalarClip (t x) (k x)) :=
  continuous_scalarClip.measurable.comp (ht.prodMk hk)

theorem measurable_clipResidualMass [SFinite ν] {k : X × Y → ℝ} {t : X → ℝ}
    (hk : Measurable k) (ht : Measurable t) :
    Measurable (fun x => clipResidualMass ν (fun y => k (x, y)) (t x)) := by
  exact (continuous_clipResidual.measurable.comp
    ((ht.comp measurable_fst).prodMk hk)).stronglyMeasurable.integral_prod_right'.measurable

end ThesisCommon
