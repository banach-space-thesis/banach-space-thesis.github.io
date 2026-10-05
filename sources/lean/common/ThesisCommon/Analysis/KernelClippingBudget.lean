import ThesisCommon.Analysis.KernelClippingSelection

/-! Columnwise clipping with a prescribed error budget. This construction is
jointly measurable and retains the full column at zero budget. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open scoped Classical

namespace ThesisCommon

variable {Y : Type*} [MeasurableSpace Y]

/-- A column clipped so the removed mass uses at most the given budget. -/
def budgetClip (ν : Measure Y) (f : Y → ℝ) (d : ℝ) (y : Y) : ℝ :=
  if 0 < d then scalarClip (continuousTailLevel (clipResidualMass ν f) d) (f y) else f y

@[simp] theorem budgetClip_zero (ν : Measure Y) (f : Y → ℝ) : budgetClip ν f 0 = f := by
  funext y
  simp [budgetClip]

theorem norm_budgetClip_le (ν : Measure Y) (f : Y → ℝ) (d : ℝ) (y : Y) :
    ‖budgetClip ν f d y‖ ≤ ‖f y‖ := by
  by_cases hd : 0 < d
  · simpa only [budgetClip, if_pos hd] using norm_scalarClip_le
      (continuousTailLevel (clipResidualMass ν f) d) (f y)
  · simp only [budgetClip, if_neg hd, le_refl]

variable {ν : Measure Y} {f : Y → ℝ}

theorem integrable_budgetClip (hf : Integrable f ν) (d : ℝ) :
    Integrable (budgetClip ν f d) ν := by
  unfold budgetClip
  by_cases hd : 0 < d
  · simpa only [budgetClip, if_pos hd] using
      integrable_scalarClip hf (continuousTailLevel (clipResidualMass ν f) d)
  · simpa only [budgetClip, if_neg hd] using hf

/-- The prescribed removed mass is attained up to the available total mass. -/
theorem integral_norm_sub_budgetClip (hf : Integrable f ν) {d : ℝ} (hd : 0 ≤ d) :
    (∫ y, ‖f y - budgetClip ν f d y‖ ∂ν) = min (∫ y, ‖f y‖ ∂ν) d := by
  rcases hd.eq_or_lt with rfl | hd
  · simp only [budgetClip_zero, sub_self, norm_zero, integral_zero]
    exact (min_eq_right (integral_nonneg fun y => norm_nonneg (f y))).symm
  · simp only [budgetClip, if_pos hd, norm_sub_scalarClip]
    exact (continuousTailLevel_value (continuous_clipResidualMass hf)
      (tendsto_clipResidualMass_atTop hf) hd).trans (by rw [clipResidualMass_zero])

/-- Exact control of every residual tail of the clipped column. -/
theorem clipResidualMass_budgetClip (hf : Integrable f ν) {d n : ℝ}
    (hd : 0 ≤ d) (hn : 0 ≤ n) :
    clipResidualMass ν (budgetClip ν f d) n = max (clipResidualMass ν f n - d) 0 := by
  rcases hd.eq_or_lt with rfl | hd
  · rw [budgetClip_zero, sub_zero, max_eq_left (clipResidualMass_nonneg n)]
  · unfold budgetClip
    simp only [if_pos hd]
    rw [clipResidualMass_scalarClip_eq hf hn
      (continuousTailLevel_mem (continuous_clipResidualMass hf)
        (tendsto_clipResidualMass_atTop hf) hd).1,
      continuousTailLevel_value (continuous_clipResidualMass hf)
        (tendsto_clipResidualMass_atTop hf) hd]
    have hR : clipResidualMass ν f n ≤ clipResidualMass ν f 0 :=
      clipResidualMass_antitone hf hn
    by_cases hmass : clipResidualMass ν f 0 ≤ d
    · rw [min_eq_left hmass, max_eq_right (sub_nonpos.mpr hR),
        max_eq_right (sub_nonpos.mpr (hR.trans hmass))]
    · rw [min_eq_right (le_of_not_ge hmass)]

variable {X : Type*} [MeasurableSpace X]

/-- The budget-selected kernel is jointly measurable for integrable columns.
No topology or countable-generation assumption on the parameter space is used. -/
theorem measurable_budgetClip [SFinite ν] {k : X × Y → ℝ} {d : X → ℝ}
    (hk : Measurable k) (hd : Measurable d)
    (hi : ∀ x, Integrable (fun y => k (x, y)) ν) :
    Measurable (fun z : X × Y => budgetClip ν (fun y => k (z.1, y)) (d z.1) z.2) := by
  let δ : X → ℝ := fun x => if 0 < d x then d x else 1
  have hδ : Measurable δ := hd.ite (measurableSet_lt measurable_const hd) measurable_const
  have hδpos (x : X) : 0 < δ x := by
    dsimp [δ]
    split_ifs with hx
    · exact hx
    · exact zero_lt_one
  have hlevel : Measurable (fun x =>
      continuousTailLevel (clipResidualMass ν (fun y => k (x, y))) (δ x)) :=
    measurable_continuousTailLevel
      (fun q => measurable_clipResidualMass hk measurable_const) hδ
      (fun x => continuous_clipResidualMass (hi x))
      (fun x => clipResidualMass_antitone (hi x))
      (fun x => tendsto_clipResidualMass_atTop (hi x)) hδpos
  have hm : Measurable (fun z : X × Y => if 0 < d z.1 then
      scalarClip (continuousTailLevel (clipResidualMass ν (fun y => k (z.1, y))) (δ z.1))
        (k z) else k z) :=
    (measurable_scalarClip hk (hlevel.comp measurable_fst)).ite
      (measurableSet_lt (measurable_const (a := (0 : ℝ))) (hd.comp measurable_fst)) hk
  convert hm using 1
  funext z
  dsimp only [budgetClip, δ]
  split_ifs <;> rfl

/-- Replace nonintegrable columns by zero, preserving every integrable column. -/
def integrableColumnKernel (ν : Measure Y) (k : X × Y → ℝ) (z : X × Y) : ℝ :=
  if Integrable (fun y => k (z.1, y)) ν then k z else 0

omit [MeasurableSpace X] in
theorem integrable_integrableColumnKernel (ν : Measure Y) (k : X × Y → ℝ) (x : X) :
    Integrable (fun y => integrableColumnKernel ν k (x, y)) ν := by
  by_cases hi : Integrable (fun y => k (x, y)) ν
  · simpa only [integrableColumnKernel, if_pos hi] using hi
  · simpa only [integrableColumnKernel, if_neg hi] using
      (integrable_zero Y ℝ ν : Integrable (fun _ : Y => (0 : ℝ)) ν)

theorem measurable_integrableColumnKernel [SFinite ν] {k : X × Y → ℝ}
    (hk : Measurable k) : Measurable (integrableColumnKernel ν k) := by
  have hs : MeasurableSet {x | Integrable (fun y => k (x, y)) ν} :=
    measurableSet_integrable hk.stronglyMeasurable
  exact hk.ite (hs.preimage measurable_fst) measurable_const

omit [MeasurableSpace X] in
theorem integrableColumnKernel_eq_of_integrable {k : X × Y → ℝ} {x : X}
    (hi : Integrable (fun y => k (x, y)) ν) (y : Y) :
    integrableColumnKernel ν k (x, y) = k (x, y) := by
  simp only [integrableColumnKernel, if_pos hi]

/-- A jointly measurable clipping construction valid also for kernels whose
columns are integrable only almost everywhere. -/
def budgetClipKernel (ν : Measure Y) (k : X × Y → ℝ) (d : X → ℝ) (z : X × Y) : ℝ :=
  budgetClip ν (fun y => integrableColumnKernel ν k (z.1, y)) (d z.1) z.2

theorem measurable_budgetClipKernel [SFinite ν] {k : X × Y → ℝ} {d : X → ℝ}
    (hk : Measurable k) (hd : Measurable d) : Measurable (budgetClipKernel ν k d) :=
  measurable_budgetClip (measurable_integrableColumnKernel hk) hd
    (integrable_integrableColumnKernel ν k)

omit [MeasurableSpace X] in
theorem budgetClipKernel_column_eq {k : X × Y → ℝ} {d : X → ℝ} {x : X}
    (hi : Integrable (fun y => k (x, y)) ν) :
    (fun y => budgetClipKernel ν k d (x, y)) = budgetClip ν (fun y => k (x, y)) (d x) := by
  have heq : (fun y => integrableColumnKernel ν k (x, y)) = (fun y => k (x, y)) :=
    funext (integrableColumnKernel_eq_of_integrable hi)
  simp only [budgetClipKernel, heq]

omit [MeasurableSpace X] in
theorem norm_budgetClipKernel_le (k : X × Y → ℝ) (d : X → ℝ) (z : X × Y) :
    ‖budgetClipKernel ν k d z‖ ≤ ‖k z‖ := by
  apply (norm_budgetClip_le ν _ _ _).trans
  dsimp only [integrableColumnKernel]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (k z)

end ThesisCommon
