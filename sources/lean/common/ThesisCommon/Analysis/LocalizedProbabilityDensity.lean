import ThesisCommon.Analysis.SigmaFiniteProbabilityDensity

/-! Normalize a sigma-finite measurable part while leaving its complement unchanged. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def patchDensity (s : Set X) (g : X → ℝ≥0) : X → ℝ≥0 :=
  s.piecewise g (fun _ => 1)

theorem measurable_patchDensity {s : Set X} (hs : MeasurableSet s) {g : X → ℝ≥0}
    (hg : Measurable g) : Measurable (patchDensity s g) :=
  hg.piecewise hs measurable_const

theorem patchDensity_pos {s : Set X} (hs : MeasurableSet s) {g : X → ℝ≥0}
    (hg : ∀ᵐ x ∂μ.restrict s, 0 < g x) : ∀ᵐ x ∂μ, 0 < patchDensity s g x := by
  filter_upwards [(ae_restrict_iff' hs).mp hg] with x hx
  by_cases hxs : x ∈ s
  · simpa [patchDensity, hxs] using hx hxs
  · simp [patchDensity, hxs]

theorem patchDensity_le {s : Set X} {g : X → ℝ≥0} {C : ℝ≥0}
    (hg : ∀ x, g x ≤ C) : ∀ x, patchDensity s g x ≤ max C 1 := by
  intro x
  by_cases hx : x ∈ s
  · simpa [patchDensity, hx] using (hg x).trans (le_max_left C 1)
  · simp [patchDensity, hx]

theorem restrict_withDensity_patchDensity {s : Set X} (hs : MeasurableSet s)
    (g : X → ℝ≥0) :
    (μ.withDensity (fun x => (patchDensity s g x : ℝ≥0∞))).restrict s =
      (μ.restrict s).withDensity (fun x => (g x : ℝ≥0∞)) := by
  rw [restrict_withDensity hs]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [patchDensity, hx]

theorem restrict_compl_withDensity_patchDensity {s : Set X} (hs : MeasurableSet s)
    (g : X → ℝ≥0) :
    (μ.withDensity (fun x => (patchDensity s g x : ℝ≥0∞))).restrict sᶜ = μ.restrict sᶜ := by
  rw [restrict_withDensity hs.compl]
  have h : (fun x => (patchDensity s g x : ℝ≥0∞)) =ᵐ[μ.restrict sᶜ] 1 := by
    filter_upwards [ae_restrict_mem hs.compl] with x hx
    change x ∉ s at hx
    simp [patchDensity, hx]
  rw [withDensity_congr_ae h, withDensity_one]

theorem exists_localized_probability_density (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) [SigmaFinite (μ.restrict s)] :
    ∃ (g : X → ℝ≥0) (C : ℝ≥0), Measurable g ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
      (∀ x, g x ≤ C) ∧
      (μ.withDensity (fun x => (g x : ℝ≥0∞))).restrict sᶜ = μ.restrict sᶜ ∧
      (μ.withDensity (fun x => (g x : ℝ≥0∞))) s < ⊤ ∧
      (μ s ≠ 0 → (μ.withDensity (fun x => (g x : ℝ≥0∞))) s = 1) := by
  by_cases hzero : μ s = 0
  · refine ⟨fun _ => 1, 1, measurable_const, Eventually.of_forall (fun _ => zero_lt_one),
      fun _ => le_rfl, ?_, ?_, ?_⟩
    · simp
    · simpa [hzero]
    · exact fun h => (h hzero).elim
  · obtain ⟨g, C, hg, hpos, hbound, hmass⟩ :=
      exists_positive_bounded_probability_density (μ.restrict s)
        (Measure.restrict_eq_zero.not.mpr hzero)
    have hmass' : (μ.withDensity (fun x => (patchDensity s g x : ℝ≥0∞))) s = 1 := by
      have := congrArg (fun ν : Measure X => ν univ) (restrict_withDensity_patchDensity hs g (μ := μ))
      simpa only [Measure.restrict_apply_univ, hmass] using this
    exact ⟨patchDensity s g, max C 1, measurable_patchDensity hs hg,
      patchDensity_pos hs hpos, patchDensity_le hbound,
      restrict_compl_withDensity_patchDensity hs g, by rw [hmass']; exact ENNReal.one_lt_top,
      fun _ => hmass'⟩

end ThesisCommon
