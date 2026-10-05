import ThesisCommon.Analysis.DominatedRadonNikodym

/-! Everywhere bounded measurable densities for dominated finite measures.

Radon--Nikodym domination initially gives only an almost-everywhere bound.
Clamping the real density to the prescribed nonnegative constant repairs
the exceptional null set while retaining the represented measure.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X]

/-- A measure bounded by `ofReal C • μ`, with finite `μ`, has a measurable
real density in `[0,C]` at every point. Zero measures and `C = 0` are included;
no probability or nonzero-mass hypothesis is imposed. -/
theorem exists_bounded_density_of_le_smul (σ μ : Measure X) [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hle : σ ≤ ENNReal.ofReal C • μ) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ C) ∧
      Integrable g μ ∧ μ.withDensity (fun x => ENNReal.ofReal (g x)) = σ := by
  letI : IsFiniteMeasure (ENNReal.ofReal C • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure σ := isFiniteMeasure_of_le (ENNReal.ofReal C • μ) hle
  have hle' : σ ≤ μ.withDensity (fun _ => ENNReal.ofReal C) := by
    simpa only [withDensity_const] using hle
  obtain ⟨r, hrm, hrpos, hri, hrle, hrepr⟩ := exists_density_of_le_withDensity σ μ
    (integrable_const C) (Eventually.of_forall fun _ => hC) hle'
  let g : X → ℝ := fun x => min (r x) C
  have hgm : Measurable g := hrm.min measurable_const
  have hg_bound : ∀ x, 0 ≤ g x ∧ g x ≤ C :=
    fun x => ⟨le_min (hrpos x) hC, min_le_right _ _⟩
  have hgr : g =ᵐ[μ] r := hrle.mono fun x hx => min_eq_left hx
  refine ⟨g, hgm, hg_bound, hri.congr hgr.symm, ?_⟩
  calc
    μ.withDensity (fun x => ENNReal.ofReal (g x)) =
        μ.withDensity (fun x => ENNReal.ofReal (r x)) :=
      withDensity_congr_ae (hgr.mono fun _ hx => congrArg ENNReal.ofReal hx)
    _ = σ := hrepr

end ThesisCommon
