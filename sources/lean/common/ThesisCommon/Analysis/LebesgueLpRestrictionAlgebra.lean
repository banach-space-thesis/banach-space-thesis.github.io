import ThesisCommon.Analysis.LebesgueLpRestrictions
import ThesisCommon.LpCut

/-! Exact retraction and cutoff algebra for actual measurable Lp parts. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lebesgueLpRestrict_comp_extend (D : Set X) (hD : MeasurableSet D) :
    (lebesgueLpRestrict (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D).comp
      (lebesgueLpExtend (𝕜 := 𝕜) D hD).toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 (Lp 𝕜 p (μ.restrict D)) := by
  ext f : 1
  exact lebesgueLpRestrict_extend D hD f

theorem lebesgueLpExtend_comp_restrict (D : Set X) (hD : MeasurableSet D) :
    (lebesgueLpExtend (𝕜 := 𝕜) (p := p) (μ := μ) D hD).toContinuousLinearMap.comp
      (lebesgueLpRestrict (𝕜 := 𝕜) D) = lpCutL D hD := by
  ext f : 1
  apply Lp.ext
  filter_upwards [lebesgueLpExtend_coe (𝕜 := 𝕜) D hD (lebesgueLpRestrict (𝕜 := 𝕜) D f),
    (ae_restrict_iff' hD).mp (lebesgueLpRestrict_coe (𝕜 := 𝕜) D f),
    lpCut_coe D hD f] with x he hr hc
  change lebesgueLpExtend (𝕜 := 𝕜) D hD (lebesgueLpRestrict (𝕜 := 𝕜) D f) x = lpCut D hD f x
  rw [he, hc]
  by_cases hx : x ∈ D <;> simp [hx, hr]

end ThesisCommon
