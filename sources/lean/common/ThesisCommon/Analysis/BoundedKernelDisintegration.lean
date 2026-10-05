import ThesisCommon.Analysis.BoundedMeasureDensity
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.WithDensity

/-! Disintegration relative to a dominating base measure.

A bounded density changes the first marginal of a finite product measure
back to the prescribed base measure. Weighting the genuine conditional
kernel by that density gives a measurable kernel with a uniform mass bound
at every point, whose composition product is the original measure.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Weight each fibre of a kernel by a density on its source space. -/
def densityWeightedKernel (κ : Kernel X Y) [IsSFiniteKernel κ] (g : X → ℝ) : Kernel X Y :=
  κ.withDensity (fun x _ => ENNReal.ofReal (g x))

theorem densityWeightedKernel_apply (κ : Kernel X Y) [IsSFiniteKernel κ]
    {g : X → ℝ} (hg : Measurable g) (x : X) :
    densityWeightedKernel κ g x = ENNReal.ofReal (g x) • κ x := by
  rw [densityWeightedKernel, Kernel.withDensity_apply _ (hg.comp measurable_fst).ennreal_ofReal,
    withDensity_const]

theorem densityWeightedKernel_isFinite (κ : Kernel X Y) [IsFiniteKernel κ]
    {g : X → ℝ} {C : ℝ} (hgC : ∀ x, g x ≤ C) :
    IsFiniteKernel (densityWeightedKernel κ g) :=
  Kernel.isFiniteKernel_withDensity_of_bounded κ ENNReal.ofReal_ne_top
    (fun x _ => ENNReal.ofReal_le_ofReal (hgC x))

theorem densityWeightedKernel_univ (κ : Kernel X Y) [IsMarkovKernel κ]
    {g : X → ℝ} (hg : Measurable g) (x : X) :
    densityWeightedKernel κ g x univ = ENNReal.ofReal (g x) := by
  rw [densityWeightedKernel_apply κ hg]
  simp

theorem densityWeightedKernel_univ_le (κ : Kernel X Y) [IsMarkovKernel κ]
    {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, g x ≤ C) (x : X) :
    densityWeightedKernel κ g x univ ≤ ENNReal.ofReal C := by
  rw [densityWeightedKernel_univ κ hg]
  exact ENNReal.ofReal_le_ofReal (hgC x)

/-- Move a measurable scalar density from the first measure to the kernel.
The s-finiteness hypotheses ensure both products are genuine integrals. -/
theorem compProd_densityWeightedKernel (μ : Measure X) [SFinite μ]
    (κ : Kernel X Y) [IsSFiniteKernel κ] {g : X → ℝ} (hg : Measurable g)
    [SFinite (μ.withDensity (fun x => ENNReal.ofReal (g x)))]
    [IsSFiniteKernel (densityWeightedKernel κ g)] :
    μ ⊗ₘ densityWeightedKernel κ g =
      (μ.withDensity (fun x => ENNReal.ofReal (g x))) ⊗ₘ κ := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul μ hg.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr
  intro x
  rw [densityWeightedKernel_apply κ hg, Measure.smul_apply]
  rfl

/-- A finite measure whose first marginal is bounded by `C μ` has an actual
measurable disintegration over `μ`, with every fibre of mass at most `C`.
For a nonempty standard Borel target the kernel is the clamped marginal
density times the Markov conditional kernel. An empty target gives the zero
kernel explicitly, so no nonemptiness or nonzero-measure premise is added. -/
theorem exists_bounded_disintegration (μ : Measure X) (ρ : Measure (X × Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ] [StandardBorelSpace Y]
    {C : ℝ} (hC : 0 ≤ C) (hfst : ρ.fst ≤ ENNReal.ofReal C • μ) :
    ∃ κ : Kernel X Y, IsFiniteKernel κ ∧
      (∀ x, κ x univ ≤ ENNReal.ofReal C) ∧ μ ⊗ₘ κ = ρ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · letI := hY
    refine ⟨0, inferInstance, fun x => by simp, ?_⟩
    have hρ : ρ = 0 := Subsingleton.elim _ _
    simp only [Measure.compProd_zero_right, hρ]
  · letI := hY
    obtain ⟨g, hgm, hgb, _, hrepr⟩ := exists_bounded_density_of_le_smul ρ.fst μ hC hfst
    let κ := densityWeightedKernel ρ.condKernel g
    letI : IsFiniteKernel κ := densityWeightedKernel_isFinite ρ.condKernel (fun x => (hgb x).2)
    letI : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x))) := by
      rw [hrepr]
      infer_instance
    refine ⟨κ, inferInstance, densityWeightedKernel_univ_le ρ.condKernel hgm
      (fun x => (hgb x).2), ?_⟩
    change μ ⊗ₘ densityWeightedKernel ρ.condKernel g = ρ
    rw [compProd_densityWeightedKernel μ ρ.condKernel hgm, hrepr]
    exact ρ.disintegrate ρ.condKernel

end ThesisCommon
