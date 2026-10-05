import ThesisCommon.Analysis.L1Lattice
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Tactic

/-! The weighted L1 isometry is onto when the weight is positive almost
everywhere. A sigma-finite measure admits such a finite weighted measure. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ≥0}

theorem withDensitySMulLI_coe (hg : Measurable g)
    (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) :
    withDensitySMulLI μ hg f =ᵐ[μ] fun x => (g x : ℝ) * f x := by
  simpa only [withDensitySMulLI_apply, NNReal.smul_def, smul_eq_mul] using
    (memL1_smul_of_L1_withDensity hg f).coeFn_toLp

theorem ae_withDensity_coe_iff_of_pos (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x)
    {p : X → Prop} : (∀ᵐ x ∂μ.withDensity (fun x => (g x : ℝ≥0∞)), p x) ↔ ∀ᵐ x ∂μ, p x := by
  rw [ae_withDensity_iff hg.coe_nnreal_ennreal]
  constructor
  · intro h
    filter_upwards [h, hpos] with x hx hxpos
    exact hx (by exact_mod_cast hxpos.ne')
  · exact fun h => h.mono fun _ hx _ => hx

theorem withDensitySMulLI_surjective (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    Function.Surjective (withDensitySMulLI μ (E := ℝ) hg) := by
  intro f
  let v : X → ℝ := fun x => (g x : ℝ)⁻¹ * f x
  have heq : (fun x => (g x : ℝ) * v x) =ᵐ[μ] f := hpos.mono fun x hx => by
    have hx' : (g x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    dsimp [v]
    rw [← mul_assoc, mul_inv_cancel₀ hx', one_mul]
  have hi : Integrable v (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
    apply (integrable_withDensity_iff_integrable_coe_smul hg).mpr
    simpa only [smul_eq_mul] using (L1.integrable_coeFn f).congr heq.symm
  refine ⟨hi.toL1 v, ?_⟩
  apply Lp.ext
  filter_upwards [withDensitySMulLI_coe hg (hi.toL1 v), heq,
    (ae_withDensity_coe_iff_of_pos hg hpos).mp (Integrable.coeFn_toL1 hi)] with x hx hx' hx''
  rw [hx, hx'', hx']

def lOneWithDensityEquiv (hg : Measurable g) (hpos : ∀ᵐ x ∂μ, 0 < g x) :
    Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞))) ≃ₗᵢ[ℝ] Lp ℝ 1 μ :=
  LinearIsometryEquiv.ofSurjective (withDensitySMulLI μ hg) (withDensitySMulLI_surjective hg hpos)

theorem withDensitySMulLI_nonneg (hg : Measurable g)
    (f : Lp ℝ 1 (μ.withDensity (fun x => (g x : ℝ≥0∞)))) (hf : 0 ≤ f) :
    0 ≤ withDensitySMulLI μ hg f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [withDensitySMulLI_coe hg f,
    (ae_withDensity_iff hg.coe_nnreal_ennreal).mp ((Lp.coeFn_nonneg f).mpr hf)] with x hx hfx
  rw [hx]
  by_cases hxg : g x = 0
  · simp [hxg]
  · exact mul_nonneg (NNReal.coe_nonneg _) (hfx (by exact_mod_cast hxg))

/-- The positive density of the finite measure equivalent to mu. This also
handles the zero measure; no probability/nonzero premise is added. -/
theorem exists_positive_finite_density (μ : Measure X) [SigmaFinite μ] :
    ∃ g : X → ℝ≥0, Measurable g ∧ (∀ᵐ x ∂μ, 0 < g x) ∧
      IsFiniteMeasure (μ.withDensity (fun x => (g x : ℝ≥0∞))) := by
  let g : X → ℝ≥0 := fun x => (μ.toFinite.rnDeriv μ x).toNNReal
  have hg : Measurable g := (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
  have heq : μ.withDensity (fun x => (g x : ℝ≥0∞)) = μ.toFinite := by
    calc
      μ.withDensity (fun x => (g x : ℝ≥0∞)) = μ.withDensity (μ.toFinite.rnDeriv μ) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top μ.toFinite μ] with x hx
        exact ENNReal.coe_toNNReal hx
      _ = μ.toFinite := Measure.withDensity_rnDeriv_eq _ _ (toFinite_absolutelyContinuous μ)
  refine ⟨g, hg, ?_, heq.symm ▸ inferInstance⟩
  filter_upwards [Measure.rnDeriv_pos' (absolutelyContinuous_toFinite μ),
    Measure.rnDeriv_ne_top μ.toFinite μ] with x hx hx'
  exact ENNReal.toNNReal_pos hx.ne' hx'

end ThesisCommon
