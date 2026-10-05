import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic

/-! A finite measure dominated by an integrable nonnegative density has a
measurable real density bounded by that same function almost everywhere. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {Z : Type*} [MeasurableSpace Z]

theorem exists_density_of_le_withDensity (M ρ : Measure Z) [IsFiniteMeasure M] [SigmaFinite ρ]
    {k : Z → ℝ} (hki : Integrable k ρ) (hkpos : 0 ≤ᵐ[ρ] k)
    (hle : M ≤ ρ.withDensity (fun z => ENNReal.ofReal (k z))) :
    ∃ r : Z → ℝ, Measurable r ∧ (∀ z, 0 ≤ r z) ∧ Integrable r ρ ∧
      r ≤ᵐ[ρ] k ∧ ρ.withDensity (fun z => ENNReal.ofReal (r z)) = M := by
  let r : Z → ℝ := fun z => (M.rnDeriv ρ z).toReal
  have hrm : Measurable r := (Measure.measurable_rnDeriv M ρ).ennreal_toReal
  have hrpos : ∀ z, 0 ≤ r z := fun _ => ENNReal.toReal_nonneg
  have hri : Integrable r ρ := integrable_toReal_of_lintegral_ne_top
    (Measure.measurable_rnDeriv M ρ).aemeasurable (Measure.lintegral_rnDeriv_lt_top M ρ).ne
  have hAC : M ≪ ρ := (Measure.absolutelyContinuous_of_le hle).trans
    (withDensity_absolutelyContinuous _ _)
  have hrepr : ρ.withDensity (fun z => ENNReal.ofReal (r z)) = M := by
    calc
      ρ.withDensity (fun z => ENNReal.ofReal (r z)) = ρ.withDensity (M.rnDeriv ρ) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top M ρ] with z hz
        exact ENNReal.ofReal_toReal hz
      _ = M := Measure.withDensity_rnDeriv_eq M ρ hAC
  have hrle : r ≤ᵐ[ρ] k := by
    apply ae_le_of_forall_setIntegral_le hri hki
    intro s hs _
    have hleft : (∫ z in s, r z ∂ρ) = M.real s :=
      Measure.setIntegral_toReal_rnDeriv' hAC hs
    have hright : (ρ.withDensity (fun z => ENNReal.ofReal (k z))).real s = ∫ z in s, k z ∂ρ := by
      rw [measureReal_def, withDensity_apply _ hs,
        ← ofReal_integral_eq_lintegral_ofReal hki.integrableOn (ae_restrict_of_ae hkpos),
        ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hkpos))]
    letI : IsFiniteMeasure (ρ.withDensity (fun z => ENNReal.ofReal (k z))) :=
      isFiniteMeasure_withDensity_ofReal hki.2
    rw [hleft, ← hright]
    exact ENNReal.toReal_mono (measure_ne_top _ s) (hle s)
  exact ⟨r, hrm, hrpos, hri, hrle, hrepr⟩

end ThesisCommon
