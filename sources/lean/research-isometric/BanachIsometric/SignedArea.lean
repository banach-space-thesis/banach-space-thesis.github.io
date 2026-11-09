import BanachIsometric.BranchFiberSum
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Signed multiplicity formula for the actual Fréchet derivative

The regular set and its measurable injective decomposition are constructed.
Outside that set the signed Jacobian is zero, including the nondifferentiability
points where Mathlib defines the derivative to be zero. No preassigned degree,
homotopy invariance, or local degree stability is assumed in this analytic result.
-/

namespace BanachIsometric

open MeasureTheory Set Function
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual differentiable regular points of a map. -/
def differentiableRegularSet (f : E → E) : Set E :=
  {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0}

theorem measurableSet_differentiableRegularSet (f : E → E) :
    MeasurableSet (differentiableRegularSet f) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hm : Measurable (fun x => (fderiv ℝ f x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
  have hz : MeasurableSet {x | (fderiv ℝ f x).det = 0} :=
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).measurableSet.preimage hm
  exact (measurableSet_of_differentiableAt ℝ f).inter hz.compl

variable [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A signed Jacobian vanishes at every point outside the regular set; no
almost-everywhere differentiability assumption is needed for this statement. -/
theorem det_fderiv_eq_zero_of_not_regular {f : E → E} {x : E}
    (hx : x ∉ differentiableRegularSet f) : (fderiv ℝ f x).det = 0 := by
  classical
  by_cases hdiff : DifferentiableAt ℝ f x
  · exact not_ne_iff.mp (fun hn => hx ⟨hdiff, hn⟩)
  · rw [fderiv_zero_of_not_differentiableAt hdiff]
    change LinearMap.det (0 : E →ₗ[ℝ] E) = 0
    rw [LinearMap.det_zero, zero_pow (Module.finrank_pos.ne')]

/-- The intrinsic regular-fiber multiplicity of the actual map and source. -/
noncomputable def signedRegularMultiplicity (f : E → E) (s : Set E) (y : E) : ℝ :=
  signedFiberSum f (fderiv ℝ f) (s ∩ differentiableRegularSet f) y

/-- A genuine signed many-to-one integral formula. The density is the actual
signed sum over the map's regular fiber, with no chosen branch data in the
statement. For a Lipschitz map it is the signed regular multiplicity used in
the area-degree argument; identifying it with topological degree is separate.
-/
theorem integral_signedRegularMultiplicity (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) {s : Set E} (hs : MeasurableSet s) (g : E → ℝ)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * g (f x)) s μ) :
    (∫ y, signedRegularMultiplicity f s y * g y ∂μ) =
      ∫ x in s, (fderiv ℝ f x).det * g (f x) ∂μ := by
  have hreg := measurableSet_differentiableRegularSet f
  have hformula := integral_signedFiberSum μ (hs.inter hreg)
    (fun x hx => hx.2.1.hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => hx.2.2) g (hint.mono_set inter_subset_left)
  change (∫ y, signedRegularMultiplicity f s y * g y ∂μ) =
    ∫ x in s ∩ differentiableRegularSet f, (fderiv ℝ f x).det * g (f x) ∂μ at hformula
  rw [hformula]
  have hzero : (∫ x in s \ differentiableRegularSet f,
      (fderiv ℝ f x).det * g (f x) ∂μ) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [det_fderiv_eq_zero_of_not_regular hx.2, zero_mul]
  have hsplit := integral_inter_add_diff hreg hint
  rwa [hzero, add_zero] at hsplit

end BanachIsometric
