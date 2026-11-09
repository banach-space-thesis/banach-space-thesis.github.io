import SurveyStatements.P5L1VariationLinfty
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Almost-everywhere uniform bounds survive strong Lp limits. This will
transfer bounds of genuine dyadic conditional means to their limiting density. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SurveyStatements.P5L1Variation

theorem ae_norm_bound_of_tendsto_Lp {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℕ → Lp E p μ) (g : Lp E p μ) (C : ℝ)
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hg : Tendsto f atTop (𝓝 g)) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
  obtain ⟨φ, hφmono, hφ⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hφ] with x hx hlim
  exact le_of_tendsto hlim.norm (Eventually.of_forall (fun n => hx (φ n)))

theorem isClosed_ae_norm_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (C : ℝ) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, ‖f x‖ ≤ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hg
  exact ae_norm_bound_of_tendsto_Lp f g C hf hg

end SurveyStatements.P5L1Variation

