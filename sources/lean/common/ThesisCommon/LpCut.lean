import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiplication by a measurable indicator on actual Lp equivalence classes. -/
def lpCut (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) : Lp 𝕜 p μ :=
  ((Lp.memLp f).indicator hA).toLp (A.indicator f)

omit [Fact (1 ≤ p)] in
theorem lpCut_coe (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) :
    lpCut A hA f =ᵐ[μ] A.indicator f := MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
theorem lpCut_add (A : Set X) (hA : MeasurableSet A) (f g : Lp 𝕜 p μ) :
    lpCut A hA (f + g) = lpCut A hA f + lpCut A hA g := by
  apply Lp.ext
  filter_upwards [lpCut_coe A hA (f + g), lpCut_coe A hA f,
    lpCut_coe A hA g, Lp.coeFn_add f g, Lp.coeFn_add (lpCut A hA f) (lpCut A hA g)]
    with x h1 h2 h3 h4 h5
  by_cases hx : x ∈ A <;> simp_all

theorem lpCut_smul (A : Set X) (hA : MeasurableSet A) (a : 𝕜) (f : Lp 𝕜 p μ) :
    lpCut A hA (a • f) = a • lpCut A hA f := by
  apply Lp.ext
  filter_upwards [lpCut_coe A hA (a • f), lpCut_coe A hA f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (lpCut A hA f)] with x h1 h2 h3 h4
  by_cases hx : x ∈ A <;> simp_all

omit [Fact (1 ≤ p)] in
theorem norm_lpCut_le (A : Set X) (hA : MeasurableSet A) (f : Lp 𝕜 p μ) :
    ‖lpCut A hA f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpCut_coe A hA f] with x hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h]

/-- The genuine bounded multiplication operator χ_A, of norm at most one. -/
def lpCutL (A : Set X) (hA : MeasurableSet A) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := lpCut A hA
      map_add' := lpCut_add A hA
      map_smul' := lpCut_smul A hA }
    1 (by intro f; simpa using norm_lpCut_le A hA f)

theorem norm_lpCutL_le (A : Set X) (hA : MeasurableSet A) :
    ‖lpCutL (𝕜 := 𝕜) (μ := μ) (p := p) A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_lpCut_le A hA f

end ThesisCommon
