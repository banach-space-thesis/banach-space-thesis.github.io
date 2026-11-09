import SurveyStatements.P5HaarNorm
import SurveyStatements.P5MixedPointwiseMultiplication
import SurveyStatements.P5Support.SignAveraging

/-! Bilinearity of actual Bochner tensors over every RCLike field. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def tensorInnerMap (f : Lp 𝕜 p unitIntervalMeasure) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] MixedNorm 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := fun g => tensorWith g f
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [tensorWith_ae (g + h) f, tensorWith_ae g f,
          tensorWith_ae h f, Lp.coeFn_add (tensorWith g f) (tensorWith h f)]
          with x hsum hg hh hadd
        simp only [Pi.add_apply] at hadd
        rw [hsum, hadd, hg, hh]
        exact smul_add _ _ _
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [tensorWith_ae (c • g) f, tensorWith_ae g f,
          Lp.coeFn_smul c (tensorWith g f)] with x hc hg hmul
        simp only [Pi.smul_apply] at hmul
        simp only [RingHom.id_apply]
        rw [hc, hmul, hg]
        exact smul_comm _ _ _ }
    ‖f‖ (fun g => by simpa only [mul_comm] using (norm_tensorWith 𝕜 p g f).le)

theorem tensorWith_sum_inner {ι : Type*} (F : Finset ι)
    (g : ι → Lp 𝕜 1 unitIntervalMeasure) (f : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith (∑ i ∈ F, g i) f = ∑ i ∈ F, tensorWith (g i) f :=
  map_sum (tensorInnerMap f) _ _

theorem tensorWith_smul_inner (c : 𝕜) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) : tensorWith (c • g) f = c • tensorWith g f :=
  map_smul (tensorInnerMap f) c g

theorem tensorWith_neg_inner (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) : tensorWith (-g) f = -(tensorWith g f) :=
  map_neg (tensorInnerMap f) g

theorem tensorWith_signed_inner (b : Bool) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith (P5Support.signedValue b g) f = P5Support.signedValue b (tensorWith g f) := by
  cases b
  · change tensorInnerMap f (-g) = -(tensorInnerMap f g)
    exact map_neg _ _
  · rfl

theorem tensorWith_signed_outer (b : Bool) (g : Lp 𝕜 1 unitIntervalMeasure)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith g (P5Support.signedValue b f) = P5Support.signedValue b (tensorWith g f) := by
  cases b <;> simp [P5Support.signedValue, map_neg]

end SurveyStatements.P5
