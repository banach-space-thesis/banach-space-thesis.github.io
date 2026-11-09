import PL1.SchurExample
import Mathlib.Analysis.RCLike.Extend

/-!
# Weak convergence and the Schur property under restriction to real scalars

The full real and complex continuous duals induce the same sequential weak
convergence. The application uses the explicit restricted scalar action and
the inherited norm appearing in the reviewed theorem statements.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
variable [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem weaklyConverges_iff_real {x : ℕ → E} {a : E} :
    WeaklyConverges 𝕜 E x a ↔ WeaklyConverges ℝ E x a := by
  constructor
  · intro hx φ
    have h := (RCLike.continuous_re.tendsto (StrongDual.extendRCLike (𝕜 := 𝕜) φ a)).comp
      (hx (StrongDual.extendRCLike (𝕜 := 𝕜) φ))
    simpa only [Function.comp_def, StrongDual.re_extendRCLike_apply] using h
  · intro hx φ
    have hr : Tendsto (fun n => RCLike.re (φ (x n))) atTop (𝓝 (RCLike.re (φ a))) :=
      hx (RCLike.reCLM.comp (φ.restrictScalars ℝ))
    have hi : Tendsto (fun n => RCLike.im (φ (x n))) atTop (𝓝 (RCLike.im (φ a))) :=
      hx (RCLike.imCLM.comp (φ.restrictScalars ℝ))
    have hr' := ((RCLike.continuous_ofReal : Continuous (fun r : ℝ => (r : 𝕜))).tendsto _).comp hr
    have hi' := ((RCLike.continuous_ofReal : Continuous (fun r : ℝ => (r : 𝕜))).tendsto _).comp hi
    simpa only [Function.comp_def, RCLike.re_add_im] using hr'.add (hi'.mul_const RCLike.I)

theorem hasSchurProperty_iff_real : HasSchurProperty 𝕜 E ↔ HasSchurProperty ℝ E := by
  constructor
  · intro h x a hx
    exact h x a (weaklyConverges_iff_real.mpr hx)
  · intro h x a hx
    exact h x a (weaklyConverges_iff_real.mp hx)

end PL1

namespace PL1

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- This statement spells out the inherited additive norm and restricted
real scalar action, so type-alias instance inference cannot select a different action. -/
theorem hasSchurProperty_iff_underlyingReal :
    HasSchurProperty 𝕜 E ↔
      @HasSchurProperty ℝ _ (UnderlyingReal 𝕜 E)
        (inferInstance : NormedAddCommGroup E) (NormedSpace.restrictScalars ℝ 𝕜 E) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  exact hasSchurProperty_iff_real

theorem Noise.schurRates_projection_range_underlyingReal_hasSchurProperty :
    @HasSchurProperty ℝ _ (UnderlyingReal 𝕜 (Noise.projection 𝕜 Noise.schurRates).range)
      (inferInstance : NormedAddCommGroup (Noise.projection 𝕜 Noise.schurRates).range)
      (NormedSpace.restrictScalars ℝ 𝕜 (Noise.projection 𝕜 Noise.schurRates).range) :=
  (hasSchurProperty_iff_underlyingReal 𝕜 _).mp
    (Noise.schurRates_projection_range_hasSchurProperty 𝕜)

end PL1
