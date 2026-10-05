import JLMS.DiscontinuousLinearWitness
import JLMS.ContinuityIdeal
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Continuity from common continuity-ideal factors for null sequences

This packages the countable version of Ogden's projection argument. One
fixed pair of elements of the continuity ideal may depend on the sequence.
If they decompose every term of that sequence, both resulting image
sequences tend to zero. No uniform choice over all sequences is assumed.
-/

noncomputable section
namespace JLMS
open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜]

theorem continuous_linear_of_nullSequences
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ[𝕜] F)
    (hnull : ∀ x : ℕ → E, Tendsto x atTop (𝓝 0) →
      Tendsto (fun n => f (x n)) atTop (𝓝 0)) : Continuous f := by
  by_contra hf
  have hw (n : ℕ) := exists_small_large_of_not_continuous f hf
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n) 1
  choose x hx hlarge using hw
  have hxzero : Tendsto x atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg (x n)) hx
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  have hnorm : Tendsto (fun n => ‖f (x n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hnull x hxzero).norm
  obtain ⟨n, hn⟩ := (hnorm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
  exact (not_lt_of_ge hn.le) (hlarge n)

theorem continuous_restriction_of_common_ideal_factors
    {B A : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
    [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    (θ : B →ₙₐ[𝕜] A) (P : Submodule 𝕜 B)
    (hcommon : ∀ x : ℕ → P, ∃ a ∈ continuityIdeal θ, ∃ b ∈ continuityIdeal θ,
      ∀ n, (x n).val = a * ((x n).val - (x n).val * b) + (x n).val * b) :
    Continuous (fun x : P => θ x.val) := by
  let f : P →ₗ[𝕜] A :=
    { toFun x := θ x.val
      map_add' x y := θ.map_add _ _
      map_smul' c x := θ.map_smul _ _ }
  apply continuous_linear_of_nullSequences f
  intro x hx
  obtain ⟨a, ha, b, hb, he⟩ := hcommon x
  have hxB : Tendsto (fun n => (x n).val) atTop (𝓝 (0 : B)) :=
    P.subtypeL.continuous.tendsto 0 |>.comp hx
  have hxb : Tendsto (fun n => (x n).val * b) atTop (𝓝 (0 : B)) := by
    simpa using hxB.mul tendsto_const_nhds
  have hdiff : Tendsto (fun n => (x n).val - (x n).val * b) atTop (𝓝 (0 : B)) := by
    simpa using hxB.sub hxb
  have ha0 := (ha.1.tendsto (0 : B)).comp hdiff
  have hb0 := (hb.2.tendsto (0 : B)).comp hxB
  have hsum : Tendsto
      (fun n => θ (a * ((x n).val - (x n).val * b)) + θ ((x n).val * b))
        atTop (𝓝 (0 : A)) := by
    simpa only [Function.comp_def, homLeftLinear_apply, homRightLinear_apply,
      mul_zero, zero_mul, map_zero, zero_add] using ha0.add hb0
  convert hsum using 1
  funext n
  change θ (x n).val = _
  rw [← map_add]
  exact congrArg θ (he n)

end JLMS
