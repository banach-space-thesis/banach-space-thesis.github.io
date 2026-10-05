import JLMS.ContinuityIdeal
import JLMS.DiscontinuousLinearWitness
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Continuity on a subspace whose null sequences factor

This is the final analytic implication used in Ogden Theorem 6.18. A null
sequence xₙ = yₙa with yₙ → 0 and a in the continuity ideal has θ(xₙ) → 0.
Rescaling witnesses to discontinuity proves continuity of the restriction.
The factorization property is explicit here; proving it from a bounded
approximate identity is the separate Cohen-factorization obligation.
-/

noncomputable section
namespace JLMS
open Filter Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

theorem continuous_restriction_of_nullSequences_factor
    (θ : B →ₙₐ[𝕜] A) (P : Submodule 𝕜 B) (hP : P ≤ continuityIdeal θ)
    (hfactor : ∀ x : ℕ → P, Tendsto x atTop (𝓝 0) →
      ∃ a ∈ P, ∃ y : ℕ → B, Tendsto y atTop (𝓝 0) ∧
        ∀ n, (x n).val = y n * a) :
    Continuous (fun x : P => θ x.val) := by
  let f : P →ₗ[𝕜] A := {
    toFun x := θ x.val
    map_add' x y := θ.map_add _ _
    map_smul' c x := θ.map_smul _ _
  }
  by_contra h
  have hf : ¬ Continuous f := h
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hrone : r < 1 := by norm_num [r]
  have hw (n : ℕ) := exists_small_large_of_not_continuous f hf (pow_pos hr n) 1
  choose x hx hlarge using hw
  have hxzero : Tendsto x atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun n => norm_nonneg (x n)) hx
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hrone))
  obtain ⟨a, ha, y, hy, hxy⟩ := hfactor x hxzero
  have hlim := ((hP ha).2.tendsto (0 : B)).comp hy
  have hzero : Tendsto (fun n => θ (x n).val) atTop (𝓝 0) := by
    simpa only [Function.comp_def, homRightLinear_apply, ← hxy, zero_mul, map_zero] using hlim
  have hnorm : Tendsto (fun n => ‖θ (x n).val‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hzero.norm
  obtain ⟨n, hn⟩ := (hnorm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
  exact (not_lt_of_ge hn.le) (hlarge n)

end JLMS
