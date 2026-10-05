import JLMS.EllOneSynthesis

/-!
# Finite ℓ¹ estimates give an actual closed embedding

A uniform lower estimate on finite scalar combinations passes to the
absolutely convergent ℓ¹ synthesis series. This turns the finite sign-tree
estimates in Hagler–Johnson into the precise ContainsEllOne predicate.
-/

noncomputable section
open Filter Topology
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem ellOneSynthesis_lower_of_finite (v : ℕ → X) {C c : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C)
    (hlower : ∀ F : Finset ℕ, ∀ a : ℕ → 𝕜,
      c * (∑ n ∈ F, ‖a n‖) ≤ ‖∑ n ∈ F, a n • v n‖) (a : ellOne 𝕜) :
    c * ‖a‖ ≤ ‖ellOneSynthesis v C hC hv a‖ := by
  have hleft : Tendsto (fun F : Finset ℕ => c * (∑ n ∈ F, ‖a n‖)) atTop (𝓝 (c * ‖a‖)) := by
    simpa only [← ellOneOn_norm_eq_tsum a] using
      (tendsto_const_nhds (x := c)).mul (ellOneOn_summable_norm a).hasSum
  have hright : Tendsto (fun F : Finset ℕ => ‖∑ n ∈ F, a n • v n‖) atTop
      (𝓝 ‖ellOneSynthesis v C hC hv a‖) := (summable_ellOne_smul v C hv a).hasSum.norm
  exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall (fun F => hlower F a))

theorem containsEllOne_of_finite_lower (v : ℕ → X) {C c : ℝ}
    (hC : 0 ≤ C) (hv : ∀ n, ‖v n‖ ≤ C) (hc : 0 < c)
    (hlower : ∀ F : Finset ℕ, ∀ a : ℕ → 𝕜,
      c * (∑ n ∈ F, ‖a n‖) ≤ ‖∑ n ∈ F, a n • v n‖) : ContainsEllOne 𝕜 X :=
  ⟨ellOneSynthesis v C hC hv, c, hc, ellOneSynthesis_lower_of_finite v hC hv hlower⟩

end JLMS
