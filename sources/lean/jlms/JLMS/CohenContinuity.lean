import JLMS.CohenFactorization
import JLMS.NullFactorizationContinuity
import JLMS.CodimensionOneContinuity

/-!
# Automatic continuity from an ideal with a bounded approximate identity

These are the final analytic implications in Ogden Theorem 6.18. Cohen
factorization is proved in the imported construction, so the remaining
geometric inputs are exactly the bounded right approximate identity and
containment in the continuity ideal.
-/

noncomputable section
open Filter Topology
namespace JLMS

variable {𝕜 B A : Type*} [RCLike 𝕜]
  [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [NormOneClass B]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A]

omit [CompleteSpace B] [NormOneClass B] in
/-- Any uniformly bounded right approximate identity, indexed by a nontrivial
filter, supplies the finite approximation property used by Cohen's proof. -/
theorem hasBoundedRightApproximation_of_tendsto
    (P : Submodule 𝕜 B) {ι : Type*} (l : Filter ι) [l.NeBot]
    (e : ι → B) (he : ∀ i, e i ∈ P) {M : ℝ} (hM : ∀ i, ‖e i‖ ≤ M)
    (happrox : ∀ z : P, Tendsto (fun i => z.val * e i) l (𝓝 z.val)) :
    HasBoundedRightApproximation P M := by
  intro s ε hε
  have hfinite : ∀ᶠ i in l, ∀ z ∈ s, ‖z.val - z.val * e i‖ < ε := by
    apply s.eventually_all.mpr
    intro z hz
    have hzero := ((tendsto_const_nhds (x := z.val)).sub (happrox z)).norm
    have hzero' : Tendsto (fun i => ‖z.val - z.val * e i‖) l (𝓝 (0 : ℝ)) := by
      simpa using hzero
    exact hzero'.eventually (eventually_lt_nhds hε)
  obtain ⟨i, hi⟩ := hfinite.exists
  exact ⟨e i, he i, hM i, fun z hz => (hi z hz).le⟩

theorem continuous_restriction_of_boundedRightApproximation
    (θ : B →ₙₐ[𝕜] A) (P : Submodule 𝕜 B)
    (hP : P ≤ continuityIdeal θ) (hclosed : IsClosed (P : Set B))
    (hleft : ∀ a b : B, b ∈ P → a * b ∈ P) {M : ℝ} (hM : 0 ≤ M)
    (hAI : HasBoundedRightApproximation P M) :
    Continuous (fun x : P => θ x.val) :=
  continuous_restriction_of_nullSequences_factor θ P hP
    (cohen_factor_tendsto_zero P hclosed hleft hM hAI)

/-- Ogden's final argument for a closed codimension-one ideal, separated
from the specific ordinal-space constructions. -/
theorem continuous_hom_of_codimensionOne_boundedRightApproximation
    (θ : B →ₙₐ[𝕜] A) (χ : B →L[𝕜] 𝕜) (e : B) (he : χ e = 1)
    (hP : LinearMap.ker χ ≤ continuityIdeal θ)
    (hleft : ∀ a b : B, b ∈ LinearMap.ker χ → a * b ∈ LinearMap.ker χ)
    {M : ℝ} (hM : 0 ≤ M) (hAI : HasBoundedRightApproximation (LinearMap.ker χ) M) :
    Continuous θ := by
  let f : B →ₗ[𝕜] A := {
    toFun := θ
    map_add' := θ.map_add
    map_smul' := θ.map_smul
  }
  apply continuous_of_continuous_on_codimensionOne_kernel f χ e he
  exact continuous_restriction_of_boundedRightApproximation θ (LinearMap.ker χ) hP
    (isClosed_singleton.preimage χ.continuous) hleft hM hAI

end JLMS
