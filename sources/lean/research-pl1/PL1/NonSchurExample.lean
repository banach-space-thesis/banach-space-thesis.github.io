import PL1.ConcreteResolvents
import PL1.RademacherEmbedding
import PL1.EigenvectorEmbedding
import PL1.Ell2Schur
import PL1.DunfordPettis

/-!
# The concrete non-Schur projection on the countable sum of Haar L1

Constant coordinate rates make the entire closed first Walsh chaos a common
resolvent eigenspace. The explicit Rademacher embedding therefore lifts to the
intrinsic graph and the actual range of the constructed projection.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace PL1.Noise

open Walsh EigenvectorEmbedding ResolventEstimates

variable (𝕜 : Type*) [RCLike 𝕜]

theorem constantRates_firstChaos_eigen (n : ℕ) (a : Ell2 𝕜) :
    (dyadicSystem 𝕜 constantRates).operator n (rademacherL1 𝕜 a) =
      (((1 + (dyadicRatio ^ 2) ^ n)⁻¹ : ℝ) : 𝕜) • rademacherL1 𝕜 a := by
  apply rademacherL1_eigen
  intro j
  change resolventL1 𝕜 constantRates (dyadicTime n) (scalarCharacterLp 𝕜 1 {j}) = _
  simp [rateSum, constantRates, dyadicTime]

theorem constantRates_intrinsic_contains_ell2 :
    ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (dyadicSystem 𝕜 constantRates).IntrinsicSpace :=
  containsIsomorphicCopy_of_first_chaos (dyadicSystem 𝕜 constantRates).operator
    (rademacherL1 𝕜) (constantRates_firstChaos_eigen 𝕜) 16 (rademacherL1_lower 𝕜)

theorem constantRates_projection_range_contains_ell2 :
    ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (projection 𝕜 constantRates).range := by
  change ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (dyadicSystem 𝕜 constantRates).projection.range
  rw [DyadicSystem.projection_range]
  exact constantRates_intrinsic_contains_ell2 𝕜

theorem constantRates_projection_range_not_schur :
    ¬ HasSchurProperty 𝕜 (projection 𝕜 constantRates).range :=
  not_hasSchurProperty_of_contains_ell2 𝕜 (constantRates_projection_range_contains_ell2 𝕜)

theorem constantRates_projection_range_infiniteDimensional :
    ¬ FiniteDimensional 𝕜 (projection 𝕜 constantRates).range := by
  intro h
  exact constantRates_projection_range_not_schur 𝕜 hasSchurProperty_of_finiteDimensional

/-- The constructed constant-rate projection has the quantitative operator
bound and its actual closed range contains ell2 and fails the Schur property. -/
theorem constantRates_projection_spec :
    IsProjection (projection 𝕜 constantRates) ∧
      ‖projection 𝕜 constantRates‖ ≤ projectionBound ∧
      IsClosed ((projection 𝕜 constantRates).range : Set (L1Sum (Lp 𝕜 1 haar))) ∧
      ¬ FiniteDimensional 𝕜 (projection 𝕜 constantRates).range ∧
      ContainsIsomorphicCopy 𝕜 (Ell2 𝕜) (projection 𝕜 constantRates).range ∧
      ¬ HasSchurProperty 𝕜 (projection 𝕜 constantRates).range :=
  ⟨projection_isProjection 𝕜 constantRates, norm_projection_le 𝕜 constantRates,
    projection_range_isClosed 𝕜 constantRates, constantRates_projection_range_infiniteDimensional 𝕜,
    constantRates_projection_range_contains_ell2 𝕜, constantRates_projection_range_not_schur 𝕜⟩

theorem linearIndependent_rademacherL1 :
    LinearIndependent 𝕜 (fun j : ℕ => scalarCharacterLp 𝕜 1 {j}) := by
  have hinj : Function.Injective (l2ToL1 (𝕜 := 𝕜)) := by
    intro f g h
    apply Lp.ext
    exact (ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) f).symm.trans
      ((by rw [h] : l2ToL1 f =ᵐ[haar] l2ToL1 g).trans
        (ProbabilityLp.coeFn_inclusion haar 1 2 (by norm_num) g))
  have hi := (orthonormal_rademacherL2 𝕜).linearIndependent.map' l2ToL1.toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
    l2ToL1_scalarCharacter] using hi

theorem linearIndependent_resolvent_rademacher (rates : ℕ → ℝ≥0) :
    LinearIndependent 𝕜 (fun j : ℕ =>
      resolventL1 𝕜 rates (dyadicTime 0) (scalarCharacterLp 𝕜 1 {j})) := by
  have hc (j : ℕ) : (((1 + (rates j : ℝ))⁻¹ : ℝ) : 𝕜) ≠ 0 := by
    exact_mod_cast inv_ne_zero (ne_of_gt (by positivity : 0 < 1 + (rates j : ℝ)))
  have hi := (linearIndependent_rademacherL1 𝕜).units_smul
    (fun j => Units.mk0 (((1 + (rates j : ℝ))⁻¹ : ℝ) : 𝕜) (hc j))
  change LinearIndependent 𝕜 (fun j =>
    (((1 + (rates j : ℝ))⁻¹ : ℝ) : 𝕜) • scalarCharacterLp 𝕜 1 {j}) at hi
  simpa only [resolventL1_scalarCharacter, dyadicTime, pow_zero,
    rateSum, Finset.sum_singleton, one_mul] using hi

set_option backward.isDefEq.respectTransparency false in
/-- Every choice of nonnegative rates gives an infinite-dimensional intrinsic
space: its zeroth reconstruction column retains independent Rademacher vectors. -/
theorem intrinsic_infiniteDimensional (rates : ℕ → ℝ≥0) :
    ¬ FiniteDimensional 𝕜 (dyadicSystem 𝕜 rates).IntrinsicSpace := by
  intro hfinite
  let v : ℕ → (dyadicSystem 𝕜 rates).IntrinsicSpace := fun j =>
    (dyadicSystem 𝕜 rates).column 0 (scalarCharacterLp 𝕜 1 {j})
  have hi : LinearIndependent 𝕜 v := by
    apply LinearIndependent.of_comp
      (IntrinsicGraph.evalZero (dyadicSystem 𝕜 rates).analysis).toLinearMap
    change LinearIndependent 𝕜 (fun j =>
      IntrinsicGraph.evalZero (dyadicSystem 𝕜 rates).analysis
        ((dyadicSystem 𝕜 rates).column 0 (scalarCharacterLp 𝕜 1 {j})))
    simp only [DyadicSystem.evalZero_column]
    exact linearIndependent_resolvent_rademacher 𝕜 rates
  exact Module.Finite.not_linearIndependent_of_infinite v hi

theorem projection_range_infiniteDimensional (rates : ℕ → ℝ≥0) :
    ¬ FiniteDimensional 𝕜 (projection 𝕜 rates).range := by
  change ¬ FiniteDimensional 𝕜 (dyadicSystem 𝕜 rates).projection.range
  rw [DyadicSystem.projection_range]
  exact intrinsic_infiniteDimensional 𝕜 rates

end PL1.Noise
