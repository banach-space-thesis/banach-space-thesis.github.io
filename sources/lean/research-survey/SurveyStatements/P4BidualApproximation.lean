import SurveyStatements.P4Approximation
import SurveyStatements.P4Gantmacher

/-!
# Approximations on the bidual and weak approximations on the adjoint

The paper uses weak compactness to place `T**(X**)` inside the canonical
copy of `Y`. Strong approximations to the identity of `Y` therefore give
norm approximations on this bidual image. This supplies the second convergence
in `p5:prop:two-sided-approximants` and the weak adjoint convergence before
tail convexification.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024

open Filter Topology

namespace SurveyStatements.P4

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Strong identity approximants on the range space converge in norm after
composition with a weakly compact map's second adjoint. -/
theorem bidual_approximants_tendsto
    (P : ℕ → Y →L[𝕜] Y)
    (hP : ∀ y : Y, Tendsto (fun n => P n y) atTop (𝓝 y))
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T)
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    Tendsto (fun n => bidualMap ((P n).comp T) ξ) atTop (𝓝 (bidualMap T ξ)) := by
  obtain ⟨y, hy⟩ := hT.bidual_mem_image ξ
  have he : ∀ n, bidualMap ((P n).comp T) ξ =
      NormedSpace.inclusionInDoubleDual 𝕜 Y (P n y) := by
    intro n
    rw [bidualMap_comp, ContinuousLinearMap.comp_apply, ← hy]
    exact bidualMap_inclusion (P n) y
  simp_rw [he]
  rw [← hy]
  exact (NormedSpace.inclusionInDoubleDual 𝕜 Y).continuous.tendsto y |>.comp (hP y)

/-- The adjoints of these approximants converge weakly in the strong dual.
The weak topology here tests every member of the continuous bidual. -/
theorem adjoint_approximants_tendsto_weak
    (P : ℕ → Y →L[𝕜] Y)
    (hP : ∀ y : Y, Tendsto (fun n => P n y) atTop (𝓝 y))
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) (φ : StrongDual 𝕜 Y) :
    Tendsto (fun n => toWeakSpace 𝕜 (StrongDual 𝕜 X) (banachAdjoint ((P n).comp T) φ))
      atTop (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 X) (banachAdjoint T φ))) := by
  have hinj : Function.Injective (topDualPairing 𝕜 (StrongDual 𝕜 X)).flip := by
    intro f g hfg
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hfg (NormedSpace.inclusionInDoubleDual 𝕜 X x)
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro ξ
  exact ((ContinuousLinearMap.apply 𝕜 𝕜 φ).continuous.tendsto (bidualMap T ξ)).comp
    (bidual_approximants_tendsto P hP T hT ξ)

/-- Actual bounded finite-rank approximants of a weakly compact map into a
separable BAP space, with bidual norm convergence and adjoint weak convergence.
Upgrading the last convergence to norm convergence requires the paper's
additional Baire-one and tail-convexification arguments. -/
theorem exists_finiteRank_bidual_and_weak_adjoint_approximants
    [TopologicalSpace.SeparableSpace Y]
    (hBAP : HasBoundedApproximationProperty 𝕜 Y)
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompactOperator 𝕜 T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A : ℕ → X →L[𝕜] Y,
      (∀ n, HasFiniteRank 𝕜 (A n)) ∧ (∀ n, ‖A n‖ ≤ C) ∧
      (∀ x : X, Tendsto (fun n => A n x) atTop (𝓝 (T x))) ∧
      (∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
        Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ))) ∧
      ∀ φ : StrongDual 𝕜 Y,
        Tendsto (fun n => toWeakSpace 𝕜 (StrongDual 𝕜 X) (banachAdjoint (A n) φ))
          atTop (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 X) (banachAdjoint T φ))) := by
  obtain ⟨C, hC, P, hfinite, hnorm, hstrong⟩ := hBAP.sequential
  refine ⟨C * ‖T‖, mul_nonneg hC (norm_nonneg _), fun n => (P n).comp T,
    fun n => (hfinite n).comp_right T, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ((P n).opNorm_comp_le T).trans
      (mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _))
  · intro x
    exact hstrong (T x)
  · exact bidual_approximants_tendsto P hstrong T hT
  · exact adjoint_approximants_tendsto_weak P hstrong T hT

end SurveyStatements.P4
