import SurveyStatements.P4ConvergentOperators
import SurveyStatements.P4FiniteRankWeakCompact

/-! The actual norm-convergent bidual coordinates in the sequence bridge. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Set Filter Topology
open scoped OnePoint

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

theorem exists_convergent_bidual_sequence
    (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y) (hA : ∀ n, HasFiniteRank 𝕜 (A n))
    (hbidual : ∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
      Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ)))
    (ξ : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    ∃ z : C(OnePoint ℕ, Y),
      (∀ n : ℕ, NormedSpace.inclusionInDoubleDual 𝕜 Y (z (n : OnePoint ℕ)) = bidualMap (A n) ξ) ∧
      NormedSpace.inclusionInDoubleDual 𝕜 Y (z ∞) = bidualMap T ξ := by
  classical
  have hT := weaklyCompact_of_finiteRank_bidual_tendsto A T hA hbidual
  choose y hy using fun n => (hA n).weaklyCompact.bidual_mem_image ξ
  obtain ⟨t, ht⟩ := hT.bidual_mem_image ξ
  have hseq : Tendsto y atTop (𝓝 t) := by
    apply (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := Y)).isometry.tendsto_nhds_iff.mpr
    change Tendsto (fun n => NormedSpace.inclusionInDoubleDual 𝕜 Y (y n)) atTop
      (𝓝 (NormedSpace.inclusionInDoubleDual 𝕜 Y t))
    simp only [hy, ht]
    exact hbidual ξ
  exact ⟨OnePoint.continuousMapMkNat y t hseq, hy, ht⟩

theorem convergentLift_weaklyCompact_of_dualDensity
    (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y) (hA : ∀ n, HasFiniteRank 𝕜 (A n))
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hbound : ∀ n, ‖A n‖ ≤ C)
    (hbidual : ∀ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
      Tendsto (fun n => bidualMap (A n) ξ) atTop (𝓝 (bidualMap T ξ)))
    (hdense : Dense (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ, ∃ φ : StrongDual 𝕜 Y,
        Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)} : Set (StrongDual 𝕜 C(OnePoint ℕ, Y)))) :
    IsWeaklyCompactOperator 𝕜 (convergentLift A T hpoint hbound) := by
  apply weaklyCompact_of_bidual_mem_image
  intro ξ
  obtain ⟨z, hz, hzInfinity⟩ := exists_convergent_bidual_sequence A T hA hbidual ξ
  refine ⟨z, ?_⟩
  let Jz := NormedSpace.inclusionInDoubleDual 𝕜 C(OnePoint ℕ, Y) z
  let Rξ := bidualMap (convergentLift A T hpoint hbound) ξ
  have htest (p : OnePoint ℕ) (φ : StrongDual 𝕜 Y) :
      Jz (φ.comp (ContinuousMap.evalCLM 𝕜 p)) =
        Rξ (φ.comp (ContinuousMap.evalCLM 𝕜 p)) := by
    cases p using OnePoint.rec with
    | infty =>
        change φ (z ∞) = ξ (φ.comp T)
        exact congrArg (fun η : StrongDual 𝕜 (StrongDual 𝕜 Y) => η φ) hzInfinity
    | coe n =>
        change φ (z (n : OnePoint ℕ)) = ξ (φ.comp (A n))
        exact congrArg (fun η : StrongDual 𝕜 (StrongDual 𝕜 Y) => η φ) (hz n)
  have hspan : (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ, ∃ φ : StrongDual 𝕜 Y,
        Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)} : Set (StrongDual 𝕜 C(OnePoint ℕ, Y))) ⊆
      {Φ | Jz Φ = Rξ Φ} := by
    have hker : Submodule.span 𝕜
        {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ, ∃ φ : StrongDual 𝕜 Y,
          Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)} ≤ LinearMap.ker (Jz - Rξ).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro Φ ⟨p, φ, rfl⟩
      change Jz (φ.comp (ContinuousMap.evalCLM 𝕜 p)) -
        Rξ (φ.comp (ContinuousMap.evalCLM 𝕜 p)) = 0
      exact sub_eq_zero.mpr (htest p φ)
    intro Φ hΦ
    exact sub_eq_zero.mp (hker hΦ)
  apply ContinuousLinearMap.ext
  intro Φ
  exact closure_minimal hspan (isClosed_eq Jz.continuous Rξ.continuous) (hdense Φ)

end SurveyStatements.P4
