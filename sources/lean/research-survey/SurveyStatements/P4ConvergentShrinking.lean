import SurveyStatements.P4ConvergentBidual
import SurveyStatements.P4StrongConvergenceDense

/-! Adjoint norm convergence gives the source's genuine shrinking estimate
for freeze projections, first on evaluation functionals and then by density. -/

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
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

lemma norm_banachAdjoint_apply_le (T : X →L[𝕜] Y) (φ : StrongDual 𝕜 Y) :
    ‖banachAdjoint T φ‖ ≤ ‖T‖ * ‖φ‖ := by
  change ‖φ.comp T‖ ≤ ‖T‖ * ‖φ‖
  simpa only [mul_comm] using φ.opNorm_comp_le T

lemma convergent_norm_banachAdjoint_le (T : X →L[𝕜] Y) : ‖banachAdjoint T‖ ≤ ‖T‖ :=
  (banachAdjoint T).opNorm_le_bound T.opNorm_nonneg (norm_banachAdjoint_apply_le T)

theorem convergentLift_shrinking
    (A : ℕ → X →L[𝕜] Y) (T : X →L[𝕜] Y)
    (hpoint : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (T x)))
    {C : ℝ} (hbound : ∀ n, ‖A n‖ ≤ C)
    (hadjoint : ∀ φ : StrongDual 𝕜 Y,
      Tendsto (fun n => banachAdjoint (A n) φ) atTop (𝓝 (banachAdjoint T φ)))
    (hdense : Dense (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ, ∃ φ : StrongDual 𝕜 Y,
        Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)} : Set (StrongDual 𝕜 C(OnePoint ℕ, Y)))) :
    ∀ Φ : StrongDual 𝕜 C(OnePoint ℕ, Y), Tendsto
      (fun n => banachAdjoint (convergentLift A T hpoint hbound)
        (banachAdjoint (convergentFreeze n) Φ)) atTop
      (𝓝 (banachAdjoint (convergentLift A T hpoint hbound) Φ)) := by
  let R := convergentLift A T hpoint hbound
  let S : ℕ → StrongDual 𝕜 C(OnePoint ℕ, Y) →L[𝕜] StrongDual 𝕜 X :=
    fun n => (banachAdjoint R).comp (banachAdjoint (convergentFreeze n))
  have hS (n : ℕ) : ‖S n‖ ≤ ‖banachAdjoint R‖ := by
    have hQ : ‖banachAdjoint (convergentFreeze (𝕜 := 𝕜) (Y := Y) n)‖ ≤ 1 :=
      (convergent_norm_banachAdjoint_le _).trans (norm_convergentFreeze_le_one n)
    exact ((banachAdjoint R).opNorm_comp_le _).trans
      ((mul_le_mul_of_nonneg_left hQ (banachAdjoint R).opNorm_nonneg).trans_eq (mul_one _))
  apply strong_tendsto_of_dense_span S (banachAdjoint R) ‖banachAdjoint R‖
    (banachAdjoint R).opNorm_nonneg hS _ hdense
  rintro Φ ⟨p, φ, rfl⟩
  cases p using OnePoint.rec with
  | infty =>
      change Tendsto (fun n => banachAdjoint (A n) φ) atTop (𝓝 (banachAdjoint T φ))
      exact hadjoint φ
  | coe k =>
      apply tendsto_const_nhds.congr'
      apply (eventually_ge_atTop k).mono
      intro n hn
      apply ContinuousLinearMap.ext
      intro x
      change φ (R x (k : OnePoint ℕ)) = φ (R x ((min n k : ℕ) : OnePoint ℕ))
      rw [min_eq_right hn]

end SurveyStatements.P4
