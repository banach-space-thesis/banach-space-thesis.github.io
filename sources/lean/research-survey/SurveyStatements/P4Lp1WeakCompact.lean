import SurveyStatements.P4Lp1Pairing

/-! A bounded family of weakly compact maps whose adjoints converge strongly
has a weakly compact sum operator on the actual absolutely summable sum.
The argument uses density of finite evaluations in the convergent-sequence dual. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 2048

open Set Filter Topology
open scoped OnePoint ENNReal

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem lp1Sum_weaklyCompact_of_adjoint_tendsto
    (A : ℕ → X →L[𝕜] E) (T : X →L[𝕜] E)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C)
    (hweak : ∀ n, IsWeaklyCompactOperator 𝕜 (A n))
    (hT : IsWeaklyCompactOperator 𝕜 T)
    (hpoint : ∀ φ : StrongDual 𝕜 E, Tendsto (fun n => banachAdjoint (A n) φ)
      atTop (𝓝 (banachAdjoint T φ)))
    (hdense : Dense (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X) |
        ∃ p : OnePoint ℕ, ∃ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
          Φ = ξ.comp (ContinuousMap.evalCLM 𝕜 p)} :
        Set (StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X)))) :
    IsWeaklyCompactOperator 𝕜 (lp1Sum A hC hA) := by
  let H := convergentLift (fun n => banachAdjoint (A n)) (banachAdjoint T) hpoint
    (fun n => (convergent_norm_banachAdjoint_le (A n)).trans (hA n))
  have hclosed : IsClosed ((banachAdjoint H) ⁻¹' (bidualImage 𝕜 E : Set _)) :=
    (isClosed_bidualImage (𝕜 := 𝕜) (F := E)).preimage (banachAdjoint H).continuous
  have hspan : (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X) |
        ∃ p : OnePoint ℕ, ∃ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
          Φ = ξ.comp (ContinuousMap.evalCLM 𝕜 p)} :
      Set (StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X))) ⊆
      (banachAdjoint H) ⁻¹' (bidualImage 𝕜 E : Set _) := by
    have hle : Submodule.span 𝕜
        {Φ : StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X) |
          ∃ p : OnePoint ℕ, ∃ ξ : StrongDual 𝕜 (StrongDual 𝕜 X),
            Φ = ξ.comp (ContinuousMap.evalCLM 𝕜 p)} ≤
        (bidualImage 𝕜 E).comap (banachAdjoint H).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro Φ ⟨p, ξ, rfl⟩
      cases p using OnePoint.rec with
      | infty =>
          change bidualMap T ξ ∈ bidualImage 𝕜 E
          exact hT.bidual_mem_image ξ
      | coe n =>
          change bidualMap (A n) ξ ∈ bidualImage 𝕜 E
          exact (hweak n).bidual_mem_image ξ
    exact fun Φ hΦ => hle hΦ
  have hH (Φ : StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X)) :
      banachAdjoint H Φ ∈ bidualImage 𝕜 E :=
    closure_minimal hspan hclosed (hdense Φ)
  apply weaklyCompact_of_bidual_mem_image
  intro ξ
  let Ψ : StrongDual 𝕜 C(OnePoint ℕ, StrongDual 𝕜 X) :=
    ξ.comp (lp1Pairing (𝕜 := 𝕜) (X := X))
  obtain ⟨y, hy⟩ := hH Ψ
  refine ⟨y, ?_⟩
  rw [show bidualMap (lp1Sum A hC hA) ξ =
    banachAdjoint H Ψ from ?_]
  · exact hy
  · apply ContinuousLinearMap.ext
    intro φ
    change ξ (banachAdjoint (lp1Sum A hC hA) φ) = ξ (lp1Pairing (H φ))
    rw [lp1Sum_adjoint_factorization A T hC hA hpoint]
    rfl

end SurveyStatements.P4
