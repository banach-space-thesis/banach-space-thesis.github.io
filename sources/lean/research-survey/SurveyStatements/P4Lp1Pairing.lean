import SurveyStatements.P4Lp1Summation
import SurveyStatements.P4ConvergentShrinking

/-! The bounded pairing between a convergent sequence of dual vectors and
an absolutely summable sequence of primal vectors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

open Filter Topology
open scoped ENNReal OnePoint

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def lp1Pairing : C(OnePoint ℕ, StrongDual 𝕜 X) →L[𝕜]
    StrongDual 𝕜 (lp (fun _ : ℕ => X) 1) :=
  ({ toFun := fun (f : C(OnePoint ℕ, StrongDual 𝕜 X)) => lp1Sum (𝕜 := 𝕜) (X := X)
        (E := 𝕜) (fun n : ℕ => f (n : OnePoint ℕ))
        (norm_nonneg f) (fun n => f.norm_coe_le_norm _)
     map_add' := by
       intro f g
       apply ContinuousLinearMap.ext
       intro x
       change (∑' n : ℕ, (f (n : OnePoint ℕ) + g (n : OnePoint ℕ)) (x n)) =
         (∑' n : ℕ, f (n : OnePoint ℕ) (x n)) + ∑' n : ℕ, g (n : OnePoint ℕ) (x n)
       simp only [ContinuousLinearMap.add_apply]
       exact (lp1_operator_summable_norm _ (norm_nonneg f)
         (fun n => f.norm_coe_le_norm _) x).of_norm.tsum_add
         (lp1_operator_summable_norm _ (norm_nonneg g)
           (fun n => g.norm_coe_le_norm _) x).of_norm
     map_smul' := by
       intro a f
       apply ContinuousLinearMap.ext
       intro x
       change (∑' n : ℕ, (a • f (n : OnePoint ℕ)) (x n)) =
         a • ∑' n : ℕ, f (n : OnePoint ℕ) (x n)
       simp only [ContinuousLinearMap.smul_apply]
       exact tsum_const_smul'' a } : C(OnePoint ℕ, StrongDual 𝕜 X) →ₗ[𝕜]
         StrongDual 𝕜 (lp (fun _ : ℕ => X) 1)).mkContinuous 1
    (fun (f : C(OnePoint ℕ, StrongDual 𝕜 X)) => by
      simpa only [one_mul] using (norm_lp1Sum_le
        (fun n : ℕ => f (n : OnePoint ℕ)) (norm_nonneg f) (fun n => f.norm_coe_le_norm _)))

@[simp] lemma lp1Pairing_apply (f : C(OnePoint ℕ, StrongDual 𝕜 X))
    (x : lp (fun _ : ℕ => X) 1) : lp1Pairing f x = ∑' n : ℕ, f (n : OnePoint ℕ) (x n) := rfl

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

lemma lp1Sum_adjoint_factorization (A : ℕ → X →L[𝕜] E) (T : X →L[𝕜] E)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C)
    (hpoint : ∀ φ : StrongDual 𝕜 E, Tendsto (fun n => banachAdjoint (A n) φ)
      atTop (𝓝 (banachAdjoint T φ))) :
    banachAdjoint (lp1Sum A hC hA) = lp1Pairing.comp
      (convergentLift (fun n => banachAdjoint (A n)) (banachAdjoint T) hpoint
        (fun n => (convergent_norm_banachAdjoint_le (A n)).trans (hA n))) := by
  apply ContinuousLinearMap.ext
  intro φ
  apply ContinuousLinearMap.ext
  intro x
  change φ (∑' n, A n (x n)) = ∑' n, φ (A n (x n))
  exact ((lp1_operator_summable_norm A hC hA x).of_norm.hasSum.map φ φ.continuous).tsum_eq.symm

end SurveyStatements.P4
