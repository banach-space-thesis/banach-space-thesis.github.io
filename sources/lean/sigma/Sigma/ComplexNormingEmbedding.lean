import Sigma.ComplexDesiredProperty
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
namespace SigmaNonprimarity
open scoped BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def complexNormingCoordinates (e : ℕ → E →L[ℂ] ℂ) (he : ∀ n, ‖e n‖ ≤ 1) :
    E →L[ℂ] (ℕ →ᵇ ℂ) :=
  ({ toFun := fun x => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
       (fun n => e n x) ‖x‖ (fun n => ((e n).le_opNorm x).trans
         (by simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg x)))
     map_add' := by intro x y; ext n; exact (e n).map_add x y
     map_smul' := by intro r x; ext n; exact (e n).map_smul r x } : E →ₗ[ℂ] (ℕ →ᵇ ℂ)).mkContinuous
    1 (by
      intro x
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
      intro n
      exact ((e n).le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg x)))

@[simp] theorem complexNormingCoordinates_apply (e : ℕ → E →L[ℂ] ℂ) (he : ∀ n, ‖e n‖ ≤ 1)
    (x : E) (n : ℕ) : complexNormingCoordinates e he x n = e n x := rfl

theorem complexNormingCoordinates_lower {e : ℕ → E →L[ℂ] ℂ} {c : ℝ} (he : IsComplexCNorming e c)
    (x : E) : c * ‖x‖ ≤ ‖complexNormingCoordinates e he.2.2.1 x‖ := by
  refine (he.2.2.2 x).trans (ciSup_le fun n => ?_)
  exact (complexNormingCoordinates e he.2.2.1 x).norm_coe_le_norm n

theorem complexNormingCoordinates_antilipschitz {e : ℕ → E →L[ℂ] ℂ} {c : ℝ}
    (he : IsComplexCNorming e c) :
    AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr he.1.le⟩ (complexNormingCoordinates e he.2.2.1) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  change ‖x‖ ≤ c⁻¹ * ‖complexNormingCoordinates e he.2.2.1 x‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ he.1).mpr (by simpa only [mul_comm] using complexNormingCoordinates_lower he x)

def complexNormingCoordinatesEquiv [CompleteSpace E] {e : ℕ → E →L[ℂ] ℂ} {c : ℝ}
    (he : IsComplexCNorming e c) :
    E ≃L[ℂ] LinearMap.range (complexNormingCoordinates e he.2.2.1) :=
  (complexNormingCoordinates e he.2.2.1).equivRange (complexNormingCoordinates_antilipschitz he).injective
    ((complexNormingCoordinates_antilipschitz he).isClosed_range
      (complexNormingCoordinates e he.2.2.1).uniformContinuous)

end SigmaNonprimarity


