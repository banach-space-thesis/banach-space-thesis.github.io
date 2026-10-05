import ThesisCommon.Analysis.NormingSequence
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
namespace ThesisCommon
open scoped BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normingCoordinates (e : ℕ → E →L[ℝ] ℝ) (he : ∀ n, ‖e n‖ ≤ 1) :
    E →L[ℝ] (ℕ →ᵇ ℝ) :=
  ({ toFun := fun x => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
       (fun n => e n x) ‖x‖ (fun n => ((e n).le_opNorm x).trans
         (by simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg x)))
     map_add' := by intro x y; ext n; exact (e n).map_add x y
     map_smul' := by intro r x; ext n; exact (e n).map_smul r x } : E →ₗ[ℝ] (ℕ →ᵇ ℝ)).mkContinuous
    1 (by
      intro x
      rw [one_mul]
      apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
      intro n
      exact ((e n).le_opNorm x).trans
        (by simpa using mul_le_mul_of_nonneg_right (he n) (norm_nonneg x)))

@[simp] theorem normingCoordinates_apply (e : ℕ → E →L[ℝ] ℝ) (he : ∀ n, ‖e n‖ ≤ 1)
    (x : E) (n : ℕ) : normingCoordinates e he x n = e n x := rfl

theorem normingCoordinates_lower {e : ℕ → E →L[ℝ] ℝ} {c : ℝ} (he : IsCNorming e c)
    (x : E) : c * ‖x‖ ≤ ‖normingCoordinates e he.2.2.1 x‖ := by
  refine (he.2.2.2 x).trans (ciSup_le fun n => ?_)
  simpa only [Real.norm_eq_abs] using (normingCoordinates e he.2.2.1 x).norm_coe_le_norm n

theorem normingCoordinates_antilipschitz {e : ℕ → E →L[ℝ] ℝ} {c : ℝ}
    (he : IsCNorming e c) :
    AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr he.1.le⟩ (normingCoordinates e he.2.2.1) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  change ‖x‖ ≤ c⁻¹ * ‖normingCoordinates e he.2.2.1 x‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ he.1).mpr (by simpa only [mul_comm] using normingCoordinates_lower he x)

def normingCoordinatesEquiv [CompleteSpace E] {e : ℕ → E →L[ℝ] ℝ} {c : ℝ}
    (he : IsCNorming e c) :
    E ≃L[ℝ] LinearMap.range (normingCoordinates e he.2.2.1) :=
  (normingCoordinates e he.2.2.1).equivRange (normingCoordinates_antilipschitz he).injective
    ((normingCoordinates_antilipschitz he).isClosed_range
      (normingCoordinates e he.2.2.1).uniformContinuous)

end ThesisCommon
