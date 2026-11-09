import NonCalkinAlgebra.ApproximateSurjection
import SurveyStatements.P2EllOneSynthesis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Normed.Group.Quotient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
open TopologicalSpace
open scoped ENNReal
universe v

/-- The fixed, concrete scalar ℓ¹ space on the natural numbers. -/
abbrev ComplexEllOne := lp (fun _ : ℕ => ℂ) 1

variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X] [SeparableSpace X]

/-- Every separable complex Banach space, in any universe and including the
zero space, is the range of a bounded linear map from the same concrete ℓ¹. -/
theorem exists_surjective_ellOne_map :
    ∃ T : ComplexEllOne →L[ℂ] X, Function.Surjective T := by
  classical
  let B := Metric.closedBall (0 : X) 1
  letI : Nonempty B := ⟨⟨0, by simp [B]⟩⟩
  let d : ℕ → B := denseSeq B
  let x : ℕ → X := fun n => (d n : X)
  have hx : ∀ n, ‖x n‖ ≤ 1 := by
    intro n
    simpa only [B, x, Metric.mem_closedBall, dist_zero_right] using (d n).property
  let T : ComplexEllOne →L[ℂ] X :=
    SurveyStatements.P2.ellOneSynthesis x 1 (by norm_num) hx
  refine ⟨T, surjective_of_approximate_preimage T 1 (by norm_num) ?_⟩
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  let z : ℂ := (‖y‖ : ℂ)
  have hznorm : ‖z‖ = ‖y‖ := by
    simp [z, Complex.norm_real]
  have hnormpos : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hz : z ≠ 0 := by
    intro hz
    exact hnormpos (hznorm.symm.trans (by simp [hz]))
  have hvnorm : ‖z⁻¹ • y‖ = 1 := by
    rw [norm_smul, norm_inv, hznorm, inv_mul_cancel₀ hnormpos]
  let b : B := ⟨z⁻¹ • y, by simp [B, Metric.mem_closedBall, dist_zero_right, hvnorm]⟩
  obtain ⟨n, hn⟩ := (denseRange_denseSeq B).exists_dist_lt b
    (by norm_num : (0 : ℝ) < 1 / 2)
  have herror : ‖z⁻¹ • y - x n‖ ≤ (1 / 2 : ℝ) := by
    exact (by simpa only [Subtype.dist_eq, dist_eq_norm] using hn :
      ‖z⁻¹ • y - x n‖ < (1 / 2 : ℝ)).le
  refine ⟨lp.single 1 n z, ?_, ?_⟩
  · change ‖y - SurveyStatements.P2.ellOneSynthesis x 1 (by norm_num) hx
      (lp.single 1 n z)‖ ≤ _
    rw [SurveyStatements.P2.ellOneSynthesis_single]
    have heq : y - z • x n = z • (z⁻¹ • y - x n) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hz, one_smul]
    rw [heq, norm_smul, hznorm]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left herror (norm_nonneg y)
  · rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), hznorm, one_mul]

/-- All canonical models live in Type 0, even when the space being modelled
belongs to a larger universe. -/
def ClosedEllOneSubspace :=
  {N : Submodule ℂ ComplexEllOne // IsClosed (N : Set ComplexEllOne)}

namespace ClosedEllOneSubspace
instance (N : ClosedEllOneSubspace) : IsClosed (N.val : Set ComplexEllOne) := N.property

abbrev Quotient (N : ClosedEllOneSubspace) := ComplexEllOne ⧸ N.val
end ClosedEllOneSubspace

/-- The concrete quotient-model theorem needed for counting separable
Banach-space isomorphism classes. Equivalence means bounded linear with
bounded inverse; no isometry or choice of a new norm is asserted. -/
theorem exists_ellOne_quotient_equiv :
    ∃ N : ClosedEllOneSubspace, Nonempty (N.Quotient ≃L[ℂ] X) := by
  obtain ⟨T, hT⟩ := exists_surjective_ellOne_map X
  let N : ClosedEllOneSubspace :=
    ⟨LinearMap.ker T.toLinearMap, ContinuousLinearMap.isClosed_ker T⟩
  letI : IsClosed (N.val : Set ComplexEllOne) := N.property
  letI : NormedAddCommGroup N.Quotient := inferInstance
  letI : NormedSpace ℂ N.Quotient := inferInstance
  letI : CompleteSpace N.Quotient := inferInstance
  let e : N.Quotient ≃ₗ[ℂ] X := T.toLinearMap.quotKerEquivOfSurjective hT
  have he : Continuous e := by
    apply (N.val.isOpenQuotientMap_mkQ.continuous_comp_iff).mp
    change Continuous T
    exact T.continuous
  let e' : N.Quotient ≃L[ℂ] X :=
    { e with continuous_toFun := he
             continuous_invFun := LinearEquiv.continuous_symm e he }
  exact ⟨N, ⟨e'⟩⟩

end NonCalkinAlgebra
