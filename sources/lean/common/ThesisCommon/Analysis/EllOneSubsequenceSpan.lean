import ThesisCommon.Analysis.SchauderOperators
import ThesisCommon.Analysis.LpSchauderBasis
import Mathlib.Analysis.Normed.Operator.Banach

/-! A finite ℓ₁ lower estimate on actual basis vectors yields an actual
bounded isomorphism from ℓ₁ onto their closed span. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ellOne_norm_finite_scalar_units (F : Finset ℕ) (a : ℕ → 𝕜) :
    ‖∑ n ∈ F, a n • (lp.single 1 n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) 1)‖ =
      ∑ n ∈ F, ‖a n‖ := by
  simpa only [← lp.single_smul, smul_eq_mul, mul_one, ENNReal.toReal_one, Real.rpow_one]
    using lp.norm_sum_single (E := fun _ : ℕ => 𝕜)
      (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal) a F

namespace NormalizedSchauderBasis
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem subsequenceSpan_equiv_ellOne_of_lower (f : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ (F : Finset ℕ) (a : ℕ → 𝕜),
      c * ∑ n ∈ F, ‖a n‖ ≤ ‖∑ n ∈ F, a n • b.vector (f n)‖) :
    Nonempty (b.subsequenceSpan f ≃L[𝕜] lp (fun _ : ℕ => 𝕜) 1) := by
  let β := scalarLpSchauderBasis (𝕜 := 𝕜) 1 (by simp)
  obtain ⟨B, _, hB⟩ := β.exists_operator (fun n => b.vector (f n)) zero_le_one (by
    intro F a
    calc
      _ ≤ ∑ n ∈ F, ‖a n • b.vector (f n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ F, ‖a n‖ := by simp only [norm_smul, b.norm_vector, mul_one]
      _ = 1 * ‖∑ n ∈ F, a n • β.vector n‖ := by
        rw [one_mul]
        exact (ellOne_norm_finite_scalar_units F a).symm)
  have hbound (x : lp (fun _ : ℕ => 𝕜) 1) : c * ‖x‖ ≤ ‖B x‖ := by
    apply le_of_tendsto_of_tendsto ((β.expansion x).norm.const_mul c)
      (((B.continuous.tendsto x).comp (β.expansion x)).norm)
    apply Filter.Eventually.of_forall
    intro N
    simp only [Function.comp_apply, map_sum, map_smul, hB]
    change c * ‖∑ n ∈ Finset.range N,
      x n • (lp.single 1 n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) 1)‖ ≤ _
    rw [ellOne_norm_finite_scalar_units]
    exact hlower _ _
  have hanti : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ B := by
    apply B.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ c⁻¹ * ‖B x‖
    calc
      _ = c⁻¹ * (c * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hc.le)
  have hclosed : IsClosed (Set.range B) := hanti.isClosed_range B.uniformContinuous
  have hrange : LinearMap.range B.toLinearMap = b.subsequenceSpan f := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have ht := (B.continuous.tendsto x).comp (β.expansion x)
      apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
      apply Filter.Eventually.of_forall
      intro N
      change B (∑ n ∈ Finset.range N, β.coord n x • β.vector n) ∈ b.subsequenceSpan f
      rw [map_sum]
      apply Submodule.sum_mem
      intro n _
      rw [map_smul, hB]
      apply Submodule.smul_mem
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
    · apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro y ⟨n, rfl⟩
        exact ⟨β.vector n, hB n⟩
      · exact hclosed
  exact ⟨((B.equivRange hanti.injective hclosed).trans
    (LinearIsometryEquiv.ofEq _ _ hrange).toContinuousLinearEquiv).symm⟩

end NormalizedSchauderBasis
end ThesisCommon
