import SurveyStatements.P5Support.HaarSignSecondMoment

/-! The genuine two-family sign averaging identity used for potential
shadow orbits. The readers and inputs are arbitrary continuous linear
maps and vectors, so actual mixed-space tensor/readers can instantiate it. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5Support SurveyStatements.P5Support.Grothendieck
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem map_signedValue (A : E →L[𝕜] F) (b : Bool) (x : E) :
    A (signedValue b x) = signedValue b (A x) := by
  cases b <;> simp [signedValue]

theorem signed_reader_input_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → E →L[𝕜] F) (x : ι → E) :
    (∑ θ : ι → Bool, (∑ i, signedValue (θ i) (A i))
      (∑ j, signedValue (θ j) (x j))) =
        Fintype.card (ι → Bool) • ∑ i, A i (x i) := by
  have happly (θ : ι → Bool) :
      (∑ i, signedValue (θ i) (A i)) (∑ j, signedValue (θ j) (x j)) =
        ∑ i, signedValue (θ i) (A i (∑ j, signedValue (θ j) (x j))) := by
    rw [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    cases θ i <;> simp [signedValue]
  simp_rw [happly]
  rw [Finset.sum_comm]
  have hterm (i : ι) :
      (∑ θ : ι → Bool, signedValue (θ i) (A i (∑ j, signedValue (θ j) (x j)))) =
        Fintype.card (ι → Bool) • A i (x i) := by
    have h := congrArg (A i) (signed_sum_orthogonality x i)
    simpa only [map_sum, map_signedValue, map_nsmul] using h
  simp_rw [hterm]
  exact Finset.smul_sum.symm

theorem norm_diagonal_sum_le_signed_reader_input_average
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → E →L[𝕜] F) (x : ι → E) :
    ‖∑ i, A i (x i)‖ ≤
      (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ θ : ι → Bool, ‖(∑ i, signedValue (θ i) (A i))
          (∑ j, signedValue (θ j) (x j))‖ := by
  have hc : 0 < (Fintype.card (ι → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h := norm_sum_le (Finset.univ : Finset (ι → Bool))
    (fun θ => (∑ i, signedValue (θ i) (A i)) (∑ j, signedValue (θ j) (x j)))
  rw [signed_reader_input_sum] at h
  have hn : ‖Fintype.card (ι → Bool) • ∑ i, A i (x i)‖ =
      (Fintype.card (ι → Bool) : ℝ) * ‖∑ i, A i (x i)‖ := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, norm_smul]
    simp
  rw [hn] at h
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h)

end SurveyStatements.P5OperatorReduction
