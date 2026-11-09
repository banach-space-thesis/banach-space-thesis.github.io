import SurveyStatements.P1C0Embedding
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Extending actual finite c0 coefficient estimates to a continuous linear
embedding of the complete complex c0 space. This is used after constant
coefficient suppression supplies finite upper bounds. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter Topology

namespace SurveyStatements.P1

def c0TruncateFinsupp (v : ComplexC0) (N : ℕ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (Finset.range N) (fun i => if i < N then v i else 0) (by
    intro i hi
    by_contra h
    have hnot : ¬ i < N := by simpa only [Finset.mem_range] using h
    exact hi (if_neg hnot))

@[simp] theorem c0TruncateFinsupp_apply (v : ComplexC0) (N i : ℕ) :
    c0TruncateFinsupp v N i = if i < N then v i else 0 := rfl

theorem c0FinsuppLinear_dense : Dense (LinearMap.range c0FinsuppLinear : Set ComplexC0) := by
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n => ‖v n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Filter.cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero] using
      (zero_at_infty v).norm
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by linarith : 0 < ε / 2)))
  let w := c0Finsupp (c0TruncateFinsupp v N)
  refine ⟨w, ⟨c0TruncateFinsupp v N, rfl⟩, ?_⟩
  have hnorm : ‖v - w‖ ≤ ε / 2 := by
    change ‖(v - w).toBCF‖ ≤ ε / 2
    apply (BoundedContinuousFunction.norm_le (by linarith : 0 ≤ ε / 2)).mpr
    intro i
    change ‖v i - (if i < N then v i else 0)‖ ≤ ε / 2
    by_cases hi : i < N
    · simp only [if_pos hi, sub_self, norm_zero]
      linarith
    · simpa only [if_neg hi, sub_zero] using (hN i (Nat.le_of_not_gt hi)).le
  have hdist : dist v w ≤ ε / 2 := by simpa only [dist_eq_norm] using hnorm
  exact hdist.trans_lt (by linarith : ε / 2 < ε)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_c0_embedding_of_finite_coefficient_bounds
    (u : ℕ → X) {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U)
    (hlower : ∀ b : ℕ →₀ ℂ,
      L * ‖c0Finsupp b‖ ≤ ‖Finsupp.linearCombination ℂ u b‖)
    (hupper : ∀ b : ℕ →₀ ℂ,
      ‖Finsupp.linearCombination ℂ u b‖ ≤ U * ‖c0Finsupp b‖) :
    ∃ T : ComplexC0 →L[ℂ] X, ‖T‖ ≤ U ∧
      (∀ b : ℕ →₀ ℂ, T (c0Finsupp b) = Finsupp.linearCombination ℂ u b) ∧
      ∀ v : ComplexC0, L * ‖v‖ ≤ ‖T v‖ := by
  let S := LinearMap.range c0FinsuppLinear
  letI : NormedAddCommGroup S := inferInstance
  letI : NormedSpace ℂ S := inferInstance
  let Q := LinearEquiv.ofInjective c0FinsuppLinear c0FinsuppLinear_injective
  let J : S →ₗ[ℂ] X := (Finsupp.linearCombination ℂ u).comp Q.symm.toLinearMap
  have hQ (x : S) : c0Finsupp (Q.symm x) = (x : ComplexC0) := by
    exact congrArg Subtype.val (Q.apply_symm_apply x)
  have hJ (x : S) : ‖J x‖ ≤ U * ‖x‖ := by
    have h := hupper (Q.symm x)
    rw [hQ] at h
    exact h
  let JC : S →L[ℂ] X := LinearMap.mkContinuous J U hJ
  have hDense : DenseRange S.subtypeL := by
    change Dense (Set.range (fun x : S => (x : ComplexC0)))
    have hRange : Set.range (fun x : S => (x : ComplexC0)) = (S : Set ComplexC0) := by
      ext x
      simp
    rw [hRange]
    exact c0FinsuppLinear_dense
  let T : ComplexC0 →L[ℂ] X := JC.extend S.subtypeL hDense
    isometry_subtype_coe.isUniformInducing
  have hext (x : S) : T (x : ComplexC0) = J x :=
    ContinuousLinearMap.extend_eq JC S.subtypeL hDense isometry_subtype_coe.isUniformInducing x
  have hTnorm : ‖T‖ ≤ U := by
    apply ContinuousLinearMap.opNorm_le_bound T hU
    intro v
    refine hDense.induction_on v (isClosed_le T.continuous.norm
      (continuous_const.mul continuous_norm)) ?_
    intro x
    change ‖T (x : ComplexC0)‖ ≤ U * ‖(x : ComplexC0)‖
    rw [hext]
    exact hJ x
  have hTlower (v : ComplexC0) : L * ‖v‖ ≤ ‖T v‖ := by
    refine hDense.induction_on v (isClosed_le (continuous_const.mul continuous_norm)
      T.continuous.norm) ?_
    intro x
    change L * ‖(x : ComplexC0)‖ ≤ ‖T (x : ComplexC0)‖
    rw [hext]
    have h := hlower (Q.symm x)
    rw [hQ] at h
    exact h
  refine ⟨T, hTnorm, ?_, hTlower⟩
  intro b
  have hQB : Q.symm (Q b) = b := Q.symm_apply_apply b
  have h := hext (Q b)
  change T (c0Finsupp b) = Finsupp.linearCombination ℂ u (Q.symm (Q b)) at h
  rwa [hQB] at h

end SurveyStatements.P1
