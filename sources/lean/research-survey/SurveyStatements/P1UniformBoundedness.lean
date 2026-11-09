import SurveyStatements.P1Transfer
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Baire's uniform boundedness argument on a complete complex normed space. -/

noncomputable section
set_option autoImplicit false
open Set Topology

namespace SurveyStatements.P1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem complex_uniform_boundedness (g : ℕ → E →L[ℂ] ℂ)
    (hpointwise : ∀ x : E, ∃ C : ℝ, ∀ n, ‖g n x‖ ≤ C) :
    ∃ C : ℝ, ∀ n, ‖g n‖ ≤ C := by
  classical
  let S : ℕ → Set E := fun K => {x | ∀ n, ‖g n x‖ ≤ (K : ℝ)}
  have hclosed : ∀ K, IsClosed (S K) := by
    intro K
    have hS : S K = ⋂ n, {x : E | ‖g n x‖ ≤ (K : ℝ)} := by
      ext x
      simp [S]
    rw [hS]
    exact isClosed_iInter fun n => isClosed_le (g n).continuous.norm continuous_const
  have hcover : ⋃ K, S K = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨C, hC⟩ := hpointwise x
    obtain ⟨K, hK⟩ := exists_nat_gt C
    exact mem_iUnion.mpr ⟨K, fun n => (hC n).trans hK.le⟩
  obtain ⟨K, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have hx₀bound : ∀ n, ‖g n x₀‖ ≤ (K : ℝ) := interior_subset hx₀
  refine ⟨4 * (K : ℝ) / δ, ?_⟩
  intro n
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  let v : E := ((δ / 2 : ℝ) : ℂ) • x
  have hvnorm : ‖v‖ = δ / 2 := by
    simp [v, norm_smul, hx, abs_of_pos hδ, abs_of_pos (half_pos hδ)]
  have hmem : x₀ + v ∈ S K := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : x₀ + v - x₀ = v := by abel
    rw [hdiff, hvnorm]
    linarith
  have hnorm : ‖g n v‖ ≤ 2 * (K : ℝ) := by
    have heq : g n v = g n (x₀ + v) - g n x₀ := by simp
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith [hmem n, hx₀bound n])
  have hscaled : ‖g n v‖ = (δ / 2) * ‖g n x‖ := by
    simp [v, map_smul, norm_smul, abs_of_pos hδ, abs_of_pos (half_pos hδ)]
  rw [hscaled] at hnorm
  exact (le_div_iff₀ hδ).mpr (by nlinarith)

end SurveyStatements.P1
