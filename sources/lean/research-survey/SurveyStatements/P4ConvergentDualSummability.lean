import SurveyStatements.P4ConvergentDualBasics

/-! Coordinate restrictions of an actual c(Y) functional are norm summable.
The bound is obtained by finite unit-ball norming in Y, without a duality
representation assumption. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology
open scoped OnePoint BigOperators

namespace SurveyStatements.P4

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem convergentDualCoordinate_sum_norm_le
    (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) (F : Finset ℕ) :
    ∑ n ∈ F, ‖convergentDualCoordinate Φ n‖ ≤ ‖Φ‖ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((F.card : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hex (n : ℕ) : ∃ x : Y, ‖x‖ ≤ 1 ∧
      ‖convergentDualCoordinate Φ n‖ - δ < RCLike.re (convergentDualCoordinate Φ n x) := by
    by_contra h
    push_neg at h
    have hb := dual_norm_le_of_re_unitBall_bound (convergentDualCoordinate Φ n) h
    linarith
  choose x hx hclose using hex
  let z : C(OnePoint ℕ, Y) := ∑ n ∈ F, convergentDualSingle (𝕜 := 𝕜) n (x n)
  have hz : ‖z‖ ≤ 1 := convergentDualSingle_sum_norm_le (𝕜 := 𝕜) F x 1 (by positivity)
    (fun n hn => hx n)
  have hvalue : ∑ n ∈ F, RCLike.re (convergentDualCoordinate Φ n (x n)) =
      RCLike.re (Φ z) := by
    dsimp only [z]
    rw [map_sum, map_sum]
    rfl
  have hΦz : RCLike.re (Φ z) ≤ ‖Φ‖ := by
    calc
      _ ≤ ‖Φ z‖ := RCLike.re_le_norm _
      _ ≤ ‖Φ‖ * ‖z‖ := Φ.le_opNorm _
      _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = ‖Φ‖ := mul_one _
  have hδmul : (F.card : ℝ) * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (F.card : ℝ) + 1)).mpr
    nlinarith
  calc
    ∑ n ∈ F, ‖convergentDualCoordinate Φ n‖ ≤
        ∑ n ∈ F, (RCLike.re (convergentDualCoordinate Φ n (x n)) + δ) := by
      apply Finset.sum_le_sum
      intro n hn
      linarith [hclose n]
    _ = RCLike.re (Φ z) + (F.card : ℝ) * δ := by
      simp only [Finset.sum_add_distrib, hvalue, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ‖Φ‖ + ε := add_le_add hΦz hδmul

theorem convergentDualCoordinate_summable_norm
    (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) :
    Summable (fun n => ‖convergentDualCoordinate Φ n‖) :=
  summable_of_sum_le (fun n => norm_nonneg _) (convergentDualCoordinate_sum_norm_le Φ)

end SurveyStatements.P4
