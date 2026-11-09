import SurveyStatements.P4ConvergentDualSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Genuine dual representation and norm-dense coordinate tests for c(Y). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter Topology
open scoped OnePoint BigOperators

namespace SurveyStatements.P4

variable {𝕜 Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

lemma convergentDual_pullback_norm_le (φ : StrongDual 𝕜 Y) (p : OnePoint ℕ) :
    ‖φ.comp (ContinuousMap.evalCLM 𝕜 p)‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  exact (φ.le_opNorm (z p)).trans
    (mul_le_mul_of_nonneg_left (z.norm_coe_le_norm p) (norm_nonneg _))

def convergentDualSeriesTerm (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) (n : ℕ) :
    StrongDual 𝕜 C(OnePoint ℕ, Y) :=
  (convergentDualCoordinate Φ n).comp (ContinuousMap.evalCLM 𝕜 (n : OnePoint ℕ))

theorem convergentDualSeries_summable (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) :
    Summable (convergentDualSeriesTerm Φ) :=
  (convergentDualCoordinate_summable_norm Φ).of_norm_bounded
    (fun n => convergentDual_pullback_norm_le (convergentDualCoordinate Φ n) _)

theorem convergentDualSeries_eq_on_zero_limit
    (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) (z : C(OnePoint ℕ, Y)) (hz : z ∞ = 0) :
    Φ z = (∑' n, convergentDualSeriesTerm Φ n) z := by
  have hfirst := (Φ.continuous.tendsto z).comp
    (convergentDualZeroTruncate_tendsto (𝕜 := 𝕜) z hz)
  change Tendsto (fun n => Φ (convergentDualZeroTruncate (𝕜 := 𝕜) n z)) atTop
    (𝓝 (Φ z)) at hfirst
  have heq (n : ℕ) : Φ (convergentDualZeroTruncate (𝕜 := 𝕜) n z) =
      (∑ k ∈ Finset.range n, convergentDualSeriesTerm Φ k) z := by
    simp only [convergentDualZeroTruncate, map_sum, ContinuousLinearMap.sum_apply,
      convergentDualSeriesTerm, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
      convergentDualCoordinate_apply]
  have hfirst' : Tendsto (fun n => (∑ k ∈ Finset.range n, convergentDualSeriesTerm Φ k) z)
      atTop (𝓝 (Φ z)) := by simpa only [heq] using hfirst
  have hsecond := ((ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.tendsto
    (∑' n, convergentDualSeriesTerm Φ n)).comp
    (convergentDualSeries_summable Φ).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hfirst' hsecond

/-- Every functional is a limit evaluation plus a norm-convergent sum of
coordinate evaluations. The coordinate functionals are actually constructed
from the given functional and their norms are summable. -/
theorem convergentDual_representation (Φ : StrongDual 𝕜 C(OnePoint ℕ, Y)) :
    ∃ η : StrongDual 𝕜 Y,
      Φ = η.comp (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)) +
        ∑' n, convergentDualSeriesTerm Φ n := by
  let S := ∑' n, convergentDualSeriesTerm Φ n
  let D := Φ - S
  let η : StrongDual 𝕜 Y := D.comp (ContinuousLinearMap.const 𝕜 (OnePoint ℕ))
  refine ⟨η, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  let w := z - ContinuousMap.const (OnePoint ℕ) (z ∞)
  have hw : w ∞ = 0 := by simp only [w, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, sub_self]
  have hzero : D w = 0 := by
    change Φ w - S w = 0
    exact sub_eq_zero.mpr (convergentDualSeries_eq_on_zero_limit Φ w hw)
  have hη : D z = η (z ∞) := by
    apply sub_eq_zero.mp
    change D z - D (ContinuousMap.const (OnePoint ℕ) (z ∞)) = 0
    rw [← map_sub]
    exact hzero
  change Φ z = η (z ∞) + S z
  change Φ z - S z = η (z ∞) at hη
  exact sub_eq_iff_eq_add.mp hη

/-- Finite coordinate evaluations together with evaluation at the limit
span a norm-dense subspace of the full continuous dual of c(Y). -/
theorem convergentDual_coordinate_span_dense :
    Dense (Submodule.span 𝕜
      {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ,
        ∃ φ : StrongDual 𝕜 Y, Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)} :
      Set (StrongDual 𝕜 C(OnePoint ℕ, Y))) := by
  classical
  let M := Submodule.span 𝕜
    {Φ : StrongDual 𝕜 C(OnePoint ℕ, Y) | ∃ p : OnePoint ℕ,
      ∃ φ : StrongDual 𝕜 Y, Φ = φ.comp (ContinuousMap.evalCLM 𝕜 p)}
  change ∀ Φ, Φ ∈ closure (M : Set (StrongDual 𝕜 C(OnePoint ℕ, Y)))
  intro Φ
  obtain ⟨η, hη⟩ := convergentDual_representation Φ
  have hmem (n : ℕ) : η.comp (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)) +
      ∑ k ∈ Finset.range n, convergentDualSeriesTerm Φ k ∈ M := by
    apply M.add_mem
    · exact Submodule.subset_span ⟨∞, η, rfl⟩
    · apply M.sum_mem
      intro k hk
      exact Submodule.subset_span ⟨(k : OnePoint ℕ), convergentDualCoordinate Φ k, rfl⟩
  have hlim : Tendsto (fun n => η.comp (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)) +
      ∑ k ∈ Finset.range n, convergentDualSeriesTerm Φ k) atTop (𝓝 Φ) := by
    have h := (tendsto_const_nhds
      (x := η.comp (ContinuousMap.evalCLM 𝕜 (∞ : OnePoint ℕ)))).add
      (convergentDualSeries_summable Φ).hasSum.tendsto_sum_nat
    simpa only [← hη] using h
  exact isClosed_closure.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => subset_closure (hmem n))

end SurveyStatements.P4
