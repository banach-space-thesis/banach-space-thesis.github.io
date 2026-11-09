import SurveyStatements.P4Approximation
import Mathlib.Analysis.Normed.Operator.Prod

/-! Genuine finite-dimensional blocks from compatible contractive projections. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

structure ContractiveFiniteDecomposition (𝕜 : Type u) [RCLike 𝕜]
    (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] where
  projection : ℕ → E →L[𝕜] E
  zero : projection 0 = 0
  finiteRank : ∀ n, HasFiniteRank 𝕜 (projection n)
  norm_le : ∀ n, ‖projection n‖ ≤ 1
  comp : ∀ n m, (projection n).comp (projection m) = projection (min n m)
  tendsto : ∀ x, Tendsto (fun n => projection n x) atTop (𝓝 x)

namespace ContractiveFiniteDecomposition

variable (D : ContractiveFiniteDecomposition 𝕜 E)

def blockProjection (n : ℕ) : E →L[𝕜] E := D.projection (n + 1) - D.projection n

lemma blockProjection_finiteRank (n : ℕ) : HasFiniteRank 𝕜 (D.blockProjection n) := by
  simpa only [blockProjection, neg_one_smul, sub_eq_add_neg] using
    (D.finiteRank (n + 1)).add ((D.finiteRank n).smul (-1 : 𝕜))

abbrev Block (n : ℕ) := LinearMap.range (D.blockProjection n).toLinearMap

instance (n : ℕ) : FiniteDimensional 𝕜 (D.Block n) := D.blockProjection_finiteRank n

def coordinate (n : ℕ) : E →L[𝕜] D.Block n :=
  (D.blockProjection n).codRestrict _ (fun x => ⟨x, rfl⟩)

lemma coordinate_val (n : ℕ) (x : E) : (D.coordinate n x).val = D.blockProjection n x := rfl

lemma norm_blockProjection_le_two (n : ℕ) : ‖D.blockProjection n‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [D.norm_le (n + 1), D.norm_le n])

lemma norm_coordinate_le_two (n : ℕ) : ‖D.coordinate n‖ ≤ 2 := by
  apply (D.coordinate n).opNorm_le_bound (by norm_num)
  intro x
  exact ((D.blockProjection n).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (D.norm_blockProjection_le_two n) (norm_nonneg x))

lemma blockProjection_idempotent (n : ℕ) :
    (D.blockProjection n).comp (D.blockProjection n) = D.blockProjection n := by
  simp only [blockProjection, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    D.comp, min_self, min_eq_left (Nat.le_succ n), min_eq_right (Nat.le_succ n)]
  abel

lemma blockProjection_coordinate (n : ℕ) (x : D.Block n) : D.blockProjection n x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  have h := congrArg (fun A : E →L[𝕜] E => A y) (D.blockProjection_idempotent n)
  change D.blockProjection n y = x.val at hy
  rw [← hy]
  exact h

lemma sum_blockProjection (N : ℕ) (x : E) :
    ∑ n ∈ Finset.range N, D.blockProjection n x = D.projection N x := by
  induction N with
  | zero => simp [D.zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [blockProjection, ContinuousLinearMap.sub_apply]
      abel

lemma blocks_tendsto (x : E) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, D.blockProjection n x) atTop (𝓝 x) := by
  simpa only [D.sum_blockProjection] using D.tendsto x

lemma blockProjection_tendsto_zero (x : E) :
    Tendsto (fun n => D.blockProjection n x) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => D.projection (n + 1) x) atTop (𝓝 x) :=
    (D.tendsto x).comp (tendsto_add_atTop_nat 1)
  simpa only [blockProjection, ContinuousLinearMap.sub_apply, sub_self] using ht.sub (D.tendsto x)

end ContractiveFiniteDecomposition

end SurveyStatements.P4
