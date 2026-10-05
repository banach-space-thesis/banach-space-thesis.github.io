import JLMS.CZeroTools
import JLMS.Adjoint

/-!
# Operators into c₀ from weak-star-null sequences

A uniformly bounded sequence of functionals that converges pointwise to zero
defines a bounded operator into c₀. Subtracting consecutive pairs of a common
weak-star-convergent subsequence supplies such a sequence, with its norm bound
unchanged after taking half-differences. This is the projection step in the
weak-star sequentially compact branch of the cited factorization machinery.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (f : ℕ → (X →L[𝕜] 𝕜)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖f n‖ ≤ C)
    (hzero : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 0))

def weakStarSequenceValues (x : X) : cZero 𝕜 where
  toFun n := f n x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact hzero x

include hC hbound in
theorem norm_weakStarSequenceValues_le (x : X) :
    ‖weakStarSequenceValues f hzero x‖ ≤ C * ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg x))).mpr
  intro n
  exact (f n).le_opNorm x |>.trans
    (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))

def weakStarSequenceOperator : X →L[𝕜] cZero 𝕜 :=
  ({ toFun := weakStarSequenceValues f hzero
     map_add' x y := by ext n; exact (f n).map_add x y
     map_smul' c x := by ext n; exact (f n).map_smul c x } :
      X →ₗ[𝕜] cZero 𝕜).mkContinuous C
        (norm_weakStarSequenceValues_le f C hC hbound hzero)

theorem norm_weakStarSequenceOperator_le :
    ‖weakStarSequenceOperator f C hC hbound hzero‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact norm_weakStarSequenceValues_le f C hC hbound hzero

@[simp] theorem weakStarSequenceOperator_apply (x : X) (n : ℕ) :
    weakStarSequenceOperator f C hC hbound hzero x n = f n x := rfl

/-- Half-differences of a convergent dual unit-ball sequence are weak-star null. -/
theorem exists_weakStarNull_halfDifferences
    (hX : DualBallWeakStarSeqCompact 𝕜 X)
    (g : ℕ → (X →L[𝕜] 𝕜)) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, ‖((1 / 2 : ℝ) : 𝕜) • (g (s (2 * n)) - g (s (2 * n + 1)))‖ ≤ 1) ∧
      ∀ x, Tendsto (fun n =>
        (((1 / 2 : ℝ) : 𝕜) • (g (s (2 * n)) - g (s (2 * n + 1)))) x) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, s, hs, ht⟩ := hX g hg
  refine ⟨s, hs, ?_, ?_⟩
  · intro n
    rw [norm_smul, RCLike.norm_ofReal]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h := norm_sub_le (g (s (2 * n))) (g (s (2 * n + 1)))
    have he := hg (s (2 * n))
    have ho := hg (s (2 * n + 1))
    linarith
  · intro x
    have he : StrictMono (fun n : ℕ => 2 * n) := by intro i j hij; dsimp; omega
    have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro i j hij; dsimp; omega
    simpa only [Function.comp_def, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, sub_self, mul_zero] using
      (tendsto_const_nhds (x := ((1 / 2 : ℝ) : 𝕜))).mul
        (((ht x).comp he.tendsto_atTop).sub ((ht x).comp ho.tendsto_atTop))

end JLMS
