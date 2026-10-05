import JLMS.DisjointSynthesis
import JLMS.ScatteredSequences

/-!
# Contractive difference evaluations into c₀

A C₀ function extends continuously to the one-point compactification with
value zero at infinity. Along a convergent point sequence, half the difference
between two successive evaluations tends to zero and has norm at most one.
This supplies the projection for a complemented copy of c₀.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [T2Space K]

/-- Extension by zero at infinity. -/
def extendCZeroOnePoint (f : CZero 𝕜 K) : C(OnePoint K, 𝕜) where
  toFun := OnePoint.rec 0 f
  continuous_toFun := by
    apply (OnePoint.continuous_iff _).mpr
    constructor
    · rw [coclosedCompact_eq_cocompact]
      exact f.zero_at_infty'
    · exact f.continuous_toFun

@[simp] theorem extendCZeroOnePoint_coe (f : CZero 𝕜 K) (x : K) :
    extendCZeroOnePoint f (x : OnePoint K) = f x := rfl

variable (p : ℕ → K) (x : OnePoint K)
    (ht : Tendsto (fun n => (p n : OnePoint K)) atTop (𝓝 x))

/-- The sequence of half-differences is an actual element of c₀. -/
def pointDifferenceValues (f : CZero 𝕜 K) : cZero 𝕜 where
  toFun n := ((1 / 2 : ℝ) : 𝕜) * (f (p (2 * n)) - f (p (2 * n + 1)))
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    have hf : Tendsto (fun n => f (p n)) atTop (𝓝 (extendCZeroOnePoint f x)) :=
      (extendCZeroOnePoint f).continuous.tendsto x |>.comp ht
    have he : StrictMono (fun n : ℕ => 2 * n) := by intro i j hij; dsimp; omega
    have ho : StrictMono (fun n : ℕ => 2 * n + 1) := by intro i j hij; dsimp; omega
    have heven := hf.comp he.tendsto_atTop
    have hodd := hf.comp ho.tendsto_atTop
    simpa only [Function.comp_def, sub_self, mul_zero] using
      (tendsto_const_nhds (x := ((1 / 2 : ℝ) : 𝕜))).mul (heven.sub hodd)

theorem norm_pointDifferenceValues_le (f : CZero 𝕜 K) :
    ‖pointDifferenceValues p x ht f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro n
  change ‖((1 / 2 : ℝ) : 𝕜) * (f (p (2 * n)) - f (p (2 * n + 1)))‖ ≤ ‖f‖
  rw [norm_mul, RCLike.norm_ofReal]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hsub := norm_sub_le (f (p (2 * n))) (f (p (2 * n + 1)))
  have heven := norm_CZero_apply_le f (p (2 * n))
  have hodd := norm_CZero_apply_le f (p (2 * n + 1))
  linarith

/-- The half-difference projection has operator norm at most one. -/
def pointDifferenceEvaluation : CZero 𝕜 K →L[𝕜] cZero 𝕜 :=
  ({ toFun := pointDifferenceValues p x ht
     map_add' f g := by
       ext n
       change ((1 / 2 : ℝ) : 𝕜) * ((f (p (2 * n)) + g (p (2 * n))) -
           (f (p (2 * n + 1)) + g (p (2 * n + 1)))) = _
       change _ = ((1 / 2 : ℝ) : 𝕜) * (f (p (2 * n)) - f (p (2 * n + 1))) +
         ((1 / 2 : ℝ) : 𝕜) * (g (p (2 * n)) - g (p (2 * n + 1)))
       ring
     map_smul' c f := by
       ext n
       change ((1 / 2 : ℝ) : 𝕜) * (c * f (p (2 * n)) - c * f (p (2 * n + 1))) =
         c * (((1 / 2 : ℝ) : 𝕜) * (f (p (2 * n)) - f (p (2 * n + 1))))
       ring } : CZero 𝕜 K →ₗ[𝕜] cZero 𝕜).mkContinuous 1
      (fun f => by simpa using norm_pointDifferenceValues_le p x ht f)

theorem norm_pointDifferenceEvaluation_le : ‖pointDifferenceEvaluation (𝕜 := 𝕜) p x ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using norm_pointDifferenceValues_le p x ht f

end JLMS
