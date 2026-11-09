import PL1.FiniteGrothendieck
import PL1.SummingTransport
import PL1.IntervalDyadicApproximation
import PL1.DyadicL1Coordinates

/-! Stability of summing estimates under pointwise norm convergence. -/
noncomputable section
open scoped BigOperators
open Filter
namespace PL1.ComplementedLattice

section PointwiseLimits
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OneSummingWith.of_pointwise_tendsto (T : ℕ → E →L[ℝ] F)
    (S : E →L[ℝ] F) (C : ℝ) (hT : ∀ m, OneSummingWith (T m) C)
    (hlim : ∀ x, Tendsto (fun m => T m x) atTop (nhds (S x))) : OneSummingWith S C := by
  refine ⟨(hT 0).1, ?_⟩
  intro n x M hx
  apply le_of_tendsto' (tendsto_finsetSum Finset.univ (fun i _ => (hlim (x i)).norm))
  exact fun m => (hT m).2 n x M hx

theorem TwoSummingWith.of_pointwise_tendsto (T : ℕ → E →L[ℝ] F)
    (S : E →L[ℝ] F) (C : ℝ) (hT : ∀ m, TwoSummingWith (T m) C)
    (hlim : ∀ x, Tendsto (fun m => T m x) atTop (nhds (S x))) : TwoSummingWith S C := by
  refine ⟨(hT 0).1, ?_⟩
  intro n x M hM hx
  apply le_of_tendsto' (tendsto_finsetSum Finset.univ (fun i _ => ((hlim (x i)).norm).pow 2))
  exact fun m => (hT m).2 n x M hM hx

end PointwiseLimits
end PL1.ComplementedLattice

namespace PL1.IntervalSumming
open PL1.DyadicTrace PL1.DyadicL1Coordinates PL1.FiniteSumming PL1.ComplementedLattice

theorem oneSumming_interval (k : ℕ) (S : IntervalL1 ℝ →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    OneSummingWith S (128 * ‖S‖) := by
  let T := fun m => (S.comp (synthesis m)).comp (analysis m)
  apply OneSummingWith.of_pointwise_tendsto T S (128 * ‖S‖)
  · intro m
    have ht := (oneSumming_128 (2 ^ m) k (S.comp (synthesis m))).precomp (analysis m)
    apply ht.mono
    have hc : ‖S.comp (synthesis m)‖ ≤ ‖S‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (norm_synthesis_le_one m) (norm_nonneg S))
    calc
      _ ≤ (128 * ‖S‖) * ‖analysis m‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num)) (norm_nonneg _)
      _ ≤ (128 * ‖S‖) * 1 := mul_le_mul_of_nonneg_left (norm_analysis_le_one m) (by positivity)
      _ = _ := mul_one _
  · intro x
    have h := (S.continuous.tendsto x).comp (dyadicAverage_tendsto x)
    simpa only [T, ContinuousLinearMap.comp_apply, synthesis_analysis, Function.comp_def] using h

theorem twoSumming_interval (d : ℕ) (S : (Fin d → ℝ) →L[ℝ] IntervalL1 ℝ) :
    TwoSummingWith S (128 * ‖S‖) := by
  let T := fun m => (synthesis m).comp ((analysis m).comp S)
  apply TwoSummingWith.of_pointwise_tendsto T S (128 * ‖S‖)
  · intro m
    have ht := (twoSumming_128 d (2 ^ m) ((analysis m).comp S)).postcomp (synthesis m)
    apply ht.mono
    have hc : ‖(analysis m).comp S‖ ≤ ‖S‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (norm_analysis_le_one m) (norm_nonneg S))
    calc
      _ ≤ ‖synthesis m‖ * (128 * ‖S‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hc (by norm_num)) (norm_nonneg _)
      _ ≤ 1 * (128 * ‖S‖) := mul_le_mul_of_nonneg_right (norm_synthesis_le_one m) (by positivity)
      _ = _ := one_mul _
  · intro x
    simpa only [T, ContinuousLinearMap.comp_apply, synthesis_analysis] using dyadicAverage_tendsto (S x)

#print axioms oneSumming_interval
#print axioms twoSumming_interval
end PL1.IntervalSumming



