import PL1.HeadTail
import PL1.L1Multiplication

/-! # Actual Haar L1 norm preservation and spike separation -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PL1.HeadTail
open Walsh

variable {K : Type*} [RCLike K]

theorem norm_toLp (f : C(Walsh.Group, K)) :
    ‖ContinuousMap.toLp 1 haar K f‖ = ∫ x, ‖f x‖ ∂haar := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := K) haar f] with x hx
  rw [hx]

/-- Exact product norm; no positivity is required of the tail multiplier. -/
theorem norm_multiplier_toLp {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hq : DependsOn T q) :
    ‖L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K f)‖ =
      ‖ContinuousMap.toLp 1 haar ℝ q‖ * ‖ContinuousMap.toLp 1 haar K f‖ := by
  rw [L1Multiplication.multiplier_toLp, norm_toLp, norm_toLp, norm_toLp]
  exact integral_norm_smul hST f q hf hq

/-- A nonnegative tail density of mass one preserves every finite head norm. -/
theorem norm_multiplier_toLp_of_density {S T : Finset ℕ} (hST : Disjoint S T)
    (f : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hq : DependsOn T q)
    (hq0 : ∀ᵐ x ∂haar, 0 ≤ q x) (hq1 : ∫ x, q x ∂haar = 1) :
    ‖L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K f)‖ =
      ‖ContinuousMap.toLp 1 haar K f‖ := by
  rw [norm_multiplier_toLp hST f q hf hq]
  have hn : ‖ContinuousMap.toLp 1 haar ℝ q‖ = 1 := by
    rw [norm_toLp, ← hq1]
    apply integral_congr_ae
    filter_upwards [hq0] with x hx
    exact Real.norm_of_nonneg hx
  rw [hn, one_mul]

/-- Finite heads are separated by an actual concentrated tail multiplier on Haar L1. -/
theorem concentration_multiplier_toLp {S T : Finset ℕ} (hST : Disjoint S T)
    (f g : C(Walsh.Group, K)) (q : C(Walsh.Group, ℝ))
    (hf : DependsOn S f) (hg : DependsOn S g) (hq : DependsOn T q)
    (hq0 : ∀ᵐ x ∂haar, 0 ≤ q x) (hq1 : ∫ x, q x ∂haar = 1)
    (B : Set Walsh.Group) (hB : MeasurableSet B) (δ : ℝ)
    (hsmall : haar.real B ≤ δ) (hconcentrated : 1 - δ ≤ ∫ x in B, q x ∂haar) :
    (1 - 2 * δ) * (‖ContinuousMap.toLp 1 haar K f‖ + ‖ContinuousMap.toLp 1 haar K g‖) ≤
      ‖ContinuousMap.toLp 1 haar K f +
        L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K g)‖ := by
  have hn : ‖ContinuousMap.toLp 1 haar K f +
      L1Multiplication.multiplier K q (ContinuousMap.toLp 1 haar K g)‖ =
        ∫ x, ‖f x + q x • g x‖ ∂haar := by
    rw [L1Multiplication.multiplier_toLp, ← map_add, norm_toLp]
    rfl
  rw [hn, norm_toLp, norm_toLp]
  exact concentration_lower_bound hST f g q hf hg hq hq0 hq1 B hB δ hsmall hconcentrated

#print axioms norm_multiplier_toLp
#print axioms concentration_multiplier_toLp
end PL1.HeadTail
