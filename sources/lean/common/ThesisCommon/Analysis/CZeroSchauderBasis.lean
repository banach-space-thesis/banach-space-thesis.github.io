import ThesisCommon.Analysis.SchauderSymmetry
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! The normalized symmetric Schauder basis of the actual scalar null-sequence
space, and its failure of the lower ℓ₁ estimate. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZero_finite_singles_apply (F : Finset ℕ) (a : ℕ → 𝕜) (i : ℕ) :
    (∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜)) i = if i ∈ F then a i else 0 := by
  classical
  change cZeroCoordinate (𝕜 := 𝕜) i (∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜)) = _
  simp [map_sum, map_smul, cZeroSingle_apply, Finset.sum_ite_eq]

/-- Ordered finite sections converge in the supremum norm because the vector
itself tends to zero; coordinatewise convergence alone is not used. -/
theorem cZero_finite_singles_tendsto (x : CZeroSum 𝕜) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, x n • cZeroSingle n (1 : 𝕜))
      atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hx : Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop, norm_zero]
      using x.zero_at_infty'.norm
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hx).2 (ε / 2) (half_pos hε))
  refine ⟨N, fun M hM => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro i
  change ‖(∑ n ∈ Finset.range M, x n • cZeroSingle n (1 : 𝕜)) i - x i‖ ≤ ε / 2
  rw [cZero_finite_singles_apply]
  by_cases hi : i ∈ Finset.range M
  · simpa only [if_pos hi, sub_self, norm_zero] using (half_pos hε).le
  · simp only [hi, if_false, zero_sub, norm_neg]
    exact (hN i (hM.trans (Nat.le_of_not_lt (by simpa using hi)))).le

/-- Actual unit vectors and actual bounded coordinate functionals of c₀. -/
def scalarCZeroSchauderBasis : NormalizedSchauderBasis 𝕜 (CZeroSum 𝕜) where
  vector n := cZeroSingle n 1
  coord := cZeroCoordinate
  biorthogonal i j := by simp
  norm_vector i := by
    apply le_antisymm
    · simpa using norm_cZeroSingle_le i (1 : 𝕜)
    · simpa using BoundedContinuousFunction.norm_coe_le_norm
        (cZeroSingle i (1 : 𝕜)).toBCF i
  expansion := cZero_finite_singles_tendsto

theorem scalarCZeroSchauderBasis_oneUnconditional :
    (scalarCZeroSchauderBasis (𝕜 := 𝕜)).IsOneUnconditional := by
  classical
  refine ⟨le_rfl, ?_⟩
  intro F a c hac
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro i
  change ‖(∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜)) i‖ ≤ _
  rw [cZero_finite_singles_apply]
  by_cases hi : i ∈ F
  · rw [if_pos hi]
    apply (hac i hi).trans
    have h := BoundedContinuousFunction.norm_coe_le_norm
      (∑ n ∈ F, c n • cZeroSingle n (1 : 𝕜)).toBCF i
    change ‖(∑ n ∈ F, c n • cZeroSingle n (1 : 𝕜)) i‖ ≤
      ‖∑ n ∈ F, c n • cZeroSingle n (1 : 𝕜)‖ at h
    simpa only [cZero_finite_singles_apply, if_pos hi] using h
  · simp [hi]

theorem scalarCZeroExtend_norm (f : ℕ ↪ ℕ) (x : CZeroSum 𝕜) :
    ‖cZeroExtend (𝕜 := 𝕜) f x‖ = ‖x‖ := by
  apply le_antisymm (norm_cZeroInsert_le f x)
  have h := norm_cZeroRead_le f (cZeroExtend (𝕜 := 𝕜) f x)
  have heq : cZeroRead f (cZeroExtend (𝕜 := 𝕜) f x) = x := by
    ext n
    exact cZeroExtend_apply_image (𝕜 := 𝕜) f x n
  simpa only [heq] using h

theorem scalarCZeroSchauderBasis_symmetric :
    (scalarCZeroSchauderBasis (𝕜 := 𝕜)).HasSymmetricNorm := by
  refine ⟨scalarCZeroSchauderBasis_oneUnconditional, ?_⟩
  intro σ F a
  have h := scalarCZeroExtend_norm σ.toEmbedding
    (∑ n ∈ F, a n • cZeroSingle n (1 : 𝕜))
  simpa only [map_sum, map_smul, cZeroExtend_single, Equiv.toEmbedding_apply] using h

/-- The norm of every finite sum of distinct unit vectors is at most one. -/
theorem cZero_norm_finite_units_le_one (F : Finset ℕ) :
    ‖∑ n ∈ F, cZeroSingle n (1 : 𝕜)‖ ≤ 1 := by
  classical
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro i
  have h := cZero_finite_singles_apply (𝕜 := 𝕜) F (fun _ => 1) i
  simp only [one_smul] at h
  change ‖(∑ n ∈ F, cZeroSingle n (1 : 𝕜)) i‖ ≤ 1
  rw [h]
  split_ifs <;> simp

theorem scalarCZeroSchauderBasis_not_equivalentEllOne :
    ¬ (scalarCZeroSchauderBasis (𝕜 := 𝕜)).EquivalentEllOne := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  have hh := h (Finset.range N) (fun _ => 1)
  simp only [norm_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    one_smul, scalarCZeroSchauderBasis] at hh
  have hu := cZero_norm_finite_units_le_one (𝕜 := 𝕜) (Finset.range N)
  have : 1 < c * N := by
    have := (div_lt_iff₀ hc).mp hN
    nlinarith
  exact (not_lt_of_ge (hh.trans hu)) this

end ThesisCommon
