import ThesisCommon.Analysis.SchauderSymmetry
import ThesisCommon.Analysis.SequenceEntryAlgebra

/-! The normalized symmetric Schauder basis on the actual scalar ℓp space,
for 1 ≤ p < ∞. In particular, the abstract basis definitions are connected
to the manuscript's concrete spaces. Infinity is deliberately excluded.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Unit vectors and bounded coordinate evaluations on scalar ℓp. -/
def scalarLpSchauderBasis (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    NormalizedSchauderBasis 𝕜 (lp (fun _ : ℕ => 𝕜) p) where
  vector n := lp.single p n 1
  coord := lpCoordinate p
  biorthogonal i j := by simp [lpCoordinate_apply, lp.single_apply, Pi.single_apply]
  norm_vector i := by
    rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)), norm_one]
  expansion x := by
    have h := (lp.hasSum_single hp x).tendsto_sum_nat
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using h

/-- The usual ℓp norm is one-unconditional, via pointwise norm domination. -/
theorem scalarLpSchauderBasis_oneUnconditional (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : (scalarLpSchauderBasis (𝕜 := 𝕜) p hp).IsOneUnconditional := by
  classical
  let b := scalarLpSchauderBasis (𝕜 := 𝕜) p hp
  refine ⟨le_rfl, ?_⟩
  intro F a c hac
  apply lp_norm_le_mul_of_pointwise _ _ zero_le_one
  intro i
  change ‖b.coord i (∑ n ∈ F, a n • b.vector n)‖ ≤
    1 * ‖b.coord i (∑ n ∈ F, c n • b.vector n)‖
  rw [b.coord_finite_sum, b.coord_finite_sum, one_mul]
  by_cases hi : i ∈ F
  · simpa only [if_pos hi] using hac i hi
  · simp [hi]

/-- Coordinate insertion preserves the scalar ℓp norm, as witnessed by its
contractive left inverse. This holds for every exponent, including infinity. -/
theorem scalarLpExtend_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : ℕ ↪ ℕ)
    (x : lp (fun _ : ℕ => 𝕜) p) : ‖lpExtend (𝕜 := 𝕜) p f x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((lpExtend (𝕜 := 𝕜) p f).le_opNorm x).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p) f) (norm_nonneg x)))
  · have hh := (lpRestrict (𝕜 := 𝕜) p f).le_opNorm (lpExtend (𝕜 := 𝕜) p f x)
    have heq : lpRestrict (𝕜 := 𝕜) p f (lpExtend (𝕜 := 𝕜) p f x) = x := by
      ext n
      exact lpExtend_apply_image (𝕜 := 𝕜) f x n
    rw [heq] at hh
    exact hh.trans (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) (p := p) f)
      (norm_nonneg (lpExtend (𝕜 := 𝕜) p f x))))

/-- Finite permutation invariance of the actual ℓp norm. -/
theorem scalarLpSchauderBasis_symmetric (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) : (scalarLpSchauderBasis (𝕜 := 𝕜) p hp).HasSymmetricNorm := by
  refine ⟨scalarLpSchauderBasis_oneUnconditional p hp, ?_⟩
  intro σ F a
  change ‖∑ n ∈ F, a n • (lp.single p (σ n) (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) p)‖ =
    ‖∑ n ∈ F, a n • (lp.single p n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) p)‖
  have h := scalarLpExtend_norm p σ.toEmbedding
    (∑ n ∈ F, a n • (lp.single p n (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) p))
  simpa only [map_sum, map_smul, lpExtend_single, Equiv.toEmbedding_apply] using h

end ThesisCommon
