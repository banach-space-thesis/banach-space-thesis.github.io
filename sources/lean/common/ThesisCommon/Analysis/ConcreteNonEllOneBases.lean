import ThesisCommon.Analysis.CZeroSchauderBasis
import ThesisCommon.Analysis.LpSchauderBasis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Concrete symmetric bases admissible as outer spaces in the mixed-space
factorisation theorems: c₀ and ℓp for 1 < p < ∞. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The norm of a finite sum of distinct scalar ℓp unit vectors is the
p-th root of the number of vectors. -/
theorem scalarLp_norm_finite_units (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Finset ℕ) :
    ‖∑ n ∈ F, lp.single p n (1 : 𝕜)‖ = (F.card : ℝ) ^ p.toReal⁻¹ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  apply (Real.eq_rpow_inv (norm_nonneg _) (Nat.cast_nonneg _) hp0.ne').mpr
  simpa using lp.norm_sum_single (E := fun _ : ℕ => 𝕜) hp0 (fun _ => 1) F

/-- For p > 1, the finite unit sums grow sublinearly; hence there is no
positive ℓ₁ lower estimate on the actual ℓp unit-vector basis. -/
theorem scalarLpSchauderBasis_not_equivalentEllOne
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p) :
    ¬ (scalarLpSchauderBasis (𝕜 := 𝕜) p hp).EquivalentEllOne := by
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  have hinv : p.toReal⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hpr
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (p.toReal⁻¹ - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hinv)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub] using h
  rintro ⟨c, hc, h⟩
  have hle : c ≤ 0 := by
    apply ge_of_tendsto ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hh := h (Finset.range N) (fun _ => 1)
    simp only [norm_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      one_smul, scalarLpSchauderBasis] at hh
    rw [scalarLp_norm_finite_units p hp, Finset.card_range] at hh
    rw [Real.rpow_sub_one hNr.ne']
    exact (le_div_iff₀ hNr).mpr hh
  exact (not_le_of_gt hc) hle

end ThesisCommon
