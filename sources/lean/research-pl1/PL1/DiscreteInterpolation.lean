import PL1.KFunctional

/-!
# The discrete interpolation norm equals the intrinsic space

The K-functional is the actual infimum for the resolvent graph, using its
sum norm. Dyadic samples recover exactly the functions in the original
intrinsic graph, with explicit two-sided norm bounds.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace PL1.DiscreteInterpolation
open Noise Walsh IntrinsicGraph ResolventEstimates

variable (K : Type*) [RCLike K] (rates : ℕ → ℝ≥0)

def term (f : Lp K 1 haar) (n : ℕ) : ℝ :=
  (dyadicRatio ^ (n + 1))⁻¹ * KFunctional.value K rates (dyadicTime (n + 1)) f

/-- The discrete norm on summable inputs. Outside that domain, Lean's real
`tsum` convention does not represent an infinite interpolation norm; all
norm comparisons below are restricted to actual intrinsic vectors. -/
def normValue (f : Lp K 1 haar) : ℝ := ‖f‖ + ∑' n, term K rates f n

theorem term_nonneg (f : Lp K 1 haar) (n : ℕ) : 0 ≤ term K rates f n :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg _))
    (KFunctional.value_nonneg K rates (dyadicTime (n + 1)).property.le f)

theorem norm_analysis_succ (f : Lp K 1 haar) (n : ℕ) :
    ‖(dyadicSystem K rates).analysis (n + 1) f‖ =
      (dyadicRatio ^ (n + 1))⁻¹ * ‖f - resolventL1 K rates (dyadicTime (n + 1)) f‖ := by
  simp only [DyadicSystem.analysis, analysisCoordinate, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg _))]
  rfl

theorem half_analysis_le_term (f : Lp K 1 haar) (n : ℕ) :
    (1 / 2 : ℝ) * ‖(dyadicSystem K rates).analysis (n + 1) f‖ ≤ term K rates f n := by
  have h := mul_le_mul_of_nonneg_left
    (KFunctional.half_norm_defect_le K rates (dyadicTime (n + 1)) f)
    (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg (n + 1)))
  rw [norm_analysis_succ]
  dsimp only [term]
  nlinarith

theorem term_le_analysis (f : Lp K 1 haar) (n : ℕ) :
    term K rates f n ≤ 2 * ‖(dyadicSystem K rates).analysis (n + 1) f‖ +
      dyadicRatio ^ (n + 1) * ‖f‖ := by
  have h := mul_le_mul_of_nonneg_left
    (KFunctional.value_le_defect K rates (dyadicTime (n + 1)) f)
    (inv_nonneg.mpr (pow_nonneg dyadicRatio_nonneg (n + 1)))
  rw [norm_analysis_succ]
  dsimp only [term]
  apply h.trans_eq
  simp only [dyadicTime, dyadicRatio_sq_pow]
  field_simp [dyadicRatio_pow_ne_zero]

theorem summable_term_iff (f : Lp K 1 haar) :
    Summable (term K rates f) ↔
      Summable (fun n => ‖(dyadicSystem K rates).analysis n f‖) := by
  constructor
  · intro h
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (h.mul_left 2)
    intro n
    linarith [half_analysis_le_term K rates f n]
  · intro h
    have h := (summable_nat_add_iff 1).mpr h
    apply Summable.of_nonneg_of_le (term_nonneg K rates f) (term_le_analysis K rates f)
    exact (h.mul_left 2).add (geometric_tail_summable.mul_right ‖f‖)

theorem mem_range_evalZero_iff (f : Lp K 1 haar) :
    f ∈ (evalZero (dyadicSystem K rates).analysis).range ↔ Summable (term K rates f) := by
  rw [IntrinsicGraph.mem_range_evalZero_iff _ rfl, summable_term_iff]

theorem summable_term_eval (x : (dyadicSystem K rates).IntrinsicSpace) :
    Summable (term K rates (evalZero (dyadicSystem K rates).analysis x)) :=
  (mem_range_evalZero_iff K rates _).mp ⟨x, rfl⟩

theorem norm_eq_base_add_tail (x : (dyadicSystem K rates).IntrinsicSpace) :
    ‖x‖ = ‖evalZero (dyadicSystem K rates).analysis x‖ +
      ∑' n, ‖(dyadicSystem K rates).analysis (n + 1)
        (evalZero (dyadicSystem K rates).analysis x)‖ := by
  have h := (summable_term_iff K rates _).mp (summable_term_eval K rates x)
  rw [norm_eq_tsum_operators, h.tsum_eq_zero_add]
  rfl

theorem half_norm_le (x : (dyadicSystem K rates).IntrinsicSpace) :
    (1 / 2 : ℝ) * ‖x‖ ≤ normValue K rates (evalZero (dyadicSystem K rates).analysis x) := by
  let f := evalZero (dyadicSystem K rates).analysis x
  have hb := summable_term_eval K rates x
  have ha := (summable_nat_add_iff 1).mpr ((summable_term_iff K rates f).mp hb)
  have hsum := (ha.mul_left (1 / 2 : ℝ)).tsum_le_tsum (half_analysis_le_term K rates f) hb
  rw [tsum_mul_left] at hsum
  rw [norm_eq_base_add_tail]
  dsimp only [normValue]
  have hf := norm_nonneg f
  change (1 / 2 : ℝ) * (‖f‖ + _) ≤ ‖f‖ + _
  linarith

theorem normValue_le (x : (dyadicSystem K rates).IntrinsicSpace) :
    normValue K rates (evalZero (dyadicSystem K rates).analysis x) ≤
      (2 + dyadicRatio / (1 - dyadicRatio)) * ‖x‖ := by
  let f := evalZero (dyadicSystem K rates).analysis x
  have hb := summable_term_eval K rates x
  have ha := (summable_nat_add_iff 1).mpr ((summable_term_iff K rates f).mp hb)
  have he := geometric_tail_summable.mul_right ‖f‖
  have hsum := hb.tsum_le_tsum (term_le_analysis K rates f) ((ha.mul_left 2).add he)
  rw [Summable.tsum_add (ha.mul_left 2) he, tsum_mul_left, tsum_mul_right,
    geometric_tail_tsum] at hsum
  have ht : 0 ≤ ∑' n, ‖(dyadicSystem K rates).analysis (n + 1) f‖ := tsum_nonneg (fun _ => norm_nonneg _)
  have hc : 0 ≤ dyadicRatio / (1 - dyadicRatio) :=
    div_nonneg dyadicRatio_nonneg one_sub_dyadicRatio_pos.le
  have hct := mul_nonneg hc ht
  rw [norm_eq_base_add_tail]
  change ‖f‖ + _ ≤ (2 + dyadicRatio / (1 - dyadicRatio)) * (‖f‖ + _)
  nlinarith [norm_nonneg f]

end PL1.DiscreteInterpolation
