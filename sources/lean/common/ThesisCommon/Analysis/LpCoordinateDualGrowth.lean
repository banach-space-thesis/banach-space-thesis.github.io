import ThesisCommon.Analysis.SchurFamilySupport
import ThesisCommon.Analysis.MatrixPowerGrowth
import ThesisCommon.Analysis.CountableSumSeparable
import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.MeanInequalities

/-! The coordinate functionals on finite-p sums are weakly null, including
p=1. Their finite signed sums have growth n^(1-1/p), strictly below linear.
No reflexivity or identification of the dual of lp is required. -/
noncomputable section
open Filter Topology TopologicalSpace
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lp_finite_norm_sum_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (s : Finset Γ) (x : lp (fun _ : Γ => 𝕜) p) :
    ∑ i ∈ s, ‖x i‖ ≤ (s.card : ℝ) ^ (1 - 1 / p.toReal) * ‖x‖ := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
  by_cases heq : p.toReal = 1
  · have h := lp.sum_rpow_le_norm_rpow hp0 x s
    simpa only [heq, Real.rpow_one, div_self one_ne_zero, sub_self, Real.rpow_zero, one_mul] using h
  · have hpgt : 1 < p.toReal := lt_of_le_of_ne hp1 (Ne.symm heq)
    let q := p.toReal / (p.toReal - 1)
    have hpq : p.toReal.HolderConjugate q :=
      (Real.holderConjugate_iff_eq_conjExponent hpgt).mpr rfl
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
      (fun i _ => norm_nonneg (x i)) (fun _ _ => zero_le_one)
    have h' : ∑ i ∈ s, ‖x i‖ ≤ (∑ i ∈ s, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) *
        (s.card : ℝ) ^ (1 / q) := by simpa using h
    have hsum : (∑ i ∈ s, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) ≤ ‖x‖ := by
      have hr := Real.rpow_le_rpow
        (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) _))
        (lp.sum_rpow_le_norm_rpow hp0 x s) (one_div_nonneg.mpr hp0.le)
      simpa only [one_div, Real.rpow_rpow_inv (norm_nonneg x) hp0.ne'] using hr
    have hq : 1 / q = 1 - 1 / p.toReal := by dsimp [q]; field_simp
    exact h'.trans (by rw [hq]; simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (Nat.cast_nonneg s.card) _))

theorem norm_sum_lp_coordinate_comp_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p)
    (n : ℕ) (e : Fin n ↪ Γ) (a : Fin n → 𝕜) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ‖∑ i, a i • ((lpCoordinate (𝕜 := 𝕜) p (e i)).comp T)‖ ≤
      ‖T‖ * (n : ℝ) ^ (1 - 1 / p.toReal) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  intro x
  have hsum : ∑ i : Fin n, ‖T x (e i)‖ ≤ (n : ℝ) ^ (1 - 1 / p.toReal) * ‖T x‖ := by
    simpa only [Finset.sum_map, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      using lp_finite_norm_sum_bound p hp (Finset.univ.map e) (T x)
  calc
    _ = ‖∑ i, a i * T x (e i)‖ := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, lpCoordinate_apply, smul_eq_mul]
    _ ≤ ∑ i, ‖a i * T x (e i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖T x (e i)‖ := Finset.sum_le_sum (fun i _ => by
      rw [norm_mul]; simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))
    _ ≤ (n : ℝ) ^ (1 - 1 / p.toReal) * ‖T x‖ := hsum
    _ ≤ (n : ℝ) ^ (1 - 1 / p.toReal) * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := by ring

theorem lp_coordinate_comp_weak_null (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : X →L[𝕜] lp (fun _ : Γ => 𝕜) p)
    (φ : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    Tendsto (fun γ => φ ((lpCoordinate (𝕜 := 𝕜) p γ).comp T)) cofinite (𝓝 0) := by
  apply functional_tendsto_zero_of_sublinear_sums
    (fun γ => (lpCoordinate (𝕜 := 𝕜) p γ).comp T)
    (fun n => ‖T‖ * (n : ℝ) ^ (1 - 1 / p.toReal))
    (norm_sum_lp_coordinate_comp_le p hp T)
  intro M hM ε hε
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hr : 1 - 1 / p.toReal < 1 := sub_lt_self _ (one_div_pos.mpr hp0)
  obtain ⟨n, _, hn, _⟩ := exists_nat_two_sublinear_powers
    (1 - 1 / p.toReal) (1 - 1 / p.toReal) (M * ‖T‖) hr hr hε
  exact ⟨n, by simpa only [mul_assoc, mul_comm ε] using hn⟩

end ThesisCommon
