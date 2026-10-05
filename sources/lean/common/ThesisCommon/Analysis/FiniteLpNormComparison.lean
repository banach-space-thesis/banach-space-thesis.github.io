import ThesisCommon.Analysis.MatrixBlockOperators
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.MeanInequalities

/-! Sharp finite-dimensional changes of exponent on the actual lp spaces.
The two inequalities are proved from sums of powers, and the coordinate
identity is then bundled as a bounded linear map. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finiteLp_norm_rpow (p : BanachExponent) (hp : 0 < p.val.toReal)
    {N : ℕ} (x : FiniteLpSpace 𝕜 p N) :
    ‖x‖ ^ p.val.toReal = ∑ i : Fin N, ‖x i‖ ^ p.val.toReal := by
  simpa only [tsum_fintype] using lp.norm_rpow_eq_tsum hp x

theorem finiteLp_norm_antitone (p q : BanachExponent)
    (hp : 0 < p.val.toReal) (hq : 0 < q.val.toReal) (hpq : p.val.toReal ≤ q.val.toReal)
    {N : ℕ} (x : FiniteLpSpace 𝕜 p N) (y : FiniteLpSpace 𝕜 q N)
    (hxy : ∀ i, y i = x i) : ‖y‖ ≤ ‖x‖ := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg y) (norm_nonneg x) hq).mp
  have hd : 0 ≤ q.val.toReal - p.val.toReal := sub_nonneg.mpr hpq
  have he (i : Fin N) : ‖x i‖ ^ q.val.toReal =
      ‖x i‖ ^ p.val.toReal * ‖x i‖ ^ (q.val.toReal - p.val.toReal) := by
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hp.le hd]
    congr 1
    ring
  calc
    ‖y‖ ^ q.val.toReal = ∑ i : Fin N, ‖x i‖ ^ q.val.toReal := by
      rw [finiteLp_norm_rpow q hq]
      simp only [hxy]
    _ = ∑ i : Fin N, ‖x i‖ ^ p.val.toReal * ‖x i‖ ^ (q.val.toReal - p.val.toReal) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ ≤ ∑ i : Fin N, ‖x i‖ ^ p.val.toReal * ‖x‖ ^ (q.val.toReal - p.val.toReal) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (lp.norm_apply_le_norm
          (ne_of_gt (zero_lt_one.trans_le p.property)) x i) hd)
        (Real.rpow_nonneg (norm_nonneg _) _)
    _ = ‖x‖ ^ p.val.toReal * ‖x‖ ^ (q.val.toReal - p.val.toReal) := by
      rw [← Finset.sum_mul, ← finiteLp_norm_rpow p hp]
    _ = ‖x‖ ^ q.val.toReal := by
      rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hp.le hd]
      congr 1
      ring

theorem finiteLp_norm_le_card_mul (p q : BanachExponent)
    (hp : 0 < p.val.toReal) (hq : 0 < q.val.toReal) (hpq : p.val.toReal ≤ q.val.toReal)
    {N : ℕ} (x : FiniteLpSpace 𝕜 p N) (y : FiniteLpSpace 𝕜 q N)
    (hxy : ∀ i, y i = x i) :
    ‖x‖ ≤ (N : ℝ) ^ (1 / p.val.toReal - 1 / q.val.toReal) * ‖y‖ := by
  have hr : 1 ≤ q.val.toReal / p.val.toReal := (le_div_iff₀ hp).mpr (by simpa)
  have hm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (Finset.univ : Finset (Fin N)) hr
    (fun i _ => Real.rpow_nonneg (norm_nonneg (x i)) p.val.toReal)
  have he : p.val.toReal * (q.val.toReal / p.val.toReal) = q.val.toReal := by field_simp
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ p.val.toReal) ^ (q.val.toReal / p.val.toReal) =
      a ^ q.val.toReal := by rw [← Real.rpow_mul ha, he]
  simp only [← finiteLp_norm_rpow p hp, Finset.card_univ, Fintype.card_fin] at hm
  simp_rw [hpow _ (norm_nonneg _)] at hm
  have hsum : (∑ i : Fin N, ‖x i‖ ^ q.val.toReal) = ‖y‖ ^ q.val.toReal := by
    rw [finiteLp_norm_rpow q hq]
    simp only [hxy]
  rw [hsum] at hm
  apply (Real.rpow_le_rpow_iff (norm_nonneg x)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (norm_nonneg y)) hq).mp
  convert hm using 1
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) (norm_nonneg y),
    ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 2
  field_simp

def finiteLpChangeValue (p q : BanachExponent) {N : ℕ} (x : FiniteLpSpace 𝕜 p N) :
    FiniteLpSpace 𝕜 q N := ⟨x, Memℓp.all x⟩

theorem finiteLpChangeValue_norm_le (p q : BanachExponent)
    (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} (x : FiniteLpSpace 𝕜 p N) :
    ‖finiteLpChangeValue p q x‖ ≤
      (N : ℝ) ^ max (1 / q.val.toReal - 1 / p.val.toReal) 0 * ‖x‖ := by
  have hp0 : 0 < p.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  have hq0 : 0 < q.val.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le q.property)) hq
  rcases le_total p.val.toReal q.val.toReal with h | h
  · have hi : 1 / q.val.toReal - 1 / p.val.toReal ≤ 0 := by
      exact sub_nonpos.mpr (one_div_le_one_div_of_le hp0 h)
    rw [max_eq_right hi, Real.rpow_zero, one_mul]
    exact finiteLp_norm_antitone p q hp0 hq0 h x _ (fun _ => rfl)
  · have hi : 0 ≤ 1 / q.val.toReal - 1 / p.val.toReal := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hq0 h)
    rw [max_eq_left hi]
    exact finiteLp_norm_le_card_mul q p hq0 hp0 h _ x (fun _ => rfl)

def finiteLpChange (p q : BanachExponent) (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} :
    FiniteLpSpace 𝕜 p N →L[𝕜] FiniteLpSpace 𝕜 q N :=
  LinearMap.mkContinuous
    { toFun := finiteLpChangeValue p q
      map_add' := by intros; apply lp.ext; rfl
      map_smul' := by intros; apply lp.ext; rfl }
    ((N : ℝ) ^ max (1 / q.val.toReal - 1 / p.val.toReal) 0)
    (finiteLpChangeValue_norm_le p q hp hq)

@[simp] theorem finiteLpChange_apply (p q : BanachExponent) (hp : p.val ≠ ∞) (hq : q.val ≠ ∞)
    {N : ℕ} (x : FiniteLpSpace 𝕜 p N) (i : Fin N) : finiteLpChange p q hp hq x i = x i := rfl

theorem norm_finiteLpChange_le (p q : BanachExponent) (hp : p.val ≠ ∞) (hq : q.val ≠ ∞) {N : ℕ} :
    ‖finiteLpChange (𝕜 := 𝕜) (N := N) p q hp hq‖ ≤
      (N : ℝ) ^ max (1 / q.val.toReal - 1 / p.val.toReal) 0 :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (Nat.cast_nonneg N) _) _

end ThesisCommon
