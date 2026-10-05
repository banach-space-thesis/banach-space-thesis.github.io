import ThesisCommon.Analysis.SubmultiplicativeHull
import ThesisCommon.Analysis.ConcaveEnvelopeMultiplication

/-! The reciprocal profile x/h(x), extended by the identity below one.
An increasing submultiplicative h, between one and x, yields a
nonnegative supermultiplicative profile bounded by the identity. -/
noncomputable section
namespace ThesisCommon

def extendedReciprocalProfile (h : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ 1 then x else x / h x

theorem extendedReciprocalProfile_of_le {h : ℝ → ℝ} {x : ℝ} (hx : x ≤ 1) :
    extendedReciprocalProfile h x = x := if_pos hx

theorem extendedReciprocalProfile_of_one_le {h : ℝ → ℝ} (h1 : h 1 = 1)
    {x : ℝ} (hx : 1 ≤ x) : extendedReciprocalProfile h x = x / h x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [extendedReciprocalProfile, h1]
  · exact if_neg (not_le.mpr hx)

theorem extendedReciprocalProfile_nonneg {h : ℝ → ℝ} (hh : ∀ x, 1 ≤ x → 1 ≤ h x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ extendedReciprocalProfile h x := by
  unfold extendedReciprocalProfile
  split_ifs with hsmall
  · exact hx
  · exact div_nonneg hx (zero_le_one.trans (hh x (le_of_not_ge hsmall)))

theorem extendedReciprocalProfile_le_id {h : ℝ → ℝ} (hh : ∀ x, 1 ≤ x → 1 ≤ h x)
    {x : ℝ} (hx : 0 ≤ x) : extendedReciprocalProfile h x ≤ x := by
  unfold extendedReciprocalProfile
  split_ifs with hsmall
  · exact le_rfl
  · exact div_le_self hx (hh x (le_of_not_ge hsmall))

theorem extendedReciprocalProfile_mul_le {h : ℝ → ℝ}
    (hh : ∀ x, 1 ≤ x → 1 ≤ h x) (hmono : MonotoneOn h (Set.Ici 1))
    (hmul : ∀ x y, 1 ≤ x → 1 ≤ y → h (x * y) ≤ h x * h y)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    extendedReciprocalProfile h x * extendedReciprocalProfile h y ≤
      extendedReciprocalProfile h (x * y) := by
  have hsmall : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y →
      extendedReciprocalProfile h x * extendedReciprocalProfile h y ≤
        extendedReciprocalProfile h (x * y) := by
    intro x y hx hx1 hy
    rw [extendedReciprocalProfile_of_le hx1]
    by_cases hxy : x * y ≤ 1
    · rw [extendedReciprocalProfile_of_le hxy]
      exact mul_le_mul_of_nonneg_left (extendedReciprocalProfile_le_id hh hy) hx
    · have hy1 : 1 < y := by nlinarith
      have hxy1 : 1 < x * y := lt_of_not_ge hxy
      rw [extendedReciprocalProfile, if_neg (not_le.mpr hy1),
        extendedReciprocalProfile, if_neg hxy, ← mul_div_assoc]
      apply div_le_div_of_nonneg_left (mul_nonneg hx hy)
        (zero_lt_one.trans_le (hh _ hxy1.le))
      exact hmono hxy1.le hy1.le (mul_le_of_le_one_left hy hx1)
  by_cases hx1 : x ≤ 1
  · exact hsmall x y hx hx1 hy
  by_cases hy1 : y ≤ 1
  · simpa only [mul_comm] using hsmall y x hy hy1 hx
  have hxp : 1 < x := lt_of_not_ge hx1
  have hyp : 1 < y := lt_of_not_ge hy1
  have hxyp : 1 < x * y := by nlinarith
  simp only [extendedReciprocalProfile, if_neg hx1, if_neg hy1, if_neg (not_le.mpr hxyp)]
  rw [div_mul_div_comm]
  exact div_le_div_of_nonneg_left (mul_nonneg hx hy)
    (zero_lt_one.trans_le (hh _ hxyp.le)) (hmul x y hxp.le hyp.le)

theorem positiveConcaveEnvelope_extendedReciprocalProfile_small
    {h : ℝ → ℝ} (hh : ∀ x, 1 ≤ x → 1 ≤ h x)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    positiveConcaveEnvelope (extendedReciprocalProfile h) x = x := by
  apply le_antisymm
  · exact positiveConcaveEnvelope_le_id (fun _ ht => extendedReciprocalProfile_nonneg hh ht)
      (fun _ ht => extendedReciprocalProfile_le_id hh ht) hx
  · simpa only [extendedReciprocalProfile_of_le hx1] using
      le_positiveConcaveEnvelope (fun _ ht => extendedReciprocalProfile_nonneg hh ht)
        (fun _ ht => extendedReciprocalProfile_le_id hh ht) hx

end ThesisCommon
