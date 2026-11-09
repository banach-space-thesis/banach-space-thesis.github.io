import PL1CD.EntropyAverage

noncomputable section
open scoped BigOperators

namespace PL1CD.Entropy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteAverage (f : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

def finiteEntropy (f : ι → ℝ) : ℝ :=
  finiteAverage (fun i => phi (f i)) - phi (finiteAverage f)

theorem finiteAverage_const (c : ℝ) : finiteAverage (fun _ : ι => c) = c := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hc]

theorem finiteEntropy_const (c : ℝ) : finiteEntropy (fun _ : ι => c) = 0 := by
  simp only [finiteEntropy, finiteAverage_const, sub_self]

theorem finiteAverage_nonneg (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : 0 ≤ finiteAverage f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hf i))

omit [Nonempty ι] in
theorem finiteAverage_add (f g : ι → ℝ) :
    finiteAverage (fun i => f i + g i) = finiteAverage f + finiteAverage g := by
  simp [finiteAverage, Finset.sum_add_distrib, mul_add]

omit [Nonempty ι] in
theorem finiteAverage_mul (c : ℝ) (f : ι → ℝ) :
    finiteAverage (fun i => c * f i) = c * finiteAverage f := by
  simp only [finiteAverage, ← Finset.mul_sum]
  ring

omit [Nonempty ι] in
theorem finiteAverage_zero : finiteAverage (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [finiteAverage]

omit [Nonempty ι] in
theorem finiteEntropy_zero : finiteEntropy (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [finiteEntropy, finiteAverage, phi]

theorem finiteAverage_eq_zero_iff (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    finiteAverage f = 0 ↔ ∀ i, f i = 0 := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteAverage, mul_eq_zero, inv_eq_zero, hc, false_or]
  exact Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i) |>.trans (by simp)

theorem finiteAverage_sum (f : ι → ℝ) :
    ∑ i, f i = (Fintype.card ι : ℝ) * finiteAverage f := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hc]

theorem finiteEntropy_nonneg (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finiteEntropy f := by
  have h := sum_hellinger_le_phi_gap f hf (finiteAverage f) (finiteAverage_sum f)
  have hleft : 0 ≤ ∑ i, (Real.sqrt (f i) - Real.sqrt (finiteAverage f)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  change 0 ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, phi (f i) - phi (finiteAverage f)
  have hscaled := mul_le_mul_of_nonneg_left (hleft.trans h) (inv_nonneg.mpr hc.le)
  simpa only [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, mul_zero] using hscaled

theorem phi_mul (a c : ℝ) : phi (c * a) = c * phi a + a * phi c := by
  by_cases ha : a = 0
  · simp [ha, phi]
  by_cases hc : c = 0
  · simp [hc, phi]
  unfold phi
  rw [Real.log_mul hc ha]
  ring

omit [Nonempty ι] in
theorem finiteEntropy_mul (c : ℝ) (f : ι → ℝ) :
    finiteEntropy (fun i => c * f i) = c * finiteEntropy f := by
  unfold finiteEntropy
  simp_rw [phi_mul]
  rw [finiteAverage_add, finiteAverage_mul,
    show (fun i => f i * phi c) = (fun i => phi c * f i) by funext i; ring,
    finiteAverage_mul, finiteAverage_mul, phi_mul]
  ring

theorem perspective_phi (a q : ℝ) (hq : q ≠ 0) :
    q * phi (a / q) = phi a - a * Real.log q := by
  by_cases ha : a = 0
  · simp [ha, phi]
  unfold phi
  rw [Real.log_div ha hq]
  field_simp

omit [Nonempty ι] in
theorem finiteEntropy_perspective (f : ι → ℝ) (hq : finiteAverage f ≠ 0) :
    finiteEntropy f = finiteAverage (fun i => finiteAverage f * phi (f i / finiteAverage f)) := by
  simp_rw [perspective_phi _ _ hq]
  unfold finiteEntropy finiteAverage
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold phi
  ring

theorem perspective_phi_convex (a b A B α β : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hB : 0 < B)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    (α * A + β * B) * phi ((α * a + β * b) / (α * A + β * B)) ≤
      α * (A * phi (a / A)) + β * (B * phi (b / B)) := by
  let M := α * A + β * B
  have hM : 0 < M := by
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [M, hα0, hβ1, hB]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) hA)
        (mul_nonneg hβ hB.le)
  have hw : α * A / M + β * B / M = 1 := by
    rw [← add_div]
    exact div_self hM.ne'
  have hin : (α * A / M) * (a / A) + (β * B / M) * (b / B) = (α * a + β * b) / M := by
    field_simp
  have hconv := Real.convexOn_mul_log.2 (div_nonneg ha hA.le) (div_nonneg hb hB.le)
    (div_nonneg (mul_nonneg hα hA.le) hM.le) (div_nonneg (mul_nonneg hβ hB.le) hM.le) hw
  change phi ((α * A / M) * (a / A) + (β * B / M) * (b / B)) ≤
    (α * A / M) * phi (a / A) + (β * B / M) * phi (b / B) at hconv
  rw [hin] at hconv
  have hscaled := mul_le_mul_of_nonneg_left hconv hM.le
  have hrhs : M * ((α * A / M) * phi (a / A) + (β * B / M) * phi (b / B)) =
      α * (A * phi (a / A)) + β * (B * phi (b / B)) := by
    field_simp
  rw [hrhs] at hscaled
  exact hscaled

theorem finiteEntropy_convex (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    finiteEntropy (fun i => α * f i + β * g i) ≤
      α * finiteEntropy f + β * finiteEntropy g := by
  by_cases hF : finiteAverage f = 0
  · have hz := (finiteAverage_eq_zero_iff f hf).mp hF
    have heq : f = fun _ => 0 := funext hz
    rw [heq, finiteEntropy_zero, mul_zero, zero_add]
    simp only [mul_zero, zero_add, finiteEntropy_mul, le_refl]
  by_cases hG : finiteAverage g = 0
  · have hz := (finiteAverage_eq_zero_iff g hg).mp hG
    have heq : g = fun _ => 0 := funext hz
    rw [heq, finiteEntropy_zero, mul_zero, add_zero]
    simp only [mul_zero, add_zero, finiteEntropy_mul, le_refl]
  have hFp : 0 < finiteAverage f := lt_of_le_of_ne (finiteAverage_nonneg f hf) (Ne.symm hF)
  have hGp : 0 < finiteAverage g := lt_of_le_of_ne (finiteAverage_nonneg g hg) (Ne.symm hG)
  have hmean : finiteAverage (fun i => α * f i + β * g i) =
      α * finiteAverage f + β * finiteAverage g := by
    rw [finiteAverage_add, finiteAverage_mul, finiteAverage_mul]
  have hpos : 0 < α * finiteAverage f + β * finiteAverage g := by
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [hα0, hβ1, hGp]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) hFp)
        (mul_nonneg hβ hGp.le)
  have hpoint := fun i => perspective_phi_convex (f i) (g i) (finiteAverage f) (finiteAverage g)
    α β (hf i) (hg i) hFp hGp hα hβ hαβ
  rw [finiteEntropy_perspective _ (by rw [hmean]; exact hpos.ne'),
    finiteEntropy_perspective f hF, finiteEntropy_perspective g hG, hmean]
  calc
    _ ≤ finiteAverage (fun i => α * (finiteAverage f * phi (f i / finiteAverage f)) +
        β * (finiteAverage g * phi (g i / finiteAverage g))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (by positivity)
    _ = _ := by simp only [finiteAverage_add, finiteAverage_mul]

end PL1CD.Entropy
