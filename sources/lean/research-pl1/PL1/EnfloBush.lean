import PL1.FiniteRademacherClipping
import PL1.EnfloStarbirdDyadic
import PL1.DyadicCellMeasure

/-! # A positive dyadic bush from an actual bounded-below L1 embedding

The finite sign averages and the integrals in this file use actual functions
and actual L1 vectors. No Enflo extraction or moment estimate is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PL1.EnfloBush
open Bonami FiniteRademacherClipping

theorem average_sq_le (n : ℕ) (f : Cube n → ℝ) :
    (average n f) ^ 2 ≤ average n (fun x => f x ^ 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h₀ := ih (fun x => f (false, x))
    have h₁ := ih (fun x => f (true, x))
    change ((average n (fun x => f (false, x)) + average n (fun x => f (true, x))) / 2) ^ 2 ≤ _
    change _ ≤ (average n (fun x => f (false, x) ^ 2) + average n (fun x => f (true, x) ^ 2)) / 2
    nlinarith [sq_nonneg (average n (fun x => f (false, x)) - average n (fun x => f (true, x)))]

theorem rademacher_abs_average_sq_le (n : ℕ) (a : ℕ → ℝ) :
    (average n (fun x => |rademacherSum n a x|)) ^ 2 ≤ energy n a := by
  have h := average_sq_le n (fun x => |rademacherSum n a x|)
  simpa only [sq_abs, second_moment] using h

def maxAbs : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, a => max (maxAbs n a) |a n|

theorem maxAbs_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ maxAbs n a := by
  cases n with
  | zero => rfl
  | succ n => exact (abs_nonneg _).trans (le_max_right _ _)

theorem abs_le_maxAbs {n j : ℕ} (a : ℕ → ℝ) (hj : j < n) : |a j| ≤ maxAbs n a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j < n
    · exact (ih h).trans (le_max_left _ _)
    · have he : j = n := by omega
      subst j
      exact le_max_right _ _

theorem energy_le_maxAbs_mul_sum (n : ℕ) (a : ℕ → ℝ) :
    energy n a ≤ maxAbs n a * ∑ j ∈ Finset.range n, |a j| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (a j) ^ 2 = |a j| * |a j| := by rw [← sq, sq_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_le_maxAbs a (Finset.mem_range.mp hj)) (abs_nonneg _)

theorem quadratic_young {A U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : A ^ 2 ≤ U * V) (k : ℝ) : 2 * k * A ≤ k ^ 2 * U + V := by
  by_cases hU0 : U = 0
  · have hA0 : A = 0 := by rw [hU0, zero_mul] at hA; nlinarith [sq_nonneg A]
    simp only [hA0, hU0, mul_zero, zero_add]
    exact hV
  · have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
    apply (mul_le_mul_iff_right₀ hUp).mp
    nlinarith [sq_nonneg (k * U - A)]

theorem rademacher_abs_average_young (n : ℕ) (a : ℕ → ℝ) (k : ℝ) :
    2 * k * average n (fun x => |rademacherSum n a x|) ≤
      k ^ 2 * maxAbs n a + ∑ j ∈ Finset.range n, |a j| :=
  quadratic_young (maxAbs_nonneg n a) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    ((rademacher_abs_average_sq_le n a).trans (energy_le_maxAbs_mul_sum n a)) k

theorem square_le_mul_of_quadratic {c U V : ℝ} (hc : 0 ≤ c) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : ∀ k : ℝ, 0 ≤ k → 2 * k * c ≤ k ^ 2 * U + V) : c ^ 2 ≤ U * V := by
  by_cases hc0 : c = 0
  · simpa only [hc0, zero_pow (by norm_num : 2 ≠ 0)] using mul_nonneg hU hV
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  by_cases hU0 : U = 0
  · have hh := h ((V + 1) / c) (div_nonneg (by linarith) hc)
    rw [hU0, mul_zero, zero_add] at hh
    have he : ((V + 1) / c) * c = V + 1 := div_mul_cancel₀ _ hc0
    nlinarith
  · have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
    have hh := mul_le_mul_of_nonneg_left (h (c / U) (div_nonneg hc hU)) hU
    have he : U * (c / U) = c := mul_div_cancel₀ c hU0
    have he2 := congrArg (fun z : ℝ => z ^ 2) he
    nlinarith

def signAt : (n : ℕ) → Cube n → ℕ → ℝ
  | 0, _, _ => 1
  | n + 1, (b, x), j => if j = n then (if b then -1 else 1) else signAt n x j

theorem abs_signAt (n : ℕ) (b : Cube n) (j : ℕ) : |signAt n b j| = 1 := by
  induction n with
  | zero => norm_num [signAt]
  | succ n ih =>
    obtain ⟨b, x⟩ := b
    by_cases hj : j = n
    · subst j
      cases b <;> norm_num [signAt]
    · simpa only [signAt, ite_eq_right hj] using ih x

section Integral
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_average (n : ℕ) (f : Cube n → Ω → ℝ)
    (hf : ∀ b, Integrable (f b) μ) : Integrable (fun x => average n (fun b => f b x)) μ := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact ((ih (fun b => f (false, b)) (fun b => hf (false, b))).add
      (ih (fun b => f (true, b)) (fun b => hf (true, b)))).div_const 2

theorem integral_average (n : ℕ) (f : Cube n → Ω → ℝ)
    (hf : ∀ b, Integrable (f b) μ) :
    (∫ x, average n (fun b => f b x) ∂μ) = average n (fun b => ∫ x, f b x ∂μ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ x, (average n (fun b => f (false, b) x) + average n (fun b => f (true, b) x)) / 2 ∂μ) = _
    rw [integral_div, integral_add
      (integrable_average n _ (fun b => hf (false, b)))
      (integrable_average n _ (fun b => hf (true, b))), ih _ (fun b => hf (false, b)),
      ih _ (fun b => hf (true, b))]
    rfl

def signedSum : (n : ℕ) → (ℕ → Lp ℝ 1 μ) → Cube n → Lp ℝ 1 μ
  | 0, _, _ => 0
  | n + 1, f, (b, x) => (if b then -f n else f n) + signedSum n f x

theorem signedSum_coe (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (b : Cube n) :
    signedSum n f b =ᵐ[μ] (fun x => rademacherSum n (fun j => f j x) b) := by
  induction n with
  | zero => exact Lp.coeFn_zero _ _ _
  | succ n ih =>
    obtain ⟨b, y⟩ := b
    cases b
    · filter_upwards [Lp.coeFn_add (f n) (signedSum n f y), ih y] with x hx hy
      simpa only [signedSum, rademacherSum, Bool.false_eq_true, ite_false, Pi.add_apply, hy] using hx
    · filter_upwards [Lp.coeFn_add (-f n) (signedSum n f y), Lp.coeFn_neg (f n), ih y] with x hx hn hy
      simpa only [signedSum, rademacherSum, ite_true, Pi.add_apply, Pi.neg_apply, hn, hy] using hx

theorem signedSum_eq_sum (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (b : Cube n) :
    signedSum n f b = ∑ j ∈ Finset.range n, signAt n b j • f j := by
  induction n with
  | zero => simp [signedSum]
  | succ n ih =>
    obtain ⟨b, y⟩ := b
    rw [Finset.sum_range_succ]
    have hs : (∑ j ∈ Finset.range n, signAt (n + 1) (b, y) j • f j) =
        ∑ j ∈ Finset.range n, signAt n y j • f j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [signAt, ite_eq_right (Nat.ne_of_lt (Finset.mem_range.mp hj))]
    rw [hs, ← ih y]
    cases b <;> simp [signedSum, signAt, add_comm]

theorem signedSum_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] Lp ℝ 1 μ) (n : ℕ) (f : ℕ → E) (b : Cube n) :
    signedSum n (fun j => T (f j)) b = T (∑ j ∈ Finset.range n, signAt n b j • f j) := by
  rw [signedSum_eq_sum, map_sum]
  simp only [map_smul]

theorem integrable_rademacher (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (b : Cube n) :
    Integrable (fun x => rademacherSum n (fun j => f j x) b) μ :=
  (L1.integrable_coeFn (signedSum n f b)).congr (signedSum_coe n f b)

theorem norm_signedSum (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (b : Cube n) :
    ‖signedSum n f b‖ = ∫ x, |rademacherSum n (fun j => f j x) b| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [signedSum_coe n f b] with x hx
  rw [hx, Real.norm_eq_abs]

theorem integrable_maxAbs (n : ℕ) (f : ℕ → Lp ℝ 1 μ) :
    Integrable (fun x => maxAbs n (fun j => f j x)) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact ih.sup (L1.integrable_coeFn (f n)).abs

theorem signed_norm_average_young (n : ℕ) (f : ℕ → Lp ℝ 1 μ) (k : ℝ) :
    2 * k * average n (fun b => ‖signedSum n f b‖) ≤
      k ^ 2 * (∫ x, maxAbs n (fun j => f j x) ∂μ) + ∑ j ∈ Finset.range n, ‖f j‖ := by
  have hi : Integrable (fun x => average n (fun b => |rademacherSum n (fun j => f j x) b|)) μ :=
    integrable_average n _ (fun b => (integrable_rademacher n f b).abs)
  have h := integral_mono (hi.const_mul (2 * k))
    (((integrable_maxAbs n f).const_mul (k ^ 2)).add
      (integrable_finsetSum _ (fun j _ => (L1.integrable_coeFn (f j)).abs)))
    (fun x => rademacher_abs_average_young n (fun j => f j x) k)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add ((integrable_maxAbs n f).const_mul (k ^ 2))
    (integrable_finsetSum _ (fun j _ => (L1.integrable_coeFn (f j)).abs)), integral_const_mul,
    integral_finsetSum _ (fun j _ => (L1.integrable_coeFn (f j)).abs), integral_average n _
      (fun b => (integrable_rademacher n f b).abs)] at h
  simp_rw [← norm_signedSum n f] at h
  have hn (j : ℕ) : (∫ x, |f j x| ∂μ) = ‖f j‖ := by
    simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm (f j)).symm
  simpa only [hn] using h

theorem lower_signed_norm_sq_le (n : ℕ) (f : ℕ → Lp ℝ 1 μ) {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ b : Cube n, c ≤ ‖signedSum n f b‖) :
    c ^ 2 ≤ (∫ x, maxAbs n (fun j => f j x) ∂μ) * ∑ j ∈ Finset.range n, ‖f j‖ := by
  apply square_le_mul_of_quadratic hc (integral_nonneg (fun x => maxAbs_nonneg n _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro k hk
  have ha : c ≤ average n (fun b => ‖signedSum n f b‖) := by
    simpa only [average_const] using average_mono n hlower
  exact (mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2 * k)).trans
    (signed_norm_average_young n f k)

end Integral

section Dyadic
open DyadicTrace
attribute [local instance] intervalMeasure_probability

theorem norm_dyadic_signed_step (n m : ℕ) (b : Cube m) :
    ‖step (𝕜 := ℝ) n (signAt m b)‖ = 1 := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ _ : ℝ, (1 : ℝ) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_step (𝕜 := ℝ) n (signAt m b)] with x hx
      rw [hx, Real.norm_eq_abs, abs_signAt]
    _ = 1 := by simp

theorem sum_norm_dyadicVector (n : ℕ) :
    (∑ j ∈ Finset.range (2 ^ n), ‖dyadicVector (𝕜 := ℝ) n j‖) = 1 := by
  have he (j : ℕ) (hj : j ∈ Finset.range (2 ^ n)) :
      ‖dyadicVector (𝕜 := ℝ) n j‖ = ((2 : ℝ) ^ n)⁻¹ := by
    rw [PartitionAverages.norm_vector]
    exact intervalMeasure_cell_toReal n j (Finset.mem_range.mp hj)
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Uniform lower bound for the pointwise maximum of actual dyadic indicator images.
The source is the genuine probability interval and the codomain can be any L1 space. -/
theorem dyadic_max_integral_mul_norm (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    {c : ℝ} (hc : 0 ≤ c) (hT : ∀ f : IntervalL1 ℝ, c * ‖f‖ ≤ ‖T f‖) (n : ℕ) :
    c ^ 2 ≤ (∫ x, maxAbs (2 ^ n) (fun j => T (dyadicVector (𝕜 := ℝ) n j) x) ∂μ) * ‖T‖ := by
  have hl (b : Cube (2 ^ n)) : c ≤ ‖signedSum (2 ^ n) (fun j => T (dyadicVector n j)) b‖ := by
    rw [signedSum_map]
    change c ≤ ‖T (step n (signAt (2 ^ n) b))‖
    have h := hT (step n (signAt (2 ^ n) b))
    simpa only [norm_dyadic_signed_step, mul_one] using h
  have h := lower_signed_norm_sq_le (2 ^ n) (fun j => T (dyadicVector n j)) hc hl
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun x => maxAbs_nonneg _ _))
  calc
    _ ≤ ∑ j ∈ Finset.range (2 ^ n), ‖T‖ * ‖dyadicVector (𝕜 := ℝ) n j‖ :=
      Finset.sum_le_sum (fun j _ => T.le_opNorm _)
    _ = ‖T‖ := by rw [← Finset.mul_sum, sum_norm_dyadicVector, mul_one]

end Dyadic

#print axioms dyadic_max_integral_mul_norm
end PL1.EnfloBush
