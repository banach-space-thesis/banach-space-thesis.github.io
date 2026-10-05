import ThesisCommon.Analysis.L1FiniteMaximumMass
import ThesisCommon.Analysis.GrothendieckMoments
import Mathlib.Analysis.InnerProductSpace.Basic

/-! The finite Rademacher estimate behind the Enflo maximum-mass argument.
All averages are finite sums and all L1 quantities are genuine integrals.
The norm second moment gives the same estimate over real and complex scalars. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThesisCommon
open Grothendieck

variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_sign_sum_second_moment {n : ℕ} (a : Fin n → 𝕜) :
    mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖ ^ 2) =
      ∑ i, ‖a i‖ ^ 2 := by
  induction n with
  | zero => simp [mean]
  | succ n ih =>
    rw [mean_succ, ← mean_add]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, signedValue,
      Bool.false_eq_true, ite_false, ite_true]
    have hp : (fun ε : Fin n → Bool =>
        ‖-a 0 + ∑ i, (if ε i then a i.succ else -a i.succ)‖ ^ 2 +
          ‖a 0 + ∑ i, (if ε i then a i.succ else -a i.succ)‖ ^ 2) =
        (fun ε => 2 * ‖∑ i, signedValue (ε i) (a i.succ)‖ ^ 2 + 2 * ‖a 0‖ ^ 2) := by
      funext ε
      have h := parallelogram_law_with_norm 𝕜
        (∑ i, signedValue (ε i) (a i.succ)) (a 0)
      simp only [← pow_two, signedValue, sub_eq_add_neg] at h
      simp only [signedValue]
      rw [add_comm (-a 0), add_comm (a 0)]
      nlinarith [h]
    rw [hp, mean_add, mean_mul_left, mean_const, ih]
    ring

theorem scalar_sign_norm_mean_sq_le {n : ℕ} (a : Fin n → 𝕜) :
    (mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖)) ^ 2 ≤
      ∑ i, ‖a i‖ ^ 2 := by
  have h := mean_mul_sq_le
    (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖) (fun _ => 1)
  simpa only [mul_one, one_pow, mean_const, scalar_sign_sum_second_moment] using h

theorem finite_norm_energy_le_max (n : ℕ) (a : ℕ → 𝕜) :
    (∑ i : Fin n, ‖a i‖ ^ 2) ≤ finiteMaxNorm n a * ∑ i : Fin n, ‖a i‖ := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (norm_le_finiteMaxNorm a i.isLt) (norm_nonneg _)

theorem quadratic_young_of_square_le {A U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hA : A ^ 2 ≤ U * V) (k : ℝ) : 2 * k * A ≤ k ^ 2 * U + V := by
  by_cases hU0 : U = 0
  · have hA0 : A = 0 := by rw [hU0, zero_mul] at hA; nlinarith [sq_nonneg A]
    simp only [hA0, hU0, mul_zero, zero_add]
    exact hV
  · have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
    apply (mul_le_mul_iff_right₀ hUp).mp
    nlinarith [sq_nonneg (k * U - A)]

theorem scalar_sign_norm_mean_young (n : ℕ) (a : ℕ → 𝕜) (k : ℝ) :
    2 * k * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖) ≤
      k ^ 2 * finiteMaxNorm n a + ∑ i : Fin n, ‖a i‖ :=
  quadratic_young_of_square_le (finiteMaxNorm_nonneg n a)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    ((scalar_sign_norm_mean_sq_le (fun i : Fin n => a i)).trans (finite_norm_energy_le_max n a)) k

theorem square_le_mul_of_all_quadratics {c U V : ℝ} (hc : 0 ≤ c) (hU : 0 ≤ U) (hV : 0 ≤ V)
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

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem l1_finset_sum_coe {I : Type*} (s : Finset I) (f : I → Lp 𝕜 1 μ) :
    (↑(∑ i ∈ s, f i) : X → 𝕜) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero 𝕜 1 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add Filter.EventuallyEq.rfl ih)

theorem l1_signedValue_coe (b : Bool) (f : Lp 𝕜 1 μ) :
    (↑(signedValue b f) : X → 𝕜) =ᵐ[μ] fun x => signedValue b (f x) := by
  cases b
  · exact Lp.coeFn_neg f
  · exact Filter.EventuallyEq.rfl

theorem l1_sign_sum_coe {n : ℕ} (f : Fin n → Lp 𝕜 1 μ) (ε : Fin n → Bool) :
    (↑(∑ i, signedValue (ε i) (f i)) : X → 𝕜) =ᵐ[μ]
      fun x => ∑ i, signedValue (ε i) (f i x) := by
  apply (l1_finset_sum_coe Finset.univ _).trans
  filter_upwards [ae_all_iff.mpr (fun i => l1_signedValue_coe (ε i) (f i))] with x hx
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem integrable_finite_mean {Ω : Type*} [Fintype Ω] (f : Ω → X → ℝ)
    (hf : ∀ ω, Integrable (f ω) μ) : Integrable (fun x => mean (fun ω => f ω x)) μ :=
  (integrable_finset_sum _ (fun ω _ => hf ω)).const_mul _

theorem integral_finite_mean {Ω : Type*} [Fintype Ω] (f : Ω → X → ℝ)
    (hf : ∀ ω, Integrable (f ω) μ) :
    (∫ x, mean (fun ω => f ω x) ∂μ) = mean (fun ω => ∫ x, f ω x ∂μ) := by
  simp only [mean]
  rw [integral_const_mul, integral_finset_sum _ (fun ω _ => hf ω)]

theorem l1_sign_sum_norm {n : ℕ} (f : Fin n → Lp 𝕜 1 μ) (ε : Fin n → Bool) :
    ‖∑ i, signedValue (ε i) (f i)‖ = ∫ x, ‖∑ i, signedValue (ε i) (f i x)‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [l1_sign_sum_coe f ε] with x hx
  rw [hx]

theorem l1_sign_sum_norm_mean_young (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) (k : ℝ) :
    2 * k * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (f i)‖) ≤
      k ^ 2 * l1FiniteMaximumMass n f + ∑ i : Fin n, ‖f i‖ := by
  have hsign (ε : Fin n → Bool) :
      Integrable (fun x => ‖∑ i, signedValue (ε i) (f i x)‖) μ :=
    ((L1.integrable_coeFn (∑ i, signedValue (ε i) (f i))).congr
      (l1_sign_sum_coe (fun i : Fin n => f i) ε)).norm
  have hi := integrable_finite_mean _ hsign
  have h := integral_mono (hi.const_mul (2 * k))
    (((integrable_finiteMaxNorm n f).const_mul (k ^ 2)).add
      (integrable_finset_sum _ (fun i : Fin n => fun _ => (L1.integrable_coeFn (f i)).norm)))
    (fun x => scalar_sign_norm_mean_young n (fun j => f j x) k)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add ((integrable_finiteMaxNorm n f).const_mul (k ^ 2))
    (integrable_finset_sum _ (fun i : Fin n => fun _ => (L1.integrable_coeFn (f i)).norm)),
    integral_const_mul, integral_finset_sum _ (fun i : Fin n => fun _ => (L1.integrable_coeFn (f i)).norm),
    integral_finite_mean _ hsign] at h
  simpa only [← l1_sign_sum_norm, ← L1.norm_eq_integral_norm, l1FiniteMaximumMass] using h

theorem l1_lower_sign_norm_square_le (n : ℕ) (f : ℕ → Lp 𝕜 1 μ) {c : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ ε : Fin n → Bool, c ≤ ‖∑ i, signedValue (ε i) (f i)‖) :
    c ^ 2 ≤ l1FiniteMaximumMass n f * ∑ i : Fin n, ‖f i‖ := by
  apply square_le_mul_of_all_quadratics hc (l1FiniteMaximumMass_nonneg n f)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro k hk
  have ha : c ≤ mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (f i)‖) := by
    simpa only [mean_const] using mean_mono hlower
  exact (mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2 * k)).trans
    (l1_sign_sum_norm_mean_young n f k)

end ThesisCommon
