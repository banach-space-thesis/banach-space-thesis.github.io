import ThesisCommon.Analysis.SignAveraging
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite Rademacher moments for the real Grothendieck estimate.  All
averages are finite sums; no probability representation theorem is used. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
namespace Grothendieck

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

section Mean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

@[simp] theorem mean_const (c : ℝ) : mean (fun _ : Ω => c) = c := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h]

theorem mean_add (f g : Ω → ℝ) : mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, mul_add]

theorem mean_sub (f g : Ω → ℝ) : mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, mul_sub]

theorem mean_mul_left (c : ℝ) (f : Ω → ℝ) : mean (fun ω => c * f ω) = c * mean f := by
  simp only [mean, Finset.mul_sum]
  ring

theorem mean_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ mean f := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ω _ => h ω)

theorem mean_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean f ≤ mean g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => h ω) (by positivity)

theorem mean_sum {I : Type*} [Fintype I] (f : I → Ω → ℝ) :
    mean (fun ω => ∑ i, f i ω) = ∑ i, mean (f i) := by
  simp only [mean, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_mul_sq_le (f g : Ω → ℝ) :
    (mean (fun ω => f ω * g ω)) ^ 2 ≤ mean (fun ω => f ω ^ 2) * mean (fun ω => g ω ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω) f g
  dsimp [mean]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg (Fintype.card Ω : ℝ)⁻¹)]

end Mean

def rademacher {n : ℕ} (a : Fin n → ℝ) (ε : Fin n → Bool) : ℝ :=
  ∑ i, signedValue (ε i) (a i)

theorem mean_succ {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    mean f = (mean (fun ε => f (Fin.cons false ε)) +
      mean (fun ε => f (Fin.cons true ε))) / 2 := by
  have hsum : (∑ ε, f ε) = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) := by
    exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool))
      _ f (fun _ => rfl)).symm
  simp only [mean, hsum, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ,
    Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev]
  ring

@[simp] theorem rademacher_cons {n : ℕ} (a : Fin (n+1) → ℝ) (b : Bool)
    (ε : Fin n → Bool) :
    rademacher a (Fin.cons b ε) = signedValue b (a 0) + rademacher (fun i => a i.succ) ε := by
  simp [rademacher, Fin.sum_univ_succ]

/-- The exact second moment of a finite signed linear form. -/
theorem rademacher_second {n : ℕ} (a : Fin n → ℝ) :
    mean (fun ε => rademacher a ε ^ 2) = ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp [rademacher, mean]
  | succ n ih =>
    rw [mean_succ, ← mean_add]
    simp only [rademacher_cons, signedValue, Bool.false_eq_true, if_false, if_true]
    have heq : (fun ε => (-a 0 + rademacher (fun i => a i.succ) ε) ^ 2 +
        (a 0 + rademacher (fun i => a i.succ) ε) ^ 2) =
        (fun ε => 2 * (rademacher (fun i => a i.succ) ε ^ 2) + 2 * a 0 ^ 2) := by
      funext ε
      ring
    rw [heq, mean_add, mean_mul_left, mean_const, ih, Fin.sum_univ_succ]
    ring

/-- The exact fourth moment, with the diagonal correction displayed. -/
theorem rademacher_fourth {n : ℕ} (a : Fin n → ℝ) :
    mean (fun ε => rademacher a ε ^ 4) =
      3 * (∑ i, a i ^ 2) ^ 2 - 2 * ∑ i, a i ^ 4 := by
  induction n with
  | zero => simp [rademacher, mean]
  | succ n ih =>
    rw [mean_succ, ← mean_add]
    simp only [rademacher_cons, signedValue, Bool.false_eq_true, if_false, if_true]
    have heq : (fun ε => (-a 0 + rademacher (fun i => a i.succ) ε) ^ 4 +
        (a 0 + rademacher (fun i => a i.succ) ε) ^ 4) =
        (fun ε => 2 * rademacher (fun i => a i.succ) ε ^ 4 +
          (12 * a 0 ^ 2) * rademacher (fun i => a i.succ) ε ^ 2 + 2 * a 0 ^ 4) := by
      funext ε
      ring
    rw [heq, mean_add, mean_add, mean_mul_left, mean_mul_left,
      mean_const, ih, rademacher_second, Fin.sum_univ_succ, Fin.sum_univ_succ]
    ring

theorem rademacher_fourth_le {n : ℕ} (a : Fin n → ℝ) :
    mean (fun ε => rademacher a ε ^ 4) ≤ 3 * (∑ i, a i ^ 2) ^ 2 := by
  rw [rademacher_fourth]
  have h : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem rademacher_covariance {n : ℕ} (a b : Fin n → ℝ) :
    mean (fun ε => rademacher a ε * rademacher b ε) = ∑ i, a i * b i := by
  have ha := rademacher_second a
  have hb := rademacher_second b
  have hab := rademacher_second (fun i => a i + b i)
  have hrad (ε : Fin n → Bool) : rademacher (fun i => a i + b i) ε =
      rademacher a ε + rademacher b ε := by
    dsimp [rademacher]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp [signedValue, add_comm]
  simp_rw [hrad] at hab
  have hfun : (fun ε => (rademacher a ε + rademacher b ε) ^ 2) =
      (fun ε => rademacher a ε ^ 2 + rademacher b ε ^ 2 +
        2 * (rademacher a ε * rademacher b ε)) := by funext ε; ring
  rw [hfun, mean_add, mean_add, mean_mul_left, ha, hb] at hab
  have hsum : (∑ i, (a i + b i) ^ 2) =
      (∑ i, a i ^ 2) + (∑ i, b i ^ 2) + 2 * ∑ i, a i * b i := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hab
  linarith

end Grothendieck
end ThesisCommon
