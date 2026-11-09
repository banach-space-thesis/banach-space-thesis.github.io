import Mathlib.Analysis.MeanInequalities
import PL1.BonamiTwoPoint
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Dimension-independent tensorization of the two-point noise inequality

The finite cubes and their normalized averages are explicit. The scalar
two-point estimate is a visible premise of the tensorization theorem.
-/

noncomputable section
open scoped BigOperators

namespace PL1.Bonami

def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

def average : (n : ℕ) → (Cube n → ℝ) → ℝ
  | 0, f => f ()
  | n + 1, f => (average n (fun x => f (false, x)) +
      average n (fun x => f (true, x))) / 2

theorem average_nonneg (n : ℕ) {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ average n f := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact div_nonneg (add_nonneg (ih (fun x => hf (false, x)))
      (ih (fun x => hf (true, x)))) (by norm_num)

theorem average_mono (n : ℕ) {f g : Cube n → ℝ} (hfg : ∀ x, f x ≤ g x) :
    average n f ≤ average n g := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    exact div_le_div_of_nonneg_right (add_le_add (ih (fun x => hfg (false, x)))
      (ih (fun x => hfg (true, x)))) (by norm_num)

theorem average_congr (n : ℕ) {f g : Cube n → ℝ} (hfg : ∀ x, f x = g x) :
    average n f = average n g := congrArg (average n) (funext hfg)

@[simp] theorem average_add (n : ℕ) (f g : Cube n → ℝ) :
    average n (fun x => f x + g x) = average n f + average n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average, ih]; ring

@[simp] theorem average_mul (n : ℕ) (c : ℝ) (f : Cube n → ℝ) :
    average n (fun x => c * f x) = c * average n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average, ih]; ring

@[simp] theorem average_const (n : ℕ) (c : ℝ) : average n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average, ih]; ring

def pairNorm (r a b : ℝ) : ℝ := (a ^ r + b ^ r) ^ (1 / r)

theorem pairNorm_nonneg {r a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ pairNorm r a b := Real.rpow_nonneg (by positivity) _

theorem pairNorm_mono {r a b c d : ℝ} (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    pairNorm r a b ≤ pairNorm r c d := by
  exact Real.rpow_le_rpow (by positivity)
    (add_le_add (Real.rpow_le_rpow ha hac hr) (Real.rpow_le_rpow hb hbd hr))
    (by positivity)

theorem pairNorm_add_le {r a b c d : ℝ} (hr : 1 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairNorm r (a + c) (b + d) ≤ pairNorm r a b + pairNorm r c d := by
  have h := Real.Lp_add_le (Finset.univ : Finset Bool)
    (fun i => if i then b else a) (fun i => if i then d else c) hr
  simpa [pairNorm, Fintype.sum_bool, abs_of_nonneg ha, abs_of_nonneg hb,
    abs_of_nonneg hc, abs_of_nonneg hd, abs_of_nonneg (add_nonneg ha hc),
    abs_of_nonneg (add_nonneg hb hd), add_comm] using h

theorem pairNorm_mul {r a b c : ℝ} (hr : r ≠ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    pairNorm r (c * a) (c * b) = c * pairNorm r a b := by
  unfold pairNorm
  rw [Real.mul_rpow hc ha, Real.mul_rpow hc hb, ← mul_add,
    Real.mul_rpow (Real.rpow_nonneg hc _) (by positivity),
    ← Real.rpow_mul hc]
  simp [hr]

/-- The mixed-norm inequality needed for the tensor step, derived from
ordinary Minkowski at the conjugate mixed exponent. -/
theorem pairNorm_average_le (n : ℕ) {r : ℝ} (hr : 1 ≤ r)
    (f g : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    pairNorm r (average n f) (average n g) ≤
      average n (fun x => pairNorm r (f x) (g x)) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hf0 := average_nonneg n (fun x => hf (false, x))
    have hf1 := average_nonneg n (fun x => hf (true, x))
    have hg0 := average_nonneg n (fun x => hg (false, x))
    have hg1 := average_nonneg n (fun x => hg (true, x))
    simp only [average]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹,
      mul_comm _ (2 : ℝ)⁻¹,
      pairNorm_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
        (add_nonneg hf0 hf1) (add_nonneg hg0 hg1) (by norm_num)]
    calc
      _ ≤ (2 : ℝ)⁻¹ * (pairNorm r (average n (fun x => f (false, x)))
            (average n (fun x => g (false, x))) +
          pairNorm r (average n (fun x => f (true, x)))
            (average n (fun x => g (true, x)))) :=
        mul_le_mul_of_nonneg_left (pairNorm_add_le hr hf0 hg0 hf1 hg1) (by norm_num)
      _ ≤ _ := by
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (add_le_add (ih _ _ (fun x => hf (false, x)) (fun x => hg (false, x)))
            (ih _ _ (fun x => hf (true, x)) (fun x => hg (true, x)))) (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)

def moment (n : ℕ) (p : ℝ) (f : Cube n → ℝ) : ℝ :=
  average n (fun x => |f x| ^ p)

theorem moment_nonneg (n : ℕ) (p : ℝ) (f : Cube n → ℝ) : 0 ≤ moment n p f :=
  average_nonneg n (fun x => Real.rpow_nonneg (abs_nonneg _) _)

theorem moment_mul (n : ℕ) (p c : ℝ) (f : Cube n → ℝ) :
    moment n p (fun x => c * f x) = |c| ^ p * moment n p f := by
  simp only [moment, abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg _), average_mul]

theorem mixed_moment_le (n : ℕ) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (f g : Cube n → ℝ) :
    moment n p f ^ (2 / p) + moment n p g ^ (2 / p) ≤
      average n (fun x => (f x ^ 2 + g x ^ 2) ^ (p / 2)) ^ (2 / p) := by
  have hr : 1 ≤ 2 / p := (le_div_iff₀ hp).mpr (by linarith)
  have hi : 1 / (2 / p) = p / 2 := by field_simp
  have hpow (a : ℝ) : (|a| ^ p) ^ (2 / p) = a ^ 2 := by
    rw [← Real.rpow_mul (abs_nonneg _)]
    have he : p * (2 / p) = 2 := by field_simp
    rw [he, Real.rpow_two, sq_abs]
  have h := pairNorm_average_le n hr (fun x => |f x| ^ p) (fun x => |g x| ^ p)
    (fun x => Real.rpow_nonneg (abs_nonneg _) _) (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  simp only [pairNorm, hi, hpow] at h
  have hb : 0 ≤ moment n p f ^ (2 / p) + moment n p g ^ (2 / p) :=
    add_nonneg (Real.rpow_nonneg (moment_nonneg _ _ _) _) (Real.rpow_nonneg (moment_nonneg _ _ _) _)
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hb (p / 2)) h
    (show 0 ≤ (2 : ℝ) / p by positivity)
  rw [← Real.rpow_mul hb] at h'
  have he : p / 2 * (2 / p) = 1 := by field_simp
  simpa only [he, Real.rpow_one, moment] using h'

def meanSlice {n : ℕ} (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (f (false, x) + f (true, x)) / 2

def diffSlice {n : ℕ} (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (f (false, x) - f (true, x)) / 2

/-- The tensor product of the two-point noise maps. False represents +1. -/
def noise (ρ : ℝ) : (n : ℕ) → (Cube n → ℝ) → Cube n → ℝ
  | 0, f => f
  | n + 1, f => fun x => noise ρ n (meanSlice f) x.2 +
      (if x.1 then -ρ else ρ) * noise ρ n (diffSlice f) x.2

theorem average_noise_sq (ρ : ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    average (n + 1) (fun x => noise ρ (n + 1) f x ^ 2) =
      average n (fun x => noise ρ n (meanSlice f) x ^ 2) +
        ρ ^ 2 * average n (fun x => noise ρ n (diffSlice f) x ^ 2) := by
  simp only [average, noise, Bool.false_eq_true, ↓reduceIte]
  rw [← average_add, ← average_mul, ← average_add]
  calc
    _ = average n (fun x => 2 * (noise ρ n (meanSlice f) x ^ 2 +
        ρ ^ 2 * noise ρ n (diffSlice f) x ^ 2)) / 2 := by
      congr 1
      apply average_congr
      intro x
      ring
    _ = _ := by rw [average_mul]; ring

/-- An explicit scalar hypothesis; this is discharged by the scalar Bonami
inequality in the application, rather than hidden in a typeclass. -/
def TwoPointBound (p ρ : ℝ) : Prop :=
  ∀ a b : ℝ, (a ^ 2 + (ρ * b) ^ 2) ^ (p / 2) ≤
    (|a + b| ^ p + |a - b| ^ p) / 2

/-- Every finite tensor power has the same norm bound one. -/
theorem noise_moment_bound {p ρ : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (hpoint : TwoPointBound p ρ) (n : ℕ) (f : Cube n → ℝ) :
    average n (fun x => noise ρ n f x ^ 2) ≤ moment n p f ^ (2 / p) := by
  induction n with
  | zero =>
    simp only [average, noise, moment]
    rw [← Real.rpow_mul (abs_nonneg _)]
    have he : p * (2 / p) = 2 := by field_simp
    rw [he, Real.rpow_two, sq_abs]
  | succ n ih =>
    rw [average_noise_sq]
    calc
      _ ≤ moment n p (meanSlice f) ^ (2 / p) +
          ρ ^ 2 * moment n p (diffSlice f) ^ (2 / p) :=
        add_le_add (ih _) (mul_le_mul_of_nonneg_left (ih _) (sq_nonneg _))
      _ = moment n p (meanSlice f) ^ (2 / p) +
          moment n p (fun x => ρ * diffSlice f x) ^ (2 / p) := by
        rw [moment_mul, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
          (moment_nonneg _ _ _), ← Real.rpow_mul (abs_nonneg _)]
        have he : p * (2 / p) = 2 := by field_simp
        rw [he, Real.rpow_two, sq_abs]
      _ ≤ average n (fun x => (meanSlice f x ^ 2 + (ρ * diffSlice f x) ^ 2) ^
          (p / 2)) ^ (2 / p) := mixed_moment_le n hp hp2 _ _
      _ ≤ moment (n + 1) p f ^ (2 / p) := by
        apply Real.rpow_le_rpow (average_nonneg n (fun x => by positivity)) _ (by positivity)
        calc
          _ ≤ average n (fun x => (|meanSlice f x + diffSlice f x| ^ p +
              |meanSlice f x - diffSlice f x| ^ p) / 2) :=
            average_mono n (fun x => hpoint _ _)
          _ = moment (n + 1) p f := by
            have hplus (x : Cube n) : meanSlice f x + diffSlice f x = f (false, x) := by
              simp only [meanSlice, diffSlice]; ring
            have hminus (x : Cube n) : meanSlice f x - diffSlice f x = f (true, x) := by
              simp only [meanSlice, diffSlice]; ring
            simp only [hplus, hminus, moment, average, div_eq_mul_inv]
            rw [show (fun x : Cube n => (|f (false, x)| ^ p + |f (true, x)| ^ p) * 2⁻¹) =
                (fun x => 2⁻¹ * (|f (false, x)| ^ p + |f (true, x)| ^ p)) by
                  funext x; ring, average_mul, average_add]
            ring

/-- The sharp finite-dimensional Bonami estimate with its scalar premise
fully discharged. -/
theorem noise_moment_bound_sharp {p ρ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) (n : ℕ) (f : Cube n → ℝ) :
    average n (fun x => noise ρ n f x ^ 2) ≤ moment n p f ^ (2 / p) :=
  noise_moment_bound (lt_of_lt_of_le zero_lt_one hp) hp2
    (BonamiTwoPoint.noise_moment p ρ hp hp2 hρ) n f

@[simp] theorem noise_zero (ρ : ℝ) (n : ℕ) : noise ρ n (fun _ => 0) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : meanSlice (fun _ : Cube (n + 1) => (0 : ℝ)) = fun _ => 0 := by
      funext x; simp [meanSlice]
    have hd : diffSlice (fun _ : Cube (n + 1) => (0 : ℝ)) = fun _ => 0 := by
      funext x; simp [diffSlice]
    funext x
    simp [noise, hm, hd, ih]

theorem noise_add (ρ : ℝ) (n : ℕ) (f g : Cube n → ℝ) :
    noise ρ n (fun x => f x + g x) = fun x => noise ρ n f x + noise ρ n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : meanSlice (fun x => f x + g x) = fun x => meanSlice f x + meanSlice g x := by
      funext x; simp only [meanSlice]; ring
    have hd : diffSlice (fun x => f x + g x) = fun x => diffSlice f x + diffSlice g x := by
      funext x; simp only [diffSlice]; ring
    funext x
    simp only [noise, hm, hd, ih]
    ring

theorem noise_mul (ρ : ℝ) (n : ℕ) (c : ℝ) (f : Cube n → ℝ) :
    noise ρ n (fun x => c * f x) = fun x => c * noise ρ n f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : meanSlice (fun x => c * f x) = fun x => c * meanSlice f x := by
      funext x; simp only [meanSlice]; ring
    have hd : diffSlice (fun x => c * f x) = fun x => c * diffSlice f x := by
      funext x; simp only [diffSlice]; ring
    funext x
    simp only [noise, hm, hd, ih]
    ring

theorem noise_sum (ρ : ℝ) (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → Cube n → ℝ) :
    noise ρ n (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, noise ρ n (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using noise_zero ρ n
  | @insert i s hi ih => simp only [Finset.sum_insert hi, noise_add, ih]

end PL1.Bonami


