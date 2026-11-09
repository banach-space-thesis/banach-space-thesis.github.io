import PL1CD.FiniteEntropy
import PL1.BonamiHaarBridge
import Mathlib.Data.Fintype.BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PL1CD.Entropy

open PL1.Bonami

instance cubeNonempty : (n : ℕ) → Nonempty (Cube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => letI := cubeNonempty n; inferInstanceAs (Nonempty (Bool × Cube n))

theorem finiteAverage_bool (f : Bool → ℝ) : finiteAverage f = (f false + f true) / 2 := by
  simp only [finiteAverage, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  ring

theorem finiteAverage_prod_bool {ι : Type*} [Fintype ι] (f : Bool × ι → ℝ) :
    finiteAverage f = (finiteAverage (fun x => f (false, x)) +
      finiteAverage (fun x => f (true, x))) / 2 := by
  simp only [finiteAverage, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    Fintype.sum_prod_type, Fintype.sum_bool, mul_inv_rev]
  ring

theorem average_eq_finiteAverage (n : ℕ) (f : Cube n → ℝ) : average n f = finiteAverage f := by
  induction n with
  | zero =>
      change f () = (Fintype.card Unit : ℝ)⁻¹ * ∑ i : Unit, f i
      simp only [Fintype.card_unique, Nat.cast_one, inv_one, one_mul, Fintype.sum_unique]
  | succ n ih =>
      change (average n (fun x => f (false, x)) + average n (fun x => f (true, x))) / 2 = _
      rw [ih, ih]
      exact (finiteAverage_prod_bool f).symm

def binaryGap (a b : ℝ) : ℝ := (phi a + phi b) / 2 - phi ((a + b) / 2)

theorem finiteEntropy_bool (f : Bool → ℝ) : finiteEntropy f = binaryGap (f false) (f true) := by
  rw [finiteEntropy, finiteAverage_bool, finiteAverage_bool]
  rfl

theorem binaryGap_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ binaryGap a b := by
  have h := finiteEntropy_nonneg (fun i : Bool => if i then b else a)
    (fun i => by cases i <;> assumption)
  simpa [finiteEntropy_bool] using h

theorem binaryGap_noise_le (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    binaryGap (((1 + ρ) / 2) * a + ((1 - ρ) / 2) * b)
      (((1 - ρ) / 2) * a + ((1 + ρ) / 2) * b) ≤ ρ * binaryGap a b := by
  let f : Bool → ℝ := fun i => if i then b else a
  let g : Bool → ℝ := fun _ => (a + b) / 2
  have hf : ∀ i, 0 ≤ f i := fun i => by cases i <;> assumption
  have hg : ∀ i, 0 ≤ g i := fun _ => div_nonneg (add_nonneg ha hb) (by norm_num)
  have h := finiteEntropy_convex f g hf hg ρ (1 - ρ) hρ0 (by linarith) (by ring)
  rw [finiteEntropy_const, mul_zero, add_zero, finiteEntropy_bool, finiteEntropy_bool] at h
  dsimp [f, g] at h
  have hp : ρ * a + (1 - ρ) * ((a + b) / 2) =
      ((1 + ρ) / 2) * a + ((1 - ρ) / 2) * b := by ring
  have hm : ρ * b + (1 - ρ) * ((a + b) / 2) =
      ((1 - ρ) / 2) * a + ((1 + ρ) / 2) * b := by ring
  simpa only [hp, hm] using h

def cubeEntropy (n : ℕ) (f : Cube n → ℝ) : ℝ :=
  average n (fun x => phi (f x)) - phi (average n f)

theorem cubeEntropy_eq_finiteEntropy (n : ℕ) (f : Cube n → ℝ) :
    cubeEntropy n f = finiteEntropy f := by
  simp only [cubeEntropy, finiteEntropy, average_eq_finiteAverage]

theorem cubeEntropy_nonneg (n : ℕ) (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeEntropy n f := by
  rw [cubeEntropy_eq_finiteEntropy]
  exact finiteEntropy_nonneg f hf

theorem cubeEntropy_convex (n : ℕ) (f g : Cube n → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    cubeEntropy n (fun x => α * f x + β * g x) ≤
      α * cubeEntropy n f + β * cubeEntropy n g := by
  simp only [cubeEntropy_eq_finiteEntropy]
  exact finiteEntropy_convex f g hf hg α β hα hβ hαβ

theorem cubeEntropy_chain (n : ℕ) (f : Cube (n + 1) → ℝ) :
    cubeEntropy (n + 1) f =
      (cubeEntropy n (fun x => f (false, x)) + cubeEntropy n (fun x => f (true, x))) / 2 +
        binaryGap (average n (fun x => f (false, x))) (average n (fun x => f (true, x))) := by
  unfold cubeEntropy binaryGap
  simp only [average]
  ring

def plusSlice {n : ℕ} (ρ : ℝ) (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  ((1 + ρ) / 2) * f (false, x) + ((1 - ρ) / 2) * f (true, x)

def minusSlice {n : ℕ} (ρ : ℝ) (f : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  ((1 - ρ) / 2) * f (false, x) + ((1 + ρ) / 2) * f (true, x)

theorem noise_slice_false (ρ : ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    (fun x => noise ρ (n + 1) f (false, x)) = noise ρ n (plusSlice ρ f) := by
  have hp : plusSlice ρ f = fun x => meanSlice f x + ρ * diffSlice f x := by
    funext x
    simp only [plusSlice, meanSlice, diffSlice]
    ring
  rw [hp, noise_add, noise_mul]
  rfl

theorem noise_slice_true (ρ : ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    (fun x => noise ρ (n + 1) f (true, x)) = noise ρ n (minusSlice ρ f) := by
  have hm : minusSlice ρ f = fun x => meanSlice f x + (-ρ) * diffSlice f x := by
    funext x
    simp only [minusSlice, meanSlice, diffSlice]
    ring
  rw [hm, noise_add, noise_mul]
  rfl

theorem plusSlice_nonneg {n : ℕ} (ρ : ℝ) (f : Cube (n + 1) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x : Cube n) :
    0 ≤ plusSlice ρ f x :=
  add_nonneg (mul_nonneg (by positivity) (hf _))
    (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (hf _))

theorem minusSlice_nonneg {n : ℕ} (ρ : ℝ) (f : Cube (n + 1) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x : Cube n) :
    0 ≤ minusSlice ρ f x :=
  add_nonneg (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (hf _))
    (mul_nonneg (by positivity) (hf _))

theorem average_plusSlice (ρ : ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    average n (plusSlice ρ f) = ((1 + ρ) / 2) * average n (fun x => f (false, x)) +
      ((1 - ρ) / 2) * average n (fun x => f (true, x)) := by
  change average n (fun x => ((1 + ρ) / 2) * f (false, x) +
    ((1 - ρ) / 2) * f (true, x)) = _
  rw [average_add, average_mul, average_mul]

theorem average_minusSlice (ρ : ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    average n (minusSlice ρ f) = ((1 - ρ) / 2) * average n (fun x => f (false, x)) +
      ((1 + ρ) / 2) * average n (fun x => f (true, x)) := by
  change average n (fun x => ((1 - ρ) / 2) * f (false, x) +
    ((1 + ρ) / 2) * f (true, x)) = _
  rw [average_add, average_mul, average_mul]

theorem average_noise (ρ : ℝ) (n : ℕ) (f : Cube n → ℝ) :
    average n (noise ρ n f) = average n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (average n (fun x => noise ρ (n + 1) f (false, x)) +
        average n (fun x => noise ρ (n + 1) f (true, x))) / 2 = _
      rw [noise_slice_false, noise_slice_true, ih, ih]
      rw [average_plusSlice, average_minusSlice]
      change _ = (average n (fun x => f (false, x)) + average n (fun x => f (true, x))) / 2
      ring

theorem cubeEntropy_noise_le (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (n : ℕ) (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    cubeEntropy n (noise ρ n f) ≤ ρ * cubeEntropy n f := by
  induction n with
  | zero => simp [cubeEntropy, average, noise]
  | succ n ih =>
      let fp := fun x => f (false, x)
      let fm := fun x => f (true, x)
      have hfp : ∀ x, 0 ≤ fp x := fun x => hf (false, x)
      have hfm : ∀ x, 0 ≤ fm x := fun x => hf (true, x)
      have hplus := ih (plusSlice ρ f) (plusSlice_nonneg ρ f hf hρ0 hρ1)
      have hminus := ih (minusSlice ρ f) (minusSlice_nonneg ρ f hf hρ0 hρ1)
      have hcplus := cubeEntropy_convex n fp fm hfp hfm
        ((1 + ρ) / 2) ((1 - ρ) / 2) (by positivity) (by linarith) (by ring)
      have hcminus := cubeEntropy_convex n fp fm hfp hfm
        ((1 - ρ) / 2) ((1 + ρ) / 2) (by linarith) (by positivity) (by ring)
      change cubeEntropy n (plusSlice ρ f) ≤ _ at hcplus
      change cubeEntropy n (minusSlice ρ f) ≤ _ at hcminus
      have hbinary := binaryGap_noise_le (average n fp) (average n fm) ρ
        (average_nonneg n hfp) (average_nonneg n hfm) hρ0 hρ1
      rw [cubeEntropy_chain, noise_slice_false, noise_slice_true, average_noise, average_noise]
      rw [average_plusSlice, average_minusSlice, cubeEntropy_chain]
      have hcsum : cubeEntropy n (plusSlice ρ f) + cubeEntropy n (minusSlice ρ f) ≤
          cubeEntropy n fp + cubeEntropy n fm := by linarith
      have hscaled := mul_le_mul_of_nonneg_left hcsum hρ0
      nlinarith

end PL1CD.Entropy
