import PL1.BonamiTensorization

/-! Concrete finite Rademacher moments and clipping. -/

noncomputable section
open scoped BigOperators

namespace PL1.FiniteRademacherClipping
open PL1.Bonami

/-- The newest Boolean coordinate supplies the sign of coefficient a(n). -/
def rademacherSum : (n : ℕ) → (ℕ → ℝ) → Cube n → ℝ
  | 0, _, _ => 0
  | n + 1, a, (b, x) => (if b then -a n else a n) + rademacherSum n a x

def energy (n : ℕ) (a : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range n, (a j) ^ 2

theorem energy_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ energy n a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_succ (n : ℕ) (a : ℕ → ℝ) :
    energy (n + 1) a = energy n a + (a n) ^ 2 := Finset.sum_range_succ _ _

theorem second_moment (n : ℕ) (a : ℕ → ℝ) :
    average n (fun x => rademacherSum n a x ^ 2) = energy n a := by
  induction n with
  | zero => simp [rademacherSum, average, energy]
  | succ n ih =>
    change (average n (fun x => (a n + rademacherSum n a x) ^ 2) +
      average n (fun x => (-a n + rademacherSum n a x) ^ 2)) / 2 = _
    rw [← average_add]
    have hp : (fun x : Cube n => (a n + rademacherSum n a x) ^ 2 +
        (-a n + rademacherSum n a x) ^ 2) =
        (fun x => 2 * ((a n) ^ 2 + rademacherSum n a x ^ 2)) := by
      funext x
      ring
    rw [hp, average_mul, average_add, average_const, ih, energy_succ]
    ring

theorem mixed_second_moment (n : ℕ) (a b : ℕ → ℝ) :
    average n (fun x => rademacherSum n a x * rademacherSum n b x) =
      ∑ j ∈ Finset.range n, a j * b j := by
  induction n with
  | zero => simp [rademacherSum, average]
  | succ n ih =>
    change (average n (fun x => (a n + rademacherSum n a x) * (b n + rademacherSum n b x)) +
      average n (fun x => (-a n + rademacherSum n a x) * (-b n + rademacherSum n b x))) / 2 = _
    rw [← average_add]
    have hp : (fun x : Cube n =>
        (a n + rademacherSum n a x) * (b n + rademacherSum n b x) +
        (-a n + rademacherSum n a x) * (-b n + rademacherSum n b x)) =
        (fun x => 2 * (a n * b n + rademacherSum n a x * rademacherSum n b x)) := by
      funext x
      ring
    rw [hp, average_mul, average_add, average_const, ih, Finset.sum_range_succ]
    ring

theorem fourth_moment (n : ℕ) (a : ℕ → ℝ) :
    average n (fun x => rademacherSum n a x ^ 4) =
      3 * (energy n a) ^ 2 - 2 * ∑ j ∈ Finset.range n, (a j) ^ 4 := by
  induction n with
  | zero => simp [rademacherSum, average, energy]
  | succ n ih =>
    change (average n (fun x => (a n + rademacherSum n a x) ^ 4) +
      average n (fun x => (-a n + rademacherSum n a x) ^ 4)) / 2 = _
    rw [← average_add]
    have hp : (fun x : Cube n => (a n + rademacherSum n a x) ^ 4 +
        (-a n + rademacherSum n a x) ^ 4) =
        (fun x => 2 * ((a n) ^ 4 + 6 * (a n) ^ 2 * rademacherSum n a x ^ 2 +
          rademacherSum n a x ^ 4)) := by
      funext x
      ring
    rw [hp, average_mul, average_add, average_add, average_const,
      average_mul, second_moment, ih, energy_succ, Finset.sum_range_succ]
    ring

theorem fourth_moment_le (n : ℕ) (a : ℕ → ℝ) :
    average n (fun x => rademacherSum n a x ^ 4) ≤ 3 * (energy n a) ^ 2 := by
  rw [fourth_moment]
  have h : 0 ≤ ∑ j ∈ Finset.range n, (a j) ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
  linarith

def clipEight (z : ℝ) : ℝ := if 8 < z then 8 else if z < -8 then -8 else z

theorem abs_clipEight_le (z : ℝ) : |clipEight z| ≤ 8 := by
  unfold clipEight
  split_ifs with hp hn
  · norm_num
  · norm_num
  · exact abs_le.mpr ⟨le_of_not_gt hn, le_of_not_gt hp⟩

theorem clipEight_sq_le (z : ℝ) : clipEight z ^ 2 ≤ z ^ 2 := by
  unfold clipEight
  split_ifs with hp hn <;> nlinarith

theorem residual_sq_le_fourth (z : ℝ) : (z - clipEight z) ^ 2 ≤ z ^ 4 / 64 := by
  unfold clipEight
  split_ifs with hp hn
  · have hs : 64 ≤ z ^ 2 := by nlinarith
    have h4 := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg z)
    nlinarith
  · have hs : 64 ≤ z ^ 2 := by nlinarith
    have h4 := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg z)
    nlinarith
  · simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    positivity

theorem clipped_second_moment_le (n : ℕ) (a : ℕ → ℝ) :
    average n (fun x => clipEight (rademacherSum n a x) ^ 2) ≤ energy n a := by
  rw [← second_moment]
  exact average_mono n (fun x => clipEight_sq_le (rademacherSum n a x))

theorem residual_second_moment_le (n : ℕ) (a : ℕ → ℝ) (ha : energy n a ≤ 1) :
    average n (fun x => (rademacherSum n a x - clipEight (rademacherSum n a x)) ^ 2) ≤
      (1 / 16 : ℝ) := by
  have h := average_mono n (fun x => residual_sq_le_fourth (rademacherSum n a x))
  have he : average n (fun x => rademacherSum n a x ^ 4 / 64) =
      (1 / 64 : ℝ) * average n (fun x => rademacherSum n a x ^ 4) := by
    convert average_mul n (1 / 64 : ℝ) (fun x => rademacherSum n a x ^ 4) using 1
    congr 1
    funext x
    ring
  rw [he] at h
  have h4 := fourth_moment_le n a
  have hs := pow_le_pow_left₀ (energy_nonneg n a) ha 2
  nlinarith

#print axioms second_moment
#print axioms mixed_second_moment
#print axioms fourth_moment_le
#print axioms residual_second_moment_le

end PL1.FiniteRademacherClipping

