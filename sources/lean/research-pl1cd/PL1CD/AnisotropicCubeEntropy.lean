import PL1CD.CubeEntropy

noncomputable section
open scoped BigOperators

namespace PL1CD.Entropy
open PL1.Bonami

theorem phi_le_mul_log_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    phi a ≤ a * Real.log (a + b) := by
  by_cases ha0 : a = 0
  · simp [ha0, phi]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hap (by linarith)) ha

theorem binaryGap_le_mass_log_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    binaryGap a b ≤ ((a + b) / 2) * Real.log 2 := by
  by_cases hs0 : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, binaryGap, phi]
  have hs : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs0)
  have h := add_le_add (phi_le_mul_log_add a b ha hb) (phi_le_mul_log_add b a hb ha)
  rw [add_comm b a] at h
  unfold binaryGap
  unfold phi at *
  rw [Real.log_div hs.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  nlinarith

def varyingNoise (r : ℕ → ℝ) : (n : ℕ) → (Cube n → ℝ) → Cube n → ℝ
  | 0, f => f
  | n + 1, f => fun x => if x.1 then varyingNoise r n (minusSlice (r n) f) x.2
      else varyingNoise r n (plusSlice (r n) f) x.2

theorem varyingNoise_false (r : ℕ → ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    (fun x => varyingNoise r (n + 1) f (false, x)) = varyingNoise r n (plusSlice (r n) f) := rfl

theorem varyingNoise_true (r : ℕ → ℝ) (n : ℕ) (f : Cube (n + 1) → ℝ) :
    (fun x => varyingNoise r (n + 1) f (true, x)) = varyingNoise r n (minusSlice (r n) f) := rfl

theorem average_varyingNoise (r : ℕ → ℝ) (n : ℕ) (f : Cube n → ℝ) :
    average n (varyingNoise r n f) = average n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (average n (fun x => varyingNoise r (n + 1) f (false, x)) +
        average n (fun x => varyingNoise r (n + 1) f (true, x))) / 2 = _
      rw [varyingNoise_false, varyingNoise_true, ih, ih, average_plusSlice, average_minusSlice]
      change _ = (average n (fun x => f (false, x)) + average n (fun x => f (true, x))) / 2
      ring

theorem varyingNoise_nonneg (r : ℕ → ℝ) (n : ℕ)
    (hr : ∀ j, j < n → r j ∈ Set.Icc 0 1)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) (x : Cube n) :
    0 ≤ varyingNoise r n f x := by
  induction n with
  | zero => exact hf x
  | succ n ih =>
      have hn := hr n (by omega)
      have hprev : ∀ j, j < n → r j ∈ Set.Icc 0 1 := fun j hj => hr j (by omega)
      rcases x with ⟨b, x⟩
      cases b
      · exact ih hprev (plusSlice (r n) f) (plusSlice_nonneg _ f hf hn.1 hn.2) x
      · exact ih hprev (minusSlice (r n) f) (minusSlice_nonneg _ f hf hn.1 hn.2) x

def headFactor (n d : ℕ) : ℝ := (min d n : ℕ) * Real.log 2

theorem cubeEntropy_varyingNoise_head_tail_le
    (r : ℕ → ℝ) (p : ℝ) (hp : 0 ≤ p) (d n : ℕ)
    (hr : ∀ j, j < n → r j ∈ Set.Icc 0 1)
    (htail : ∀ j, d ≤ j → j < n → r j ≤ p)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    cubeEntropy n (varyingNoise r n f) ≤
      headFactor n d * average n f + p * cubeEntropy n f := by
  induction n with
  | zero => simp [varyingNoise, cubeEntropy, average, headFactor]
  | succ n ih =>
      let fp := fun x => f (false, x)
      let fm := fun x => f (true, x)
      have hfp : ∀ x, 0 ≤ fp x := fun x => hf (false, x)
      have hfm : ∀ x, 0 ≤ fm x := fun x => hf (true, x)
      have hn := hr n (by omega)
      have hprev : ∀ j, j < n → r j ∈ Set.Icc 0 1 := fun j hj => hr j (by omega)
      have htprev : ∀ j, d ≤ j → j < n → r j ≤ p := fun j hj hjn => htail j hj (by omega)
      have hplus := ih hprev htprev (plusSlice (r n) f) (plusSlice_nonneg _ f hf hn.1 hn.2)
      have hminus := ih hprev htprev (minusSlice (r n) f) (minusSlice_nonneg _ f hf hn.1 hn.2)
      have hcplus := cubeEntropy_convex n fp fm hfp hfm
        ((1 + r n) / 2) ((1 - r n) / 2) (by linarith [hn.1]) (by linarith [hn.2]) (by ring)
      have hcminus := cubeEntropy_convex n fp fm hfp hfm
        ((1 - r n) / 2) ((1 + r n) / 2) (by linarith [hn.2]) (by linarith [hn.1]) (by ring)
      change cubeEntropy n (plusSlice (r n) f) ≤ _ at hcplus
      change cubeEntropy n (minusSlice (r n) f) ≤ _ at hcminus
      have hcsum : cubeEntropy n (plusSlice (r n) f) + cubeEntropy n (minusSlice (r n) f) ≤
          cubeEntropy n fp + cubeEntropy n fm := by linarith
      have hscaled := mul_le_mul_of_nonneg_left hcsum hp
      have hmass : average n (plusSlice (r n) f) + average n (minusSlice (r n) f) =
          2 * average (n + 1) f := by
        rw [average_plusSlice, average_minusSlice]
        change _ = 2 * ((average n fp + average n fm) / 2)
        ring
      have hE : (cubeEntropy n (varyingNoise r n (plusSlice (r n) f)) +
          cubeEntropy n (varyingNoise r n (minusSlice (r n) f))) / 2 ≤
          headFactor n d * average (n + 1) f + p * (cubeEntropy n fp + cubeEntropy n fm) / 2 := by
        have hmass' := congrArg (fun t => headFactor n d * t) hmass
        nlinarith
      have hgap0 := binaryGap_nonneg (average n fp) (average n fm)
        (average_nonneg n hfp) (average_nonneg n hfm)
      rw [cubeEntropy_chain, varyingNoise_false, varyingNoise_true,
        average_varyingNoise, average_varyingNoise, cubeEntropy_chain]
      by_cases hdn : d ≤ n
      · have hcount : headFactor (n + 1) d = headFactor n d := by
          simp only [headFactor, Nat.min_eq_left hdn, Nat.min_eq_left (by omega : d ≤ n + 1)]
        have hbinary := binaryGap_noise_le (average n fp) (average n fm) (r n)
          (average_nonneg n hfp) (average_nonneg n hfm) hn.1 hn.2
        have hbinary' := mul_le_mul_of_nonneg_right (htail n hdn (by omega)) hgap0
        rw [average_plusSlice, average_minusSlice, hcount]
        nlinarith
      · have hnd : n < d := by omega
        have hcount : headFactor (n + 1) d = headFactor n d + Real.log 2 := by
          simp only [headFactor, Nat.min_eq_right hnd.le,
            Nat.min_eq_right (by omega : n + 1 ≤ d), Nat.cast_add, Nat.cast_one]
          ring
        have hbinary := binaryGap_le_mass_log_two
          (average n (plusSlice (r n) f)) (average n (minusSlice (r n) f))
          (average_nonneg n (plusSlice_nonneg _ f hf hn.1 hn.2))
          (average_nonneg n (minusSlice_nonneg _ f hf hn.1 hn.2))
        have hbinary' : binaryGap (average n (plusSlice (r n) f))
            (average n (minusSlice (r n) f)) ≤ Real.log 2 * average (n + 1) f := by
          rw [hmass] at hbinary
          nlinarith
        have hgapScaled := mul_nonneg hp hgap0
        rw [hcount]
        nlinarith

theorem cubeEntropy_varyingNoise_le (r : ℕ → ℝ) (p : ℝ) (hp : 0 ≤ p) (d n : ℕ)
    (hr : ∀ j, j < n → r j ∈ Set.Icc 0 1)
    (htail : ∀ j, d ≤ j → j < n → r j ≤ p)
    (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    cubeEntropy n (varyingNoise r n f) ≤
      (d : ℝ) * Real.log 2 * average n f + p * cubeEntropy n f := by
  apply (cubeEntropy_varyingNoise_head_tail_le r p hp d n hr htail f hf).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (average_nonneg n hf)
  change (min d n : ℕ) * Real.log 2 ≤ (d : ℝ) * Real.log 2
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.min_le_left d n)
    (Real.log_nonneg (by norm_num))

end PL1CD.Entropy
