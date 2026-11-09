import PL1.BonamiTwoPoint
import PL1.BonamiTensorization
import PL1.NoiseSemigroup

/-! # Finite cubes inside the actual Haar sign group

The normalized finite-cube average is derived from Haar invariance under
coordinate flips. No independent-product description of Haar is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ENNReal

namespace PL1.Bonami
open Walsh

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := cubeFintype n; inferInstanceAs (Fintype (Bool × Cube n))

instance cubeTopologicalSpace : (n : ℕ) → TopologicalSpace (Cube n)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | n + 1 => letI := cubeTopologicalSpace n
             inferInstanceAs (TopologicalSpace (Bool × Cube n))

instance cubeDiscreteTopology : (n : ℕ) → DiscreteTopology (Cube n)
  | 0 => inferInstanceAs (DiscreteTopology Unit)
  | n + 1 => letI := cubeDiscreteTopology n
             inferInstanceAs (DiscreteTopology (Bool × Cube n))

def signBit (a : Sign) : Bool := decide (a.toAdd ≠ 0)

theorem signValue_eq_bit (a : Sign) : signValue a = if signBit a then -1 else 1 := by
  by_cases ha : a.toAdd = 0 <;> simp [signBit, signValue, ha]

/-- Read the first n sign coordinates, with the newest coordinate first. -/
def sample : (n : ℕ) → Walsh.Group → Cube n
  | 0, _ => ()
  | n + 1, x => (signBit (x n), sample n x)

theorem continuous_sample (n : ℕ) : Continuous (sample n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_of_discreteTopology : Continuous signBit).comp
      (continuous_apply n)).prodMk ih

def liftContinuous (n : ℕ) (f : Cube n → ℝ) : C(Walsh.Group, ℝ) :=
  ⟨fun x => f (sample n x), continuous_of_discreteTopology.comp (continuous_sample n)⟩

theorem continuous_lift (n : ℕ) (f : Cube n → ℝ) :
    Continuous (fun x => f (sample n x)) := (liftContinuous n f).continuous

theorem integrable_lift (n : ℕ) (f : Cube n → ℝ) (μ : Measure Walsh.Group)
    [IsFiniteMeasure μ] : Integrable (fun x => f (sample n x)) μ :=
  (continuous_lift n f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sample_congr (n : ℕ) {x y : Walsh.Group} (h : ∀ j < n, x j = y j) :
    sample n x = sample n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sample, h n (Nat.lt_succ_self n), ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem sample_flip (n : ℕ) (x : Walsh.Group) : sample n (flip n * x) = sample n x := by
  apply sample_congr
  intro j hj
  simp [Walsh.flip, Pi.mul_apply, Function.update_of_ne (Nat.ne_of_lt hj)]

theorem integral_sign_mul_lift (n : ℕ) (f : Cube n → ℝ) :
    ∫ x, signValue (x n) * f (sample n x) ∂haar = 0 := by
  apply integral_eq_zero_of_mul_left_eq_neg (g := flip n)
  intro x
  rw [sample_flip, Pi.mul_apply, signValue_mul]
  norm_num [Walsh.flip, signValue]
  split_ifs <;> ring

theorem lift_succ (n : ℕ) (f : Cube (n + 1) → ℝ) (x : Walsh.Group) :
    f (sample (n + 1) x) = meanSlice f (sample n x) +
      signValue (x n) * diffSlice f (sample n x) := by
  rw [signValue_eq_bit]
  cases h : signBit (x n) <;> simp [sample, h, meanSlice, diffSlice] <;> ring

/-- Haar expectation of every finite-coordinate function is its normalized cube average. -/
theorem integral_lift (n : ℕ) (f : Cube n → ℝ) :
    ∫ x, f (sample n x) ∂haar = average n f := by
  induction n with
  | zero => simp [sample, average]
  | succ n ih =>
    have hf : Integrable (fun x : Walsh.Group => signValue (x n) * diffSlice f (sample n x)) haar :=
      (((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply n)).mul
        (continuous_lift n (diffSlice f))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    simp_rw [lift_succ]
    rw [integral_add (integrable_lift n _ haar) hf, integral_sign_mul_lift, add_zero, ih]
    change average n (fun x => (f (false, x) + f (true, x)) / 2) = _
    simp only [average, div_eq_mul_inv]
    rw [show (fun x : Cube n => (f (false, x) + f (true, x)) * 2⁻¹) =
      (fun x => 2⁻¹ * (f (false, x) + f (true, x))) by funext x; ring,
      average_mul, average_add]
    ring

/-- A finite-cube Walsh character; coordinates outside the cube are ignored. -/
def cubeCharacter : (n : ℕ) → Finset ℕ → Cube n → ℝ
  | 0, _, _ => 1
  | n + 1, F, x => (if n ∈ F then (if x.1 then -1 else 1) else 1) *
      cubeCharacter n (F.erase n) x.2

private theorem erase_subset_range {n : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range (n + 1)) :
    F.erase n ⊆ Finset.range n := by
  intro j hj
  obtain ⟨hjn, hjF⟩ := Finset.mem_erase.mp hj
  have hjlt := Finset.mem_range.mp (hF hjF)
  exact Finset.mem_range.mpr (by omega)

theorem cubeCharacter_sample (n : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.range n)
    (x : Walsh.Group) : cubeCharacter n F (sample n x) = character F x := by
  induction n generalizing F with
  | zero =>
    have hF0 : F = ∅ := Finset.subset_empty.mp (by simpa using hF)
    simp [hF0, cubeCharacter]
  | succ n ih =>
    have he := erase_subset_range hF
    by_cases hn : n ∈ F
    · have hc : character F x = signValue (x n) * character (F.erase n) x := by
        conv_lhs => rw [← Finset.insert_erase hn]
        rw [character, Finset.prod_insert (Finset.notMem_erase n F)]
        rfl
      simp only [cubeCharacter, hn, ↓reduceIte, sample, ih (F.erase n) he, hc,
        signValue_eq_bit]
    · simpa [cubeCharacter, hn, sample, Finset.erase_eq_of_notMem hn] using
        ih (F.erase n) he

theorem noise_cubeCharacter (ρ : ℝ) (n : ℕ) (F : Finset ℕ)
    (hF : F ⊆ Finset.range n) (x : Cube n) :
    noise ρ n (cubeCharacter n F) x = ρ ^ F.card * cubeCharacter n F x := by
  induction n generalizing F with
  | zero =>
    have hF0 : F = ∅ := Finset.subset_empty.mp (by simpa using hF)
    simp [hF0, cubeCharacter, noise]
  | succ n ih =>
    have he := erase_subset_range hF
    by_cases hn : n ∈ F
    · have hm : meanSlice (cubeCharacter (n + 1) F) = fun _ => 0 := by
        funext y
        simp [meanSlice, cubeCharacter, hn]
      have hd : diffSlice (cubeCharacter (n + 1) F) = cubeCharacter n (F.erase n) := by
        funext y
        simp [diffSlice, cubeCharacter, hn]
      have hcard : F.card = (F.erase n).card + 1 := (Finset.card_erase_add_one hn).symm
      rw [noise, hm, hd, noise_zero]
      simp only [zero_add, ih (F.erase n) he, cubeCharacter, hn, ↓reduceIte, hcard, pow_succ]
      cases x.1 <;> simp <;> ring
    · have hm : meanSlice (cubeCharacter (n + 1) F) = cubeCharacter n (F.erase n) := by
        funext y
        simp [meanSlice, cubeCharacter, hn]
      have hd : diffSlice (cubeCharacter (n + 1) F) = fun _ => 0 := by
        funext y
        simp [diffSlice, cubeCharacter, hn]
      rw [noise, hm, hd, noise_zero]
      simp only [mul_zero, add_zero]
      rw [ih (F.erase n) he]
      simp only [
        cubeCharacter, hn, ↓reduceIte, one_mul,
        Finset.erase_eq_of_notMem hn]

/-- Dimension-independent noise estimate for actual finite Walsh sums on Haar. -/
theorem finite_walsh_sum_bound (p ρ : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hρ : ρ ^ 2 ≤ p - 1) (s : Finset (Finset ℕ)) (c : Finset ℕ → ℝ) :
    (∫ x, (∑ F ∈ s, c F * ρ ^ F.card * character F x) ^ 2 ∂haar) ≤
      (∫ x, |∑ F ∈ s, c F * character F x| ^ p ∂haar) ^ (2 / p) := by
  classical
  let n := s.sup (fun F => F.sup id + 1)
  have hF : ∀ F ∈ s, F ⊆ Finset.range n := by
    intro F hFs j hj
    apply Finset.mem_range.mpr
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
      (Finset.le_sup (f := fun F : Finset ℕ => F.sup id + 1) hFs)
  let f : Cube n → ℝ := fun y => ∑ F ∈ s, c F * cubeCharacter n F y
  have hlift (x : Walsh.Group) : f (sample n x) = ∑ F ∈ s, c F * character F x := by
    apply Finset.sum_congr rfl
    intro F hFs
    rw [cubeCharacter_sample n F (hF F hFs)]
  have hnoise (x : Walsh.Group) : noise ρ n f (sample n x) =
      ∑ F ∈ s, c F * ρ ^ F.card * character F x := by
    dsimp only [f]
    rw [noise_sum]
    apply Finset.sum_congr rfl
    intro F hFs
    rw [noise_mul]
    change c F * noise ρ n (cubeCharacter n F) (sample n x) = _
    rw [noise_cubeCharacter ρ n F (hF F hFs), cubeCharacter_sample n F (hF F hFs)]
    ring
  calc
    _ = ∫ x, noise ρ n f (sample n x) ^ 2 ∂haar := by simp_rw [hnoise]
    _ = average n (fun y => noise ρ n f y ^ 2) :=
      integral_lift n (fun y => noise ρ n f y ^ 2)
    _ ≤ moment n p f ^ (2 / p) := noise_moment_bound_sharp hp hp2 hρ n f
    _ = _ := by
      congr 1
      rw [moment, ← integral_lift]
      simp_rw [hlift]

#print axioms integral_lift
#print axioms finite_walsh_sum_bound

/-- The same bound in the exponential eigenvalue normalization of the actual noise semigroup. -/
theorem finite_walsh_exp_sum_bound (p u : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hu : (Real.exp (-u)) ^ 2 ≤ p - 1) (s : Finset (Finset ℕ)) (c : Finset ℕ → ℝ) :
    (∫ x, (∑ F ∈ s, c F * Real.exp (-u * F.card) * character F x) ^ 2 ∂haar) ≤
      (∫ x, |∑ F ∈ s, c F * character F x| ^ p ∂haar) ^ (2 / p) := by
  have h := finite_walsh_sum_bound p (Real.exp (-u)) hp hp2 hu s c
  have he (F : Finset ℕ) : Real.exp (-u) ^ F.card = Real.exp (-u * F.card) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [he] using h

#print axioms finite_walsh_exp_sum_bound

end PL1.Bonami
