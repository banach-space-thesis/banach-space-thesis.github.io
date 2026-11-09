import PL1.FiniteSummingFromMatrix
import PL1.FiniteRademacherClipping
import PL1.BonamiHaarBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PL1.FiniteGrothendieck
open PL1.Bonami PL1.FiniteRademacherClipping

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Cube n) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

theorem average_eq_sum (n : ℕ) (f : Cube n → ℝ) :
    average n f = (∑ x, f x) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [average, Cube]
  | succ n ih =>
    change (average n (fun x => f (false, x)) + average n (fun x => f (true, x))) / 2 = _
    rw [ih, ih]
    change _ = (∑ x : Bool × Cube n, f x) / _
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, pow_succ]
    ring

def finExtend {n : ℕ} (a : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then a ⟨j, h⟩ else 0

theorem energy_extend {n : ℕ} (a : Fin n → ℝ) :
    energy n (finExtend a) = ∑ j, (a j) ^ 2 := by
  unfold energy
  rw [Finset.sum_range]
  simp [finExtend]

theorem mixed_extend {n : ℕ} (a b : Fin n → ℝ) :
    average n (fun x => rademacherSum n (finExtend a) x * rademacherSum n (finExtend b) x) =
      ∑ j, a j * b j := by
  rw [mixed_second_moment, Finset.sum_range]
  simp [finExtend]

def coordinates (n : ℕ) (f : Cube n → ℝ) : Fin (Fintype.card (Cube n)) → ℝ :=
  fun i => f ((Fintype.equivFin (Cube n)).symm i) / Real.sqrt ((2 : ℝ) ^ n)

theorem coordinates_product (n : ℕ) (f g : Cube n → ℝ) :
    (∑ i, coordinates n f i * coordinates n g i) = average n (fun x => f x * g x) := by
  simp only [coordinates, div_mul_div_comm]
  rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  rw [← Finset.sum_div, (Fintype.equivFin (Cube n)).symm.sum_comp (fun x => f x * g x)]
  exact (average_eq_sum n _).symm

theorem coordinates_square (n : ℕ) (f : Cube n → ℝ) :
    (∑ i, coordinates n f i ^ 2) = average n (fun x => f x ^ 2) := by
  simpa only [pow_two] using coordinates_product n f f

theorem average_sum {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → Cube n → ℝ) :
    average n (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, average n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem abs_average_le (n : ℕ) (f : Cube n → ℝ) (B : ℝ)
    (h : ∀ x, |f x| ≤ B) : |average n f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have hh := average_mono n (fun x => (abs_le.mp (h x)).1)
    simpa using hh
  · have hh := average_mono n (fun x => (abs_le.mp (h x)).2)
    simpa using hh

end PL1.FiniteGrothendieck


