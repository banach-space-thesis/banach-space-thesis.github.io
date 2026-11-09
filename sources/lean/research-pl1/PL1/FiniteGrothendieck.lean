import PL1.FiniteGrothendieckNormalization

/-! A dimension-independent real finite Grothendieck inequality with constant 128,
using concrete finite Rademacher moments, clipping at 8, and a bounded supremum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PL1.FiniteGrothendieck
open PL1.Bonami PL1.FiniteRademacherClipping

def form {r c d : ℕ} (a : Fin r → Fin c → ℝ)
    (u : Fin r → Fin d → ℝ) (v : Fin c → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * (∑ l, u i l * v j l)

def values {r c : ℕ} (a : Fin r → Fin c → ℝ) : Set ℝ :=
  {z | ∃ (d : ℕ) (u : Fin r → Fin d → ℝ) (v : Fin c → Fin d → ℝ),
    (∀ i, ∑ l, (u i l) ^ 2 ≤ 1) ∧ (∀ j, ∑ l, (v j l) ^ 2 ≤ 1) ∧ z = |form a u v|}

theorem zero_mem_values {r c : ℕ} (a : Fin r → Fin c → ℝ) : 0 ∈ values a := by
  refine ⟨0, fun _ _ => 0, fun _ _ => 0, ?_, ?_, ?_⟩ <;> simp [form]

theorem inner_le_one {d : ℕ} (u v : Fin d → ℝ)
    (hu : ∑ l, (u l)^2 ≤ 1) (hv : ∑ l, (v l)^2 ≤ 1) :
    |∑ l, u l * v l| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) u v
  have hv0 : 0 ≤ ∑ l, (v l)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hu hv0
  have ha := abs_nonneg (∑ l, u l * v l)
  rw [← sq_abs] at h
  nlinarith

theorem values_bddAbove {r c : ℕ} (a : Fin r → Fin c → ℝ) : BddAbove (values a) := by
  refine ⟨∑ i, ∑ j, |a i j|, ?_⟩
  rintro z ⟨d, u, v, hu, hv, rfl⟩
  calc
    |form a u v| ≤ ∑ i, |∑ j, a i j * (∑ l, u i l * v j l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j| := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, |a i j * (∑ l, u i l * v j l)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left (inner_le_one _ _ (hu i) (hv j))
            (abs_nonneg _)).trans_eq (mul_one _))

def bound {r c : ℕ} (a : Fin r → Fin c → ℝ) : ℝ := sSup (values a)

theorem bound_nonneg {r c : ℕ} (a : Fin r → Fin c → ℝ) : 0 ≤ bound a :=
  le_csSup (values_bddAbove a) (zero_mem_values a)

theorem form_le_bound {r c d : ℕ} (a : Fin r → Fin c → ℝ)
    (u : Fin r → Fin d → ℝ) (v : Fin c → Fin d → ℝ)
    (hu : ∀ i, ∑ l, (u i l)^2 ≤ 1) (hv : ∀ j, ∑ l, (v j l)^2 ≤ 1) :
    |form a u v| ≤ bound a :=
  le_csSup (values_bddAbove a) ⟨d, u, v, hu, hv, rfl⟩

def cubeForm {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ) : ℝ :=
  average n (fun x => ∑ i, ∑ j, a i j * (f i x * g j x))

theorem cubeForm_eq {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ) :
    cubeForm a n f g = form a (fun i => coordinates n (f i)) (fun j => coordinates n (g j)) := by
  simp only [cubeForm, form, average_sum, average_mul, coordinates_product]

theorem cubeForm_le_bound {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ)
    (hf : ∀ i, average n (fun x => (f i x)^2) ≤ 1)
    (hg : ∀ j, average n (fun x => (g j x)^2) ≤ 1) :
    |cubeForm a n f g| ≤ bound a := by
  rw [cubeForm_eq]
  exact form_le_bound a _ _ (by simpa only [coordinates_square] using hf)
    (by simpa only [coordinates_square] using hg)

theorem cubeForm_mul_left {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ) (t : ℝ) :
    cubeForm a n (fun i x => t * f i x) g = t * cubeForm a n f g := by
  simp only [cubeForm, ← average_mul, Finset.mul_sum]
  apply average_congr
  intro x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cubeForm_mul_right {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ) (t : ℝ) :
    cubeForm a n f (fun j x => t * g j x) = t * cubeForm a n f g := by
  simp only [cubeForm, ← average_mul, Finset.mul_sum]
  apply average_congr
  intro x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem cubeForm_clipping_le {r c : ℕ} (a : Fin r → Fin c → ℝ) (n : ℕ)
    (f : Fin r → Cube n → ℝ) (g : Fin c → Cube n → ℝ) (D : ℝ)
    (hscalar : ∀ (s : Fin r → ℝ) (t : Fin c → ℝ),
      (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ D)
    (hf : ∀ i, average n (fun x => (f i x)^2) ≤ 1)
    (hg : ∀ j, average n (fun x => (g j x)^2) ≤ 1)
    (hr : ∀ i, average n (fun x => (f i x - clipEight (f i x))^2) ≤ 1 / 16)
    (hs : ∀ j, average n (fun x => (g j x - clipEight (g j x))^2) ≤ 1 / 16) :
    |cubeForm a n f g| ≤ 64 * D + bound a / 2 := by
  let C : Fin r → Cube n → ℝ := fun i x => clipEight (f i x)
  let E : Fin c → Cube n → ℝ := fun j x => clipEight (g j x)
  let R : Fin r → Cube n → ℝ := fun i x => f i x - C i x
  let S : Fin c → Cube n → ℝ := fun j x => g j x - E j x
  have hC (i) : average n (fun x => (C i x)^2) ≤ 1 :=
    (average_mono n (fun x => clipEight_sq_le (f i x))).trans (hf i)
  have hR (i) : average n (fun x => (4 * R i x)^2) ≤ 1 := by
    have he : (fun x => (4 * R i x)^2) = (fun x => 16 * (R i x)^2) := by funext x; ring
    rw [he, average_mul]
    have hh := hr i
    change average n (fun x => (R i x)^2) ≤ 1 / 16 at hh
    linarith
  have hS (j) : average n (fun x => (4 * S j x)^2) ≤ 1 := by
    have he : (fun x => (4 * S j x)^2) = (fun x => 16 * (S j x)^2) := by funext x; ring
    rw [he, average_mul]
    have hh := hs j
    change average n (fun x => (S j x)^2) ≤ 1 / 16 at hh
    linarith
  have hresL : |cubeForm a n R g| ≤ bound a / 4 := by
    have h := cubeForm_le_bound a n (fun i x => 4 * R i x) g hR hg
    rw [cubeForm_mul_left, abs_mul] at h
    norm_num at h
    linarith
  have hresR : |cubeForm a n C S| ≤ bound a / 4 := by
    have h := cubeForm_le_bound a n C (fun j x => 4 * S j x) hC hS
    rw [cubeForm_mul_right, abs_mul] at h
    norm_num at h
    linarith
  have hclip : |cubeForm a n C E| ≤ 64 * D := by
    apply abs_average_le
    intro x
    have hc (z : ℝ) : |clipEight z / 8| ≤ 1 := by
      rw [abs_div]
      norm_num
      exact (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr (abs_clipEight_le z)
    have h := hscalar (fun i => C i x / 8) (fun j => E j x / 8)
      (fun i => hc (f i x)) (fun j => hc (g j x))
    have he : (∑ i, ∑ j, a i j * (C i x * E j x)) =
        64 * (∑ i, ∑ j, a i j * (C i x / 8) * (E j x / 8)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, abs_mul]
    norm_num
    nlinarith
  have he : cubeForm a n f g = cubeForm a n C E + cubeForm a n R g + cubeForm a n C S := by
    simp only [cubeForm, ← average_add, ← Finset.sum_add_distrib]
    apply average_congr
    intro x
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [R, S]
    ring
  rw [he]
  calc
    _ ≤ |cubeForm a n C E + cubeForm a n R g| + |cubeForm a n C S| := abs_add_le _ _
    _ ≤ (|cubeForm a n C E| + |cubeForm a n R g|) + |cubeForm a n C S| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 64 * D + bound a / 2 := by linarith

theorem form_clipping_le {r c d : ℕ} (a : Fin r → Fin c → ℝ)
    (u : Fin r → Fin d → ℝ) (v : Fin c → Fin d → ℝ) (D : ℝ)
    (hu : ∀ i, ∑ l, (u i l)^2 ≤ 1) (hv : ∀ j, ∑ l, (v j l)^2 ≤ 1)
    (hscalar : ∀ (s : Fin r → ℝ) (t : Fin c → ℝ),
      (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ D) :
    |form a u v| ≤ 64 * D + bound a / 2 := by
  let f := fun i => rademacherSum d (finExtend (u i))
  let g := fun j => rademacherSum d (finExtend (v j))
  have hf i : energy d (finExtend (u i)) ≤ 1 := by rw [energy_extend]; exact hu i
  have hg j : energy d (finExtend (v j)) ≤ 1 := by rw [energy_extend]; exact hv j
  have he : cubeForm a d f g = form a u v := by
    simp only [cubeForm, form, f, g, average_sum, average_mul, mixed_extend]
  rw [← he]
  exact cubeForm_clipping_le a d f g D hscalar
    (fun i => by dsimp [f]; rw [second_moment]; exact hf i)
    (fun j => by dsimp [g]; rw [second_moment]; exact hg j)
    (fun i => residual_second_moment_le d _ (hf i))
    (fun j => residual_second_moment_le d _ (hg j))

theorem bound_le {r c : ℕ} (a : Fin r → Fin c → ℝ) (D : ℝ)
    (hscalar : ∀ (s : Fin r → ℝ) (t : Fin c → ℝ),
      (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) →
      |∑ i, ∑ j, a i j * s i * t j| ≤ D) : bound a ≤ 128 * D := by
  have h : bound a ≤ 64 * D + bound a / 2 := by
    apply csSup_le ⟨0, zero_mem_values a⟩
    rintro z ⟨d, u, v, hu, hv, rfl⟩
    exact form_clipping_le a u v D hu hv hscalar
  linarith

end PL1.FiniteGrothendieck

namespace PL1.FiniteSumming
open PL1.FiniteGrothendieck

theorem matrixGrothendieckWith_128 : MatrixGrothendieckWith 128 := by
  refine ⟨by norm_num, ?_⟩
  intro r c d a u v D hu hv hscalar
  exact (form_le_bound a u v hu hv).trans (bound_le a D hscalar)

theorem twoSumming_128 (d k : ℕ) (T : (Fin d → ℝ) →L[ℝ] EllOne k) :
    PL1.ComplementedLattice.TwoSummingWith T (128 * ‖T‖) :=
  twoSumming_of_matrix matrixGrothendieckWith_128 d k T

theorem oneSumming_128 (d k : ℕ) (S : EllOne d →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    PL1.ComplementedLattice.OneSummingWith S (128 * ‖S‖) :=
  oneSumming_of_matrix matrixGrothendieckWith_128 d k S

#print axioms matrixGrothendieckWith_128
#print axioms twoSumming_128
#print axioms oneSumming_128
end PL1.FiniteSumming



