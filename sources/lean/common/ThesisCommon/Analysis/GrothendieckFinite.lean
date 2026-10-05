import ThesisCommon.Analysis.GrothendieckClipping
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A dimension-independent real Grothendieck inequality, with the deliberately
non-optimal constant 128.  The proof uses finite signs and truncation only. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.Grothendieck

variable {I J : Type*} [Fintype I] [Fintype J]

def form (A : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * y j

def hilbertValues (A : I → J → ℝ) : Set ℝ :=
  {z | ∃ (n : ℕ) (x : I → Fin n → ℝ) (y : J → Fin n → ℝ),
    (∀ i, ∑ k, x i k ^ 2 ≤ 1) ∧ (∀ j, ∑ k, y j k ^ 2 ≤ 1) ∧
    z = |∑ i, ∑ j, A i j * ∑ k, x i k * y j k|}

def hilbertBound (A : I → J → ℝ) : ℝ := sSup (hilbertValues A)

theorem zero_mem_hilbertValues (A : I → J → ℝ) : 0 ∈ hilbertValues A := by
  refine ⟨0, (fun _ _ => 0), (fun _ _ => 0), ?_, ?_, ?_⟩ <;> simp

theorem hilbertValues_bddAbove (A : I → J → ℝ) : BddAbove (hilbertValues A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro z ⟨n,x,y,hx,hy,rfl⟩
  calc
    |∑ i, ∑ j, A i j * ∑ k, x i k * y j k| ≤
        ∑ i, ∑ j, |A i j * ∑ k, x i k * y j k| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (x i) (y j)
      have hnx : 0 ≤ ∑ k, x i k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      have hny : 0 ≤ ∑ k, y j k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      have hprod : (∑ k, x i k ^ 2) * (∑ k, y j k ^ 2) ≤ 1 := by
        exact (mul_le_mul (hx i) (hy j) hny (by norm_num)).trans_eq (by norm_num)
      have hab : |∑ k, x i k * y j k| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hab (abs_nonneg _)).trans_eq (mul_one _)

theorem hilbertBound_nonneg (A : I → J → ℝ) : 0 ≤ hilbertBound A :=
  le_csSup (hilbertValues_bddAbove A) (zero_mem_hilbertValues A)

theorem configuration_le_hilbertBound (A : I → J → ℝ) {n : ℕ}
    (x : I → Fin n → ℝ) (y : J → Fin n → ℝ)
    (hx : ∀ i, ∑ k, x i k ^ 2 ≤ 1) (hy : ∀ j, ∑ k, y j k ^ 2 ≤ 1) :
    |∑ i, ∑ j, A i j * ∑ k, x i k * y j k| ≤ hilbertBound A :=
  le_csSup (hilbertValues_bddAbove A) ⟨n,x,y,hx,hy,rfl⟩

section ReindexMean
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def meanCoordinates (f : Ω → ℝ) : Fin (Fintype.card Ω) → ℝ :=
  fun k => Real.sqrt (Fintype.card Ω : ℝ)⁻¹ * f ((Fintype.equivFin Ω).symm k)

theorem meanCoordinates_dot (f g : Ω → ℝ) :
    (∑ k, meanCoordinates f k * meanCoordinates g k) = mean (fun ω => f ω * g ω) := by
  have hroot : Real.sqrt (Fintype.card Ω : ℝ)⁻¹ ^ 2 = (Fintype.card Ω : ℝ)⁻¹ :=
    Real.sq_sqrt (by positivity)
  have hterm (k : Fin (Fintype.card Ω)) : meanCoordinates f k * meanCoordinates g k =
      (Fintype.card Ω : ℝ)⁻¹ *
        (f ((Fintype.equivFin Ω).symm k) * g ((Fintype.equivFin Ω).symm k)) := by
    dsimp [meanCoordinates]
    calc
      _ = (Real.sqrt (Fintype.card Ω : ℝ)⁻¹ ^ 2) *
        (f ((Fintype.equivFin Ω).symm k) * g ((Fintype.equivFin Ω).symm k)) := by ring
      _ = _ := by rw [hroot]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin Ω).symm _ _ (fun _ => rfl)

theorem meanCoordinates_sq (f : Ω → ℝ) :
    (∑ k, meanCoordinates f k ^ 2) = mean (fun ω => f ω ^ 2) := by
  simpa only [pow_two] using meanCoordinates_dot f f

theorem mean_form (A : I → J → ℝ) (x : I → Ω → ℝ) (y : J → Ω → ℝ) :
    mean (fun ω => form A (fun i => x i ω) (fun j => y j ω)) =
      ∑ i, ∑ j, A i j * mean (fun ω => x i ω * y j ω) := by
  unfold form
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [mul_assoc] using mean_mul_left (A i j) (fun ω => x i ω * y j ω)

theorem mean_form_le_hilbertBound (A : I → J → ℝ) (x : I → Ω → ℝ) (y : J → Ω → ℝ)
    (hx : ∀ i, mean (fun ω => x i ω ^ 2) ≤ 1)
    (hy : ∀ j, mean (fun ω => y j ω ^ 2) ≤ 1) :
    |mean (fun ω => form A (fun i => x i ω) (fun j => y j ω))| ≤ hilbertBound A := by
  have h := configuration_le_hilbertBound A (fun i => meanCoordinates (x i))
    (fun j => meanCoordinates (y j))
    (by simpa only [meanCoordinates_sq] using hx)
    (by simpa only [meanCoordinates_sq] using hy)
  simpa only [meanCoordinates_dot, mean_form] using h

theorem mean_form_quarter_left (A : I → J → ℝ) (x : I → Ω → ℝ) (y : J → Ω → ℝ)
    (hx : ∀ i, mean (fun ω => x i ω ^ 2) ≤ (1/4 : ℝ)^2)
    (hy : ∀ j, mean (fun ω => y j ω ^ 2) ≤ 1) :
    |mean (fun ω => form A (fun i => x i ω) (fun j => y j ω))| ≤
      (1/4 : ℝ) * hilbertBound A := by
  have hx' (i : I) : mean (fun ω => (4 * x i ω) ^ 2) ≤ 1 := by
    have heq : (fun ω => (4 * x i ω) ^ 2) = (fun ω => 16 * x i ω ^ 2) := by funext ω; ring
    rw [heq, mean_mul_left]
    have := hx i
    linarith
  have h := mean_form_le_hilbertBound A (fun i ω => 4 * x i ω) y hx' hy
  have heq : (fun ω => form A (fun i => 4 * x i ω) (fun j => y j ω)) =
      (fun ω => 4 * form A (fun i => x i ω) (fun j => y j ω)) := by
    funext ω
    simp only [form, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, mean_mul_left, abs_mul] at h
  norm_num at h
  linarith

theorem mean_form_quarter_right (A : I → J → ℝ) (x : I → Ω → ℝ) (y : J → Ω → ℝ)
    (hx : ∀ i, mean (fun ω => x i ω ^ 2) ≤ 1)
    (hy : ∀ j, mean (fun ω => y j ω ^ 2) ≤ (1/4 : ℝ)^2) :
    |mean (fun ω => form A (fun i => x i ω) (fun j => y j ω))| ≤
      (1/4 : ℝ) * hilbertBound A := by
  have hy' (j : J) : mean (fun ω => (4 * y j ω) ^ 2) ≤ 1 := by
    have heq : (fun ω => (4 * y j ω) ^ 2) = (fun ω => 16 * y j ω ^ 2) := by funext ω; ring
    rw [heq, mean_mul_left]
    have := hy j
    linarith
  have h := mean_form_le_hilbertBound A x (fun j ω => 4 * y j ω) hx hy'
  have heq : (fun ω => form A (fun i => x i ω) (fun j => 4 * y j ω)) =
      (fun ω => 4 * form A (fun i => x i ω) (fun j => y j ω)) := by
    funext ω
    simp only [form, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, mean_mul_left, abs_mul] at h
  norm_num at h
  linarith

end ReindexMean

theorem configuration_clipping_bound (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ (a : I → ℝ) (b : J → ℝ), (∀ i, |a i| ≤ 1) →
      (∀ j, |b j| ≤ 1) → |form A a b| ≤ B)
    {n : ℕ} (x : I → Fin n → ℝ) (y : J → Fin n → ℝ)
    (hx : ∀ i, ∑ k, x i k ^ 2 ≤ 1) (hy : ∀ j, ∑ k, y j k ^ 2 ≤ 1) :
    |∑ i, ∑ j, A i j * ∑ k, x i k * y j k| ≤ 64 * B + hilbertBound A / 2 := by
  let X : I → (Fin n → Bool) → ℝ := fun i => rademacher (x i)
  let Y : J → (Fin n → Bool) → ℝ := fun j => rademacher (y j)
  have hX := fun i => clipped_rademacher_bounds (x i) (hx i)
  have hY := fun j => clipped_rademacher_bounds (y j) (hy j)
  have hCpoint (ε : Fin n → Bool) : |form A (fun i => clip (X i ε)) (fun j => clip (Y j ε))| ≤ 64 * B := by
    have h := hB (fun i => clip (X i ε) / 8) (fun j => clip (Y j ε) / 8)
      (fun i => by rw [abs_div]; norm_num; exact (div_le_one (by norm_num)).mpr (abs_clip_le _))
      (fun j => by rw [abs_div]; norm_num; exact (div_le_one (by norm_num)).mpr (abs_clip_le _))
    have heq : form A (fun i => clip (X i ε)) (fun j => clip (Y j ε)) =
        64 * form A (fun i => clip (X i ε) / 8) (fun j => clip (Y j ε) / 8) := by
      simp only [form, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, abs_mul]
    norm_num
    linarith
  have hC : |mean (fun ε => form A (fun i => clip (X i ε)) (fun j => clip (Y j ε)))| ≤ 64 * B := by
    rw [abs_le]
    constructor
    · have h := mean_mono fun ε => (abs_le.mp (hCpoint ε)).1
      simpa only [mean_const] using h
    · have h := mean_mono fun ε => (abs_le.mp (hCpoint ε)).2
      simpa only [mean_const] using h
  have hL := mean_form_quarter_left A (fun i ε => X i ε - clip (X i ε)) Y
    (fun i => (hX i).2.2) (fun j => (hY j).1)
  have hR := mean_form_quarter_right A (fun i ε => clip (X i ε))
    (fun j ε => Y j ε - clip (Y j ε)) (fun i => (hX i).2.1) (fun j => (hY j).2.2)
  have hdecomp (ε : Fin n → Bool) : form A (fun i => X i ε) (fun j => Y j ε) =
      form A (fun i => clip (X i ε)) (fun j => clip (Y j ε)) +
      form A (fun i => X i ε - clip (X i ε)) (fun j => Y j ε) +
      form A (fun i => clip (X i ε)) (fun j => Y j ε - clip (Y j ε)) := by
    simp only [form, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hid : mean (fun ε => form A (fun i => X i ε) (fun j => Y j ε)) =
      ∑ i, ∑ j, A i j * ∑ k, x i k * y j k := by
    rw [mean_form]
    simp only [X, Y, rademacher_covariance]
  rw [← hid]
  simp_rw [hdecomp]
  rw [mean_add, mean_add]
  have htri := (abs_add_le
    (mean (fun ε => form A (fun i => clip (X i ε)) (fun j => clip (Y j ε))) +
     mean (fun ε => form A (fun i => X i ε - clip (X i ε)) (fun j => Y j ε)))
    (mean (fun ε => form A (fun i => clip (X i ε)) (fun j => Y j ε - clip (Y j ε)))))
  have htri' := abs_add_le
    (mean (fun ε => form A (fun i => clip (X i ε)) (fun j => clip (Y j ε))))
    (mean (fun ε => form A (fun i => X i ε - clip (X i ε)) (fun j => Y j ε)))
  linarith

/-- A real Grothendieck bound uniform in the size of the matrix and in the
dimension of the Hilbert vectors. -/
theorem finite_grothendieck (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ (a : I → ℝ) (b : J → ℝ), (∀ i, |a i| ≤ 1) →
      (∀ j, |b j| ≤ 1) → |form A a b| ≤ B)
    {n : ℕ} (x : I → Fin n → ℝ) (y : J → Fin n → ℝ)
    (hx : ∀ i, ∑ k, x i k ^ 2 ≤ 1) (hy : ∀ j, ∑ k, y j k ^ 2 ≤ 1) :
    |∑ i, ∑ j, A i j * ∑ k, x i k * y j k| ≤ 128 * B := by
  have hs : hilbertBound A ≤ 64 * B + hilbertBound A / 2 := by
    apply csSup_le ⟨0, zero_mem_hilbertValues A⟩
    rintro z ⟨m,u,v,hu,hv,rfl⟩
    exact configuration_clipping_bound A B hB u v hu hv
  have hg : hilbertBound A ≤ 128 * B := by linarith
  exact (configuration_le_hilbertBound A x y hx hy).trans hg

end ThesisCommon.Grothendieck
