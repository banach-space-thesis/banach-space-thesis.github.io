import ThesisCommon.Analysis.GrothendieckFinite
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite operator consequences of the proved Grothendieck inequality. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.Grothendieck

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem euclidean_norm_sq (x : EuclideanSpace ℝ K) : ‖x‖ ^ 2 = ∑ k, x k ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

theorem euclidean_inner (x y : EuclideanSpace ℝ K) :
    inner ℝ x y = ∑ k, x k * y k := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem finite_grothendieck_euclidean (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ (a : I → ℝ) (b : J → ℝ), (∀ i, |a i| ≤ 1) →
      (∀ j, |b j| ≤ 1) → |form A a b| ≤ B)
    (x : I → EuclideanSpace ℝ K) (y : J → EuclideanSpace ℝ K)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * inner ℝ (x i) (y j)| ≤ 128 * B := by
  let e := (Fintype.equivFin K).symm
  have hreindex (f : K → ℝ) : (∑ k : Fin (Fintype.card K), f (e k)) = ∑ k, f k :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hx' (i : I) : ∑ k, x i (e k) ^ 2 ≤ 1 := by
    rw [hreindex (fun k => x i k ^ 2), ← euclidean_norm_sq]
    nlinarith [norm_nonneg (x i), hx i]
  have hy' (j : J) : ∑ k, y j (e k) ^ 2 ≤ 1 := by
    rw [hreindex (fun k => y j k ^ 2), ← euclidean_norm_sq]
    nlinarith [norm_nonneg (y j), hy j]
  have h := finite_grothendieck A B hB (fun i k => x i (e k))
    (fun j k => y j (e k)) hx' hy'
  have hinner (i : I) (j : J) : (∑ k, x i (e k) * y j (e k)) = inner ℝ (x i) (y j) :=
    (hreindex (fun k => x i k * y j k)).trans (euclidean_inner _ _).symm
  simpa only [hinner] using h

def normalized (x : EuclideanSpace ℝ K) : EuclideanSpace ℝ K := ‖x‖⁻¹ • x

theorem normalized_norm_le (x : EuclideanSpace ℝ K) : ‖normalized x‖ ≤ 1 := by
  by_cases h : x = 0
  · simp [normalized, h]
  · simp [normalized, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), norm_ne_zero_iff.mpr h]

theorem inner_normalized (x : EuclideanSpace ℝ K) : inner ℝ x (normalized x) = ‖x‖ := by
  by_cases h : x = 0
  · simp [normalized, h]
  · rw [normalized, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr h]

theorem scalar_form_le_of_column_bound (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → (∑ i, |∑ j, A i j * b j|) ≤ B)
    (a : I → ℝ) (b : J → ℝ) (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) :
    |form A a b| ≤ B := by
  have heq : form A a b = ∑ i, a i * ∑ j, A i j * b j := by
    simp only [form, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |a i * ∑ j, A i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |∑ j, A i j * b j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)).trans_eq (one_mul _)
    _ ≤ B := hB b hb

/-- The finite ell-one to Hilbert 1-summing estimate, for columns in the unit ball. -/
theorem finite_column_sum_norm_le (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → (∑ i, |∑ j, A i j * b j|) ≤ B)
    (u : I → EuclideanSpace ℝ K) (hu : ∀ i, ‖u i‖ ≤ 1) :
    (∑ j, ‖∑ i, A i j • u i‖) ≤ 128 * B := by
  let z : J → EuclideanSpace ℝ K := fun j => ∑ i, A i j • u i
  let v := fun j => normalized (z j)
  have h := finite_grothendieck_euclidean A B (scalar_form_le_of_column_bound A B hB)
    u v hu (fun j => normalized_norm_le (z j))
  have heq : (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) = ∑ j, ‖z j‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have h := inner_normalized (z j)
    simpa only [z, v, sum_inner, real_inner_smul_left] using h
  rw [heq, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
  exact h

/-- A finite collection of ell-one columns has a uniform square-sum bound
whenever every scalar combination with coefficients in [-1,1] is bounded. -/
theorem finite_column_l1_square_sum_le (A : I → J → ℝ) (B : ℝ)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → (∑ i, |∑ j, A i j * b j|) ≤ B) :
    (∑ j, (∑ i, |A i j|) ^ 2) ≤ (128 * B) ^ 2 := by
  classical
  let c : EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => ∑ i, |A i j|)
  let t := normalized c
  let u : I → EuclideanSpace ℝ J := fun i => WithLp.toLp 2
    (fun j => if 0 ≤ A i j then t j else -t j)
  let v : J → EuclideanSpace ℝ J := fun j => EuclideanSpace.single j 1
  have htu : ‖t‖ ≤ 1 := normalized_norm_le c
  have hu (i : I) : ‖u i‖ ≤ 1 := by
    have hsq : ‖u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [euclidean_norm_sq, euclidean_norm_sq]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u]
      split_ifs <;> ring
    nlinarith [norm_nonneg (u i), norm_nonneg t]
  have hv (j : J) : ‖v j‖ ≤ 1 := by simp [v, EuclideanSpace.norm_single]
  have h := finite_grothendieck_euclidean A B (scalar_form_le_of_column_bound A B hB)
    u v hu hv
  have hinner (i : I) (j : J) : A i j * inner ℝ (u i) (v j) = |A i j| * t j := by
    simp only [v, EuclideanSpace.inner_single_right]
    change A i j * (1 * (if 0 ≤ A i j then t j else -t j)) = |A i j| * t j
    rw [one_mul]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have heq : (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) = ‖c‖ := by
    simp_rw [hinner]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hc := inner_normalized c
    rw [euclidean_inner] at hc
    exact hc
  rw [heq, abs_of_nonneg (norm_nonneg c)] at h
  have hBnon : 0 ≤ B := by
    have hzero := hB (fun _ => 0) (by simp)
    simpa using hzero
  have hsq : ‖c‖ ^ 2 ≤ (128 * B) ^ 2 := by nlinarith [norm_nonneg c]
  simpa only [euclidean_norm_sq, c] using hsq

end ThesisCommon.Grothendieck
