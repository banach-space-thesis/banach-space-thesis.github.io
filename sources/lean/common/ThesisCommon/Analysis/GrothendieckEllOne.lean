import ThesisCommon.Analysis.GrothendieckOperators
import ThesisCommon.Analysis.LpOneRestriction

/-! Grothendieck operator estimates on ell-one over an arbitrary index set.
Finite coordinate sets converge through the unconditional series in ell-one. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ThesisCommon.Grothendieck
attribute [local instance] Classical.decEq

variable {I J K : Type*} [Fintype J] [Fintype K]

theorem ellOne_finite_mass_le (x : lp (fun _ : I => ℝ) 1) (s : Finset I) :
    (∑ i ∈ s, |x i|) ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using
    sum_le_hasSum s (fun i _ => norm_nonneg (x i)) (lp_one_hasSum_norm x)

theorem ellOne_finite_column_bound (x : J → lp (fun _ : I => ℝ) 1) (s : Finset I)
    (B : ℝ) (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → ‖∑ j, b j • x j‖ ≤ B)
    (b : J → ℝ) (hb : ∀ j, |b j| ≤ 1) :
    (∑ i : s, |∑ j, x j i * b j|) ≤ B := by
  have h := (ellOne_finite_mass_le (∑ j, b j • x j) s).trans (hB b hb)
  rw [Finset.sum_coe_sort s (fun i => |∑ j, x j i * b j|)]
  simpa only [lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using h

/-- The uniform ell-two estimate for any finite family in arbitrary-index
ell-one, obtained from the proved finite Grothendieck inequality. -/
theorem ellOne_square_sum_le (x : J → lp (fun _ : I => ℝ) 1) (B : ℝ)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → ‖∑ j, b j • x j‖ ≤ B) :
    (∑ j, ‖x j‖ ^ 2) ≤ (128 * B) ^ 2 := by
  classical
  have hs (s : Finset I) : (∑ j, (∑ i ∈ s, |x j i|) ^ 2) ≤ (128 * B)^2 := by
    have h := finite_column_l1_square_sum_le (fun (i : s) j => x j i) B
      (ellOne_finite_column_bound x s B hB)
    have hreindex (j : J) : (∑ i : s, |x j i|) = ∑ i ∈ s, |x j i| :=
      Finset.sum_coe_sort s (fun i => |x j i|)
    simpa only [hreindex] using h
  have hj (j : J) : Tendsto (fun s : Finset I => ∑ i ∈ s, |x j i|) atTop (𝓝 ‖x j‖) := by
    simpa only [Real.norm_eq_abs] using (lp_one_hasSum_norm (x j))
  have ht : Tendsto (fun s : Finset I => ∑ j, (∑ i ∈ s, |x j i|)^2) atTop
      (𝓝 (∑ j, ‖x j‖^2)) := tendsto_finset_sum _ (fun j _ => (hj j).pow 2)
  exact le_of_tendsto' ht hs

theorem ellOne_image_series (S : lp (fun _ : I => ℝ) 1 →L[ℝ] EuclideanSpace ℝ K)
    (x : lp (fun _ : I => ℝ) 1) :
    HasSum (fun i => x i • S (lp.single 1 i 1)) (S x) := by
  have h := (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) x).map S S.continuous
  have hi (i : I) : S (lp.single 1 i (x i)) = x i • S (lp.single 1 i 1) := by
    rw [← map_smul, ← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  simpa only [Function.comp_def, hi] using h

/-- Every continuous map from ell-one to a finite-dimensional real Hilbert
space is 1-summing, with an explicit uniform constant. -/
theorem ellOne_hilbert_sum_norm_le
    (S : lp (fun _ : I => ℝ) 1 →L[ℝ] EuclideanSpace ℝ K)
    (x : J → lp (fun _ : I => ℝ) 1) (B M : ℝ) (hM : 0 < M) (hS : ‖S‖ ≤ M)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → ‖∑ j, b j • x j‖ ≤ B) :
    (∑ j, ‖S (x j)‖) ≤ 128 * M * B := by
  classical
  let u : I → EuclideanSpace ℝ K := fun i => M⁻¹ • S (lp.single 1 i 1)
  have hu (i : I) : ‖u i‖ ≤ 1 := by
    have hnorm : ‖S (lp.single 1 i (1 : ℝ))‖ ≤ M := by
      have h := S.le_opNorm (lp.single 1 i (1 : ℝ))
      simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 1), norm_one, mul_one]
        using h.trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hM]
    exact (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hM.le)).trans_eq (inv_mul_cancel₀ hM.ne')
  have hs (s : Finset I) : (∑ j, ‖∑ i ∈ s, x j i • S (lp.single 1 i 1)‖) ≤ 128 * M * B := by
    have h := finite_column_sum_norm_le (fun (i : s) j => x j i) B
      (ellOne_finite_column_bound x s B hB) (fun i : s => u i) (fun i => hu i)
    have heq (j : J) : (∑ i ∈ s, x j i • S (lp.single 1 i 1)) =
        M • ∑ i : s, x j i • u i := by
      rw [Finset.sum_coe_sort s (fun i => x j i • u i), Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [u]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hM.ne']
    simp_rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hM, ← Finset.mul_sum]
    have h' := mul_le_mul_of_nonneg_left h hM.le
    nlinarith
  have hj (j : J) : Tendsto
      (fun s : Finset I => ‖∑ i ∈ s, x j i • S (lp.single 1 i 1)‖)
      atTop (𝓝 ‖S (x j)‖) := by
    have ht : Tendsto (fun s : Finset I => ∑ i ∈ s, x j i • S (lp.single 1 i 1))
        atTop (𝓝 (S (x j))) := ellOne_image_series S (x j)
    exact ht.norm
  exact le_of_tendsto' (tendsto_finset_sum _ (fun j _ => hj j)) hs

end ThesisCommon.Grothendieck
