import ThesisCommon.Analysis.RademacherFirstMoment
import ThesisCommon.Analysis.Cotype
import ThesisCommon.Analysis.LpOneRestriction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite cotype of actual arbitrary-index scalar ell-one. The estimate
uses finite first-moment Khintchine and the Euclidean triangle inequality,
then passes to the genuine unconditional coordinate expansion. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
open Grothendieck
variable {𝕜 : Type*} [RCLike 𝕜]
set_option maxHeartbeats 800000

theorem rclike_rademacher_second_le_nine_first_sq {n : ℕ} (a : Fin n → 𝕜) :
    (∑ i, ‖a i‖ ^ 2) ≤
      9 * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i)‖) ^ 2 := by
  let R (ε : Fin n → Bool) := ∑ i, signedValue (ε i) (a i)
  let A := mean (fun ε => ‖R ε‖)
  have hre (ε : Fin n → Bool) : rademacher (fun i => RCLike.re (a i)) ε = RCLike.re (R ε) := by
    simp only [rademacher, R, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp [signedValue]
  have him (ε : Fin n → Bool) : rademacher (fun i => RCLike.im (a i)) ε = RCLike.im (R ε) := by
    simp only [rademacher, R, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases ε i <;> simp [signedValue]
  have hAr : mean (fun ε => |RCLike.re (R ε)|) ≤ A :=
    mean_mono fun ε => by simpa only [Real.norm_eq_abs] using RCLike.norm_re_le_norm (R ε)
  have hAi : mean (fun ε => |RCLike.im (R ε)|) ≤ A :=
    mean_mono fun ε => by simpa only [Real.norm_eq_abs] using RCLike.norm_im_le_norm (R ε)
  have hr := rademacher_second_le_three_first_sq (fun i => RCLike.re (a i))
  have hi := rademacher_second_le_three_first_sq (fun i => RCLike.im (a i))
  simp only [hre] at hr
  simp only [him] at hi
  have hsr := sq_le_sq₀ (mean_nonneg fun ε => abs_nonneg _) (mean_nonneg fun ε => norm_nonneg _) |>.mpr hAr
  have hsi := sq_le_sq₀ (mean_nonneg fun ε => abs_nonneg _) (mean_nonneg fun ε => norm_nonneg _) |>.mpr hAi
  have heq : (∑ i, ‖a i‖ ^ 2) = (∑ i, RCLike.re (a i) ^ 2) +
      ∑ i, RCLike.im (a i) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [pow_two] using (RCLike.norm_sq_eq_def (z := a i))
  change (∑ i, ‖a i‖ ^ 2) ≤ 9 * A ^ 2
  rw [heq]
  nlinarith [sq_nonneg A]

theorem finite_ellOne_cotype_estimate {I : Type*} [Fintype I] {n : ℕ}
    (a : Fin n → I → 𝕜) :
    (∑ i, (∑ j, ‖a i j‖) ^ 2) ≤
      9 * mean (fun ε : Fin n → Bool => (∑ j, ‖∑ i, signedValue (ε i) (a i j)‖) ^ 2) := by
  let v (j : I) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ‖a i j‖)
  let A (ε : Fin n → Bool) := ∑ j, ‖∑ i, signedValue (ε i) (a i j)‖
  have hv (j : I) : ‖v j‖ ≤ 3 * mean (fun ε : Fin n → Bool =>
      ‖∑ i, signedValue (ε i) (a i j)‖) := by
    have h := rclike_rademacher_second_le_nine_first_sq (fun i => a i j)
    have hn : ‖v j‖ ^ 2 = ∑ i, ‖a i j‖ ^ 2 := by
      simpa only [v, PiLp.toLp_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        EuclideanSpace.norm_sq_eq (v j)
    rw [← hn] at h
    have hm : 0 ≤ mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i j)‖) :=
      mean_nonneg fun ε => norm_nonneg _
    nlinarith [norm_nonneg (v j)]
  have ht : ‖∑ j, v j‖ ≤ 3 * mean A := by
    calc
      _ ≤ ∑ j, ‖v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, 3 * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (a i j)‖) :=
        Finset.sum_le_sum fun j _ => hv j
      _ = 3 * mean A := by rw [← Finset.mul_sum, ← mean_sum]
  have hsum : ‖∑ j, v j‖ ^ 2 = ∑ i, (∑ j, ‖a i j‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    let ev : EuclideanSpace ℝ (Fin n) →+ ℝ :=
      { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have he : (∑ j, v j) i = ∑ j, ‖a i j‖ := map_sum ev v Finset.univ
    rw [he]
    rw [Real.norm_eq_abs, sq_abs]
  have hcs := mean_mul_sq_le (fun _ : Fin n → Bool => (1 : ℝ)) A
  simp only [one_mul, one_pow, mean_const] at hcs
  have hma : 0 ≤ mean A := mean_nonneg fun ε => Finset.sum_nonneg fun j _ => norm_nonneg _
  rw [← hsum]
  nlinarith [norm_nonneg (∑ j, v j)]

theorem scalar_ellOne_hasRademacherCotype_two (I : Type*) :
    HasRademacherCotype (lp (fun _ : I => 𝕜) 1) 2 3 := by
  classical
  have hnorm (f : lp (fun _ : I => 𝕜) 1) : HasSum (fun j => ‖f j‖) ‖f‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) f
  refine ⟨le_rfl, by norm_num, ?_⟩
  intro n x
  have hs (s : Finset I) : (∑ i, (∑ j ∈ s, ‖x i j‖) ^ 2) ≤
      9 * mean (fun ε : Fin n → Bool => ‖∑ i, signedValue (ε i) (x i)‖ ^ 2) := by
    have h := finite_ellOne_cotype_estimate (fun i (j : s) => x i j)
    have hmass (ε : Fin n → Bool) : (∑ j : s, ‖∑ i, signedValue (ε i) (x i j)‖) ≤
        ‖∑ i, signedValue (ε i) (x i)‖ := by
      have heq (j : I) : (∑ i, signedValue (ε i) (x i)) j =
          ∑ i, signedValue (ε i) (x i j) := by
        rw [lp.coeFn_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        cases ε i <;> simp [signedValue]
      calc
        _ = ∑ j ∈ s, ‖∑ i, signedValue (ε i) (x i j)‖ :=
          Finset.sum_coe_sort s (fun j => ‖∑ i, signedValue (ε i) (x i j)‖)
        _ ≤ _ := by
          simpa only [heq] using sum_le_hasSum s (fun j _ => norm_nonneg _)
            (hnorm (∑ i, signedValue (ε i) (x i)))
    have hmean := mean_mono fun ε => (sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (norm_nonneg _)).mpr (hmass ε)
    have hreindex (i : Fin n) : (∑ j : s, ‖x i j‖) = ∑ j ∈ s, ‖x i j‖ :=
      Finset.sum_coe_sort s (fun j => ‖x i j‖)
    simp_rw [hreindex] at h
    exact h.trans (mul_le_mul_of_nonneg_left hmean (by norm_num))
  have hi (i : Fin n) : Tendsto (fun s : Finset I => ∑ j ∈ s, ‖x i j‖)
      atTop (𝓝 ‖x i‖) := hnorm (x i)
  have h := le_of_tendsto' (tendsto_finset_sum _ (fun i _ => (hi i).pow 2)) hs
  simpa only [Real.rpow_two, mean, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, signedValue,
    show (3 : ℝ) ^ 2 = 9 by norm_num, mul_assoc] using h

theorem scalar_ellOne_hasFiniteCotype (I : Type*) :
    HasFiniteCotype (lp (fun _ : I => 𝕜) 1) :=
  ⟨2, 3, scalar_ellOne_hasRademacherCotype_two I⟩

end ThesisCommon
