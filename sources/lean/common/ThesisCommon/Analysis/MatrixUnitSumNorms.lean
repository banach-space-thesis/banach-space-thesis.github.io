import ThesisCommon.Analysis.MatrixBlockOperators
import Mathlib.Analysis.MeanInequalities

/-! Exact column and row matrix-unit norms in the actual finite ℓp operator
space. Row norms use Hölder and the explicit conjugate-phase norming vector. -/
noncomputable section
open scoped ENNReal BigOperators ComplexConjugate
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_lp_unimodular_sum_single {ι : Type*} [DecidableEq ι] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (S : Finset ι) (ε : ι → 𝕜) (hε : ∀ i ∈ S, ‖ε i‖ = 1) :
    ‖∑ i ∈ S, lp.single (E := fun _ : ι => 𝕜) p i (ε i)‖ =
      (S.card : ℝ) ^ (1 / p.toReal) := by
  have h := lp.norm_sum_single (E := fun _ : ι => 𝕜) hp ε S
  have heq : (∑ i ∈ S, ‖ε i‖ ^ p.toReal) = (S.card : ℝ) := by
    calc
      _ = ∑ i ∈ S, (1 : ℝ) := Finset.sum_congr rfl (fun i hi => by rw [hε i hi, Real.one_rpow])
      _ = _ := by simp
  rw [heq] at h
  have hh := congrArg (fun t : ℝ => t ^ (p.toReal)⁻¹) h
  simpa only [Real.rpow_rpow_inv (norm_nonneg _) hp.ne', one_div] using hh

theorem norm_matrixUnit_column_sum (p : BanachExponent) (hp : 0 < p.val.toReal)
    {N : ℕ} (I : Finset (Fin N)) (ε : Fin N → 𝕜) (hε : ∀ i ∈ I, ‖ε i‖ = 1)
    (j : Fin N) :
    ‖∑ i ∈ I, ε i • matrixUnit (𝕜 := 𝕜) p i j‖ = (I.card : ℝ) ^ (1 / p.val.toReal) := by
  let v : FiniteLpSpace 𝕜 p N := ∑ i ∈ I, lp.single p.val i (ε i)
  let A : FiniteMatrixBlock 𝕜 p N := ∑ i ∈ I, ε i • matrixUnit p i j
  have hA : A = (lpCoordinate p.val j).smulRight v := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext k
    simp only [A, v, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, matrixUnit_apply,
      ContinuousLinearMap.smulRight_apply, lpCoordinate_apply,
      lp.single_apply, Pi.single_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mul_comm]
  have hv : ‖v‖ = (I.card : ℝ) ^ (1 / p.val.toReal) := by
    simpa only [v] using norm_lp_unimodular_sum_single (𝕜 := 𝕜) p.val hp I ε hε
  have hnorm : ‖A‖ = ‖v‖ := by
    apply le_antisymm
    · rw [hA, ContinuousLinearMap.norm_smulRight_apply]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_lpCoordinate_le (𝕜 := 𝕜) (X := 𝕜) p.val j) (norm_nonneg v)
    · have h := A.le_opNorm (lp.single p.val j (1 : 𝕜))
      simpa only [hA, ContinuousLinearMap.smulRight_apply, lpCoordinate_apply,
        lp.single_apply_self, one_smul, lp.norm_single (zero_lt_one.trans_le p.property),
        norm_one, mul_one] using h
  exact hnorm.trans hv

theorem finite_lp_sum_norm_bound (p : BanachExponent) (hp : 1 < p.val.toReal)
    {N : ℕ} (J : Finset (Fin N)) (x : FiniteLpSpace 𝕜 p N) :
    ∑ j ∈ J, ‖x j‖ ≤ (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) * ‖x‖ := by
  let q := p.val.toReal / (p.val.toReal - 1)
  have hpq : p.val.toReal.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg J hpq
    (fun j _ => norm_nonneg (x j)) (fun _ _ => zero_le_one)
  have h' : ∑ j ∈ J, ‖x j‖ ≤ (∑ j ∈ J, ‖x j‖ ^ p.val.toReal) ^ (1 / p.val.toReal) *
      (J.card : ℝ) ^ (1 / q) := by simpa using h
  have hsum : (∑ j ∈ J, ‖x j‖ ^ p.val.toReal) ^ (1 / p.val.toReal) ≤ ‖x‖ := by
    have hr := Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg (x j)) _))
      (lp.sum_rpow_le_norm_rpow (zero_lt_one.trans hp) x J) (one_div_nonneg.mpr (zero_lt_one.trans hp).le)
    simpa only [one_div, Real.rpow_rpow_inv (norm_nonneg x) (zero_lt_one.trans hp).ne'] using hr
  exact h'.trans (by simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (Nat.cast_nonneg J.card) (1 / q))))

set_option maxHeartbeats 800000 in
theorem norm_matrixUnit_row_sum (p : BanachExponent) (hp : 1 < p.val.toReal)
    {N : ℕ} (J : Finset (Fin N)) (hJ : J.Nonempty)
    (δ : Fin N → 𝕜) (hδ : ∀ j ∈ J, ‖δ j‖ = 1) (i : Fin N) :
    ‖∑ j ∈ J, δ j • matrixUnit (𝕜 := 𝕜) p i j‖ =
      (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) := by
  let A : FiniteMatrixBlock 𝕜 p N := ∑ j ∈ J, δ j • matrixUnit p i j
  change ‖A‖ = (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1)))
  have hA (x : FiniteLpSpace 𝕜 p N) : A x = lp.single p.val i (∑ j ∈ J, δ j * x j) := by
    apply lp.ext
    funext k
    by_cases hk : k = i
    · subst k
      simp [A, matrixUnit_apply, smul_eq_mul]
    · simp [A, matrixUnit_apply, hk, lp.single_apply]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    intro x
    rw [hA, lp.norm_single (zero_lt_one.trans_le p.property)]
    calc
      _ ≤ ∑ j ∈ J, ‖δ j * x j‖ := norm_sum_le _ _
      _ = ∑ j ∈ J, ‖x j‖ := Finset.sum_congr rfl (fun j hj => by rw [norm_mul, hδ j hj, one_mul])
      _ ≤ _ := finite_lp_sum_norm_bound (𝕜 := 𝕜) p hp J x
  · let v : FiniteLpSpace 𝕜 p N := ∑ j ∈ J, lp.single p.val j (conj (δ j))
    have hv : ‖v‖ = (J.card : ℝ) ^ (1 / p.val.toReal) :=
      norm_lp_unimodular_sum_single (𝕜 := 𝕜) p.val (zero_lt_one.trans hp) J _
        (fun j hj => (RCLike.norm_conj _).trans (hδ j hj))
    have hvj (j : Fin N) (hj : j ∈ J) : v j = conj (δ j) := by
      simp only [v, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
      exact Finset.sum_ite_eq J j (fun k => conj (δ k)) |>.trans (if_pos hj)
    have hsum : (∑ j ∈ J, δ j * v j) = (J.card : 𝕜) := by
      calc
        _ = ∑ j ∈ J, (1 : 𝕜) := Finset.sum_congr rfl (fun j hj => by
          rw [hvj j hj, RCLike.mul_conj, hδ j hj]; norm_num)
        _ = _ := by simp
    have hlo := A.le_opNorm v
    rw [hA, hsum, lp.norm_single (zero_lt_one.trans_le p.property), hv] at hlo
    have hc : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
    have hpq : p.val.toReal.HolderConjugate (p.val.toReal / (p.val.toReal - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
    have hpow : (J.card : ℝ) ^ (1 / (p.val.toReal / (p.val.toReal - 1))) *
        (J.card : ℝ) ^ (1 / p.val.toReal) = J.card := by
      rw [← Real.rpow_add hc, one_div, one_div, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hc (1 / p.val.toReal))).mp
    rw [hpow]
    simpa using hlo

end ThesisCommon
