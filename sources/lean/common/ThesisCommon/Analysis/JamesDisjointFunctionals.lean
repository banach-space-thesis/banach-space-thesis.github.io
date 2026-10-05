import ThesisCommon.Analysis.JamesDisjointEstimate

/-! A functional cannot be uniformly positive on arbitrarily long finite
disjoint families of bounded James vectors when p > 1. This quantitative
finite obstruction is the input to the shrinking argument. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem james_no_disjoint_functional_witnesses (hpl : 1 < p.val.toReal)
    (φ : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) :
    ¬ (∀ m : ℕ, ∃ x : Fin m → JamesSequenceSpace 𝕜 p,
      (∀ n : ℕ, (Finset.univ.filter (fun i => x i n ≠ 0)).card ≤ 1) ∧
      (∀ i, ‖x i‖ ≤ M) ∧ (∀ i, δ ≤ RCLike.re (φ (x i)))) := by
  classical
  intro hw
  let q := p.val.toReal
  have hq : 0 < q := by dsimp [q]; linarith
  let C := ‖φ‖ ^ q * 2 ^ (q - 1) * M ^ q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 ((C / δ ^ q) ^ (q - 1)⁻¹))
  have hmpos : (0 : ℝ) < m := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hm)
  have hlarge : C / δ ^ q < (m : ℝ) ^ (q - 1) :=
    (Real.rpow_inv_lt_iff_of_pos (div_nonneg hC hd.le) (Nat.cast_nonneg _)
      (by dsimp [q]; linarith)).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨x, hxdisj, hxnorm, hxφ⟩ := hw m
  have hsum : (m : ℝ) * δ ≤ ‖φ‖ * ‖∑ i, x i‖ := by
    calc
      _ = ∑ _i : Fin m, δ := by simp
      _ ≤ ∑ i, RCLike.re (φ (x i)) := Finset.sum_le_sum (fun i _ => hxφ i)
      _ = RCLike.re (φ (∑ i, x i)) := by simp only [map_sum]
      _ ≤ ‖φ (∑ i, x i)‖ := RCLike.re_le_norm _
      _ ≤ ‖φ‖ * ‖∑ i, x i‖ := φ.le_opNorm _
  have hnorm : ‖∑ i, x i‖ ^ q ≤ 2 ^ (q - 1) * (m : ℝ) * M ^ q := by
    apply (james_disjoint_norm_rpow_le p hp Finset.univ x hxdisj).trans
    have hs : ∑ i, ‖x i‖ ^ q ≤ (m : ℝ) * M ^ q := by
      calc
        _ ≤ ∑ _i : Fin m, M ^ q := Finset.sum_le_sum (fun i _ =>
          Real.rpow_le_rpow (norm_nonneg _) (hxnorm i) hq.le)
        _ = _ := by simp
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  have hpow := Real.rpow_le_rpow (mul_nonneg hmpos.le hδ.le) hsum hq.le
  rw [Real.mul_rpow hmpos.le hδ.le,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hpow
  have hpow' : (m : ℝ) ^ q * δ ^ q ≤ (m : ℝ) * C := by
    exact (hpow.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))).trans_eq
      (by dsimp [C]; ring)
  have hidentity : (m : ℝ) ^ q = (m : ℝ) * (m : ℝ) ^ (q - 1) := by
    calc
      _ = (m : ℝ) ^ (1 + (q - 1)) := by congr 1; ring
      _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ (q - 1) := Real.rpow_add hmpos _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hidentity, mul_assoc] at hpow'
  have hsmall := le_of_mul_le_mul_left hpow' hmpos
  have hlarge' := (div_lt_iff₀ hd).mp hlarge
  linarith

end ThesisCommon
