import SurveyStatements.P1C0BlockSynthesis

/-! Nearly maximal disjoint c₀ blocks give quantitative finite-combination
lower bounds, with the off-block functional errors retained explicitly. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

theorem c0Finsupp_norm_attained {a : ℕ →₀ ℂ} (ha : a ≠ 0) :
    ∃ j ∈ a.support, ‖a j‖ = ‖c0Finsupp a‖ := by
  classical
  have hnonempty : a.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h => ha (Finsupp.support_eq_empty.mp h))
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image a.support (fun i => ‖a i‖) hnonempty
  refine ⟨j, hj, le_antisymm (c0Finsupp_apply_norm_le a j) ?_⟩
  apply norm_c0Finsupp_le (norm_nonneg _)
  intro i
  by_cases hi : i ∈ a.support
  · exact hmax i hi
  · simp [Finsupp.notMem_support_iff.mp hi, norm_nonneg]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem c0_disjointBlocks_finite_lower (T : ComplexC0 →L[ℂ] X) (N : ℕ)
    (b : ℕ → ℕ →₀ ℂ)
    (hsupp : ∀ n i, i ∈ (b n).support → N ≤ i)
    (hdisjoint : ∀ n k, n ≠ k → Disjoint (b n).support (b k).support)
    (hb : ∀ n i, ‖b n i‖ ≤ 1) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, c ≤ ‖T (c0Finsupp (b n))‖) (a : ℕ →₀ ℂ) :
    (2 * c - c0TailUpperNorm T N) * ‖c0Finsupp a‖ ≤
      ‖T (c0Finsupp (Finsupp.linearCombination ℂ b a))‖ := by
  classical
  by_cases ha0 : a = 0
  · subst a
    have hzero : c0Finsupp 0 = 0 := by ext i; rfl
    simp [hzero]
  obtain ⟨j, hj, hCj⟩ := c0Finsupp_norm_attained ha0
  let C : ℝ := ‖c0Finsupp a‖
  have hC : 0 < C := by
    change 0 < ‖c0Finsupp a‖
    rw [← hCj]
    exact norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hj)
  have hCnz : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let d : ℕ →₀ ℂ := (C : ℂ)⁻¹ • Finsupp.linearCombination ℂ b (a.erase j)
  have herase : ∀ k, ‖(a.erase j) k‖ ≤ C := by
    intro k
    by_cases hkj : k = j
    · subst k; simp [hC.le]
    · simpa [Finsupp.erase_apply, hkj] using c0Finsupp_apply_norm_le a k
  have hdcoeff : ∀ i, ‖d i‖ ≤ 1 := by
    intro i
    have hbnd := finsuppBlockSynthesis_coeff_bound b hdisjoint hb (a.erase j) hC.le herase i
    simp only [d, Finsupp.smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hC]
    exact (mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')
  have hdsupp : ∀ i ∈ d.support, N ≤ i := by
    intro i hi
    exact finsuppBlockSynthesis_tail_support b N hsupp (a.erase j) i (Finsupp.support_smul hi)
  have hbd : Disjoint (b j).support d.support :=
    (finsuppBlockSynthesis_erase_disjoint b hdisjoint a j).mono_right Finsupp.support_smul
  have hvpos : 0 < ‖T (c0Finsupp (b j))‖ := hc.trans_le (hlower j)
  obtain ⟨f, hfnorm, hfvalue⟩ := exists_dual_vector ℂ (T (c0Finsupp (b j)))
    (norm_pos_iff.mp hvpos)
  have hoff := c0_normingFunctional_offBlock_bound T N (b j) d (hsupp j) hdsupp
    (hb j) hdcoeff hbd f hfnorm hfvalue
  have haEq : a = Finsupp.single j (a j) + a.erase j := by
    ext k
    by_cases hkj : k = j
    · subst k; simp
    · simp [Finsupp.single_apply, Finsupp.erase_apply, hkj]
  have hdEq : (C : ℂ) • d = Finsupp.linearCombination ℂ b (a.erase j) := by
    simp [d, smul_smul, hCnz]
  have hraw : Finsupp.linearCombination ℂ b a = a j • b j + (C : ℂ) • d := by
    conv_lhs => rw [haEq, map_add, Finsupp.linearCombination_single]
    rw [hdEq]
  let V : X := T (c0Finsupp (Finsupp.linearCombination ℂ b a))
  have hV : V = a j • T (c0Finsupp (b j)) + (C : ℂ) • T (c0Finsupp d) := by
    change T (c0FinsuppLinear (Finsupp.linearCombination ℂ b a)) = _
    rw [hraw, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
    rfl
  have hfeq : a j * f (T (c0Finsupp (b j))) = f V - (C : ℂ) * f (T (c0Finsupp d)) := by
    rw [hV, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hnormleft : ‖a j * f (T (c0Finsupp (b j)))‖ = C * ‖T (c0Finsupp (b j))‖ := by
    rw [norm_mul, hfvalue, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), hCj]
  have hfV : ‖f V‖ ≤ ‖V‖ := by simpa [hfnorm] using f.le_opNorm V
  have htriangle : C * ‖T (c0Finsupp (b j))‖ ≤
      ‖V‖ + C * ‖f (T (c0Finsupp d))‖ := by
    rw [← hnormleft, hfeq]
    exact (norm_sub_le _ _).trans (by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
      exact add_le_add_right hfV _)
  have hoffC := mul_le_mul_of_nonneg_left hoff hC.le
  have hcC := mul_le_mul_of_nonneg_left (hlower j) hC.le
  change (2 * c - c0TailUpperNorm T N) * C ≤ ‖V‖
  nlinarith

theorem c0_disjointBlocks_finite_upper (T : ComplexC0 →L[ℂ] X) (N : ℕ)
    (b : ℕ → ℕ →₀ ℂ)
    (hsupp : ∀ n i, i ∈ (b n).support → N ≤ i)
    (hdisjoint : ∀ n k, n ≠ k → Disjoint (b n).support (b k).support)
    (hb : ∀ n i, ‖b n i‖ ≤ 1) (a : ℕ →₀ ℂ) :
    ‖T (c0Finsupp (Finsupp.linearCombination ℂ b a))‖ ≤
      c0TailUpperNorm T N * ‖c0Finsupp a‖ := by
  classical
  by_cases ha0 : a = 0
  · subst a
    have hzero : c0Finsupp 0 = 0 := by ext i; rfl
    simp [hzero]
  obtain ⟨j, hj, hCj⟩ := c0Finsupp_norm_attained ha0
  let C : ℝ := ‖c0Finsupp a‖
  have hC : 0 < C := by
    change 0 < ‖c0Finsupp a‖
    rw [← hCj]
    exact norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hj)
  have hCnz : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let d : ℕ →₀ ℂ := (C : ℂ)⁻¹ • Finsupp.linearCombination ℂ b a
  have hdcoeff : ∀ i, ‖d i‖ ≤ 1 := by
    intro i
    have hbnd := finsuppBlockSynthesis_coeff_bound b hdisjoint hb a hC.le
      (c0Finsupp_apply_norm_le a) i
    simp only [d, Finsupp.smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hC]
    exact (mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')
  have hdsupp : ∀ i ∈ d.support, N ≤ i := by
    intro i hi
    exact finsuppBlockSynthesis_tail_support b N hsupp a i (Finsupp.support_smul hi)
  have hdEq : (C : ℂ) • d = Finsupp.linearCombination ℂ b a := by
    simp [d, smul_smul, hCnz]
  have himage : T (c0Finsupp (Finsupp.linearCombination ℂ b a)) = (C : ℂ) • T (c0Finsupp d) := by
    change T (c0FinsuppLinear (Finsupp.linearCombination ℂ b a)) = _
    rw [← hdEq, map_smul, map_smul]
    rfl
  rw [himage, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact (mul_le_mul_of_nonneg_left (norm_c0Finsupp_image_le_tail T N d hdsupp hdcoeff) hC.le).trans_eq
    (mul_comm _ _)

end SurveyStatements.P1
