import ThesisCommon.Analysis.ALRenormBandEstimates

/-! The norm estimate for a simultaneous finite spectral approximation.
The finite cells and their scalar approximants remain explicit throughout. -/
noncomputable section
open scoped BigOperators ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E J L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem al_norm_mono {x y : E} (hx : 0 ≤ x) (hxy : x ≤ y) : ‖x‖ ≤ ‖y‖ :=
  norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]; exact hxy)

/-- Finite grid comparisons locate an element in one scalar interval. This
does not require a total order on the vector lattice. -/
theorem spectral_grid_interval (v w : E) (hv : 0 ≤ v) (hw : 0 ≤ w) (hwv : w ≤ v)
    (n : ℕ) (hn : 0 < n)
    (hcut : ∀ k : Fin n, ((k : ℝ) / n) • v ≤ w ∨ w ≤ ((k : ℝ) / n) • v) :
    ∃ a : ℝ, 0 ≤ a ∧ a • v ≤ w ∧ w ≤ (a + 1 / n) • v := by
  have hstep : ∀ m : ℕ, m ≤ n →
      (∃ a : ℝ, 0 ≤ a ∧ a • v ≤ w ∧ w ≤ (a + 1 / n) • v) ∨
      ((m : ℝ) / n) • v ≤ w := by
    intro m
    induction m with
    | zero => intro _; right; simpa using hw
    | succ m ih =>
      intro hmn
      rcases ih (by omega) with h | h
      · exact Or.inl h
      · by_cases hlast : m+1 = n
        · left
          refine ⟨(m : ℝ) / n, by positivity, h, ?_⟩
          have heq : (m : ℝ) / n + 1 / n = 1 := by
            have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
            have hmn' : (m : ℝ)+1 = n := by exact_mod_cast hlast
            field_simp
            exact hmn'
          simpa only [heq, one_smul] using hwv
        · rcases hcut ⟨m+1, by omega⟩ with hlo | hhi
          · exact Or.inr hlo
          · left
            refine ⟨(m : ℝ) / n, by positivity, h, ?_⟩
            convert hhi using 1 <;> push_cast <;> congr 1 <;> ring
  rcases hstep n le_rfl with h | h
  · exact h
  · refine ⟨1, by norm_num, ?_, ?_⟩
    · simpa only [div_self (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn), one_smul] using h
    · exact hwv.trans (by
        have h := smul_le_smul_of_nonneg_right
          (show (1 : ℝ) ≤ 1 + 1/n by exact le_add_of_nonneg_right (by positivity)) hv
        simpa only [one_smul] using h)

/-- If every positive summand is trapped between neighboring scalar
multiples of every cell, the disjoint-cell lower estimate bounds the sum of
all original norms, with an explicit mesh error. -/
theorem positive_sum_bound_of_spectral_cells [Fintype J] [Fintype L]
    (u : J → E) (hu : ∀ j, 0 ≤ u j) (Q : L → E →L[ℝ] E)
    (hQ : ∀ l, 0 ≤ Q l) (hQsum : ∀ y, (∑ l, Q l y) = y)
    (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hQnorm : (∑ l, ‖Q l (∑ j, u j)‖) ≤ K * ‖∑ j, u j‖)
    (a : J → L → ℝ) (ha : ∀ j l, 0 ≤ a j l)
    (hlo : ∀ j l, a j l • Q l (∑ j, u j) ≤ Q l (u j))
    (hhi : ∀ j l, Q l (u j) ≤ (a j l + δ) • Q l (∑ j, u j)) :
    (∑ j, ‖u j‖) ≤ (1 + (Fintype.card J : ℝ) * δ) * K * ‖∑ j, u j‖ := by
  let x := ∑ j, u j
  have hx : 0 ≤ x := Finset.sum_nonneg fun j _ => hu j
  have hw (j : J) (l : L) : ‖Q l (u j)‖ ≤ (a j l + δ) * ‖Q l x‖ := by
    have h := al_norm_mono (hQ l (u j) (hu j)) (hhi j l)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (ha j l) hδ)] at h
  have hweight (l : L) : (∑ j, a j l) * ‖Q l x‖ ≤ ‖Q l x‖ := by
    have horder : (∑ j, a j l) • Q l x ≤ Q l x := by
      rw [Finset.sum_smul]
      have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlo j l)
      simpa only [← map_sum] using h
    have h := al_norm_mono (smul_nonneg (Finset.sum_nonneg fun j _ => ha j l) (hQ l x hx)) horder
    rwa [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => ha j l)] at h
  calc
    (∑ j, ‖u j‖) = ∑ j, ‖∑ l, Q l (u j)‖ := by simp only [hQsum]
    _ ≤ ∑ j, ∑ l, ‖Q l (u j)‖ := Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j, ∑ l, (a j l + δ) * ‖Q l x‖ :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hw j l
    _ = ∑ l, ((∑ j, a j l) + (Fintype.card J : ℝ) * δ) * ‖Q l x‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    _ ≤ ∑ l, (1 + (Fintype.card J : ℝ) * δ) * ‖Q l x‖ := by
      apply Finset.sum_le_sum
      intro l _
      have h := hweight l
      nlinarith
    _ = (1 + (Fintype.card J : ℝ) * δ) * ∑ l, ‖Q l x‖ := (Finset.mul_sum ..).symm
    _ ≤ (1 + (Fintype.card J : ℝ) * δ) * (K * ‖x‖) :=
      mul_le_mul_of_nonneg_left hQnorm (by positivity)
    _ = _ := by ring

end ThesisCommon
