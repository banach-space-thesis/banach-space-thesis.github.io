import ThesisCommon.Analysis.OperatorAlgebraAutomaticBound

/-! Automatic boundedness from countably many exactly extractable copies.
The tested homogeneous function need not be continuous or complete. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_small_norm_large_homogeneous_value
    (α : X → ℝ) (hzero : α 0 = 0)
    (hsmul : ∀ (a : 𝕜) x, α (a • x) = ‖a‖ * α x)
    (hbad : ¬ ∃ C : ℝ, 0 < C ∧ ∀ x, α x ≤ C * ‖x‖)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ∃ x : X, ‖x‖ ≤ δ ∧ R < α x := by
  have hex : ∃ x : X, ((R + 1) / δ) * ‖x‖ < α x := by
    by_contra h
    push_neg at h
    exact hbad ⟨(R + 1) / δ, by positivity, h⟩
  obtain ⟨x, hx⟩ := hex
  have hxpos : 0 < ‖x‖ := by
    by_contra h
    have hz : x = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h) (norm_nonneg _))
    simp only [hz, norm_zero, mul_zero, hzero, lt_self_iff_false] at hx
  let a : 𝕜 := ((δ / ‖x‖ : ℝ) : 𝕜)
  have ha : ‖a‖ = δ / ‖x‖ :=
    (RCLike.norm_ofReal _).trans (abs_of_pos (div_pos hδ hxpos))
  refine ⟨a • x, ?_, ?_⟩
  · rw [norm_smul, ha, div_mul_cancel₀ _ hxpos.ne']
  · rw [hsmul, ha]
    have hscaled := mul_lt_mul_of_pos_left hx (div_pos hδ hxpos)
    have heq : δ / ‖x‖ * ((R + 1) / δ * ‖x‖) = R + 1 := by field_simp
    rw [heq] at hscaled
    linarith

theorem exists_homogeneous_bound_of_orthogonal_embeddings [CompleteSpace X]
    (I Q : ℕ → X →L[𝕜] X)
    (hdiag : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 X)
    (hoff : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (α : X → ℝ) (hnonneg : ∀ x, 0 ≤ α x) (hzero : α 0 = 0)
    (hsmul : ∀ (a : 𝕜) x, α (a • x) = ‖a‖ * α x)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hact : ∀ n x, α (Q n x) ≤ a n * α x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, α x ≤ C * ‖x‖ := by
  classical
  by_contra hbad
  have hex (n : ℕ) : ∃ x : X,
      ‖x‖ ≤ (1 / 2 : ℝ)^n / (‖I n‖ + 1) ∧
      ((n : ℝ) + 1) * (a n + 1) < α x :=
    exists_small_norm_large_homogeneous_value α hzero hsmul hbad (by positivity)
      (mul_nonneg (by positivity) (by linarith [ha n]))
  choose x hnorm hlarge using hex
  let F : ℕ → X := fun n => I n (x n)
  have hFnorm (n : ℕ) : ‖F n‖ ≤ (1 / 2 : ℝ)^n := by
    calc
      _ ≤ ‖I n‖ * ‖x n‖ := (I n).le_opNorm _
      _ ≤ ‖I n‖ * ((1 / 2 : ℝ)^n / (‖I n‖ + 1)) :=
        mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _)
      _ ≤ (1 / 2 : ℝ)^n := by
        have hd : 0 < ‖I n‖ + 1 := by positivity
        apply (le_of_mul_le_mul_right ?_ hd)
        field_simp
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n]
  have hs : Summable F := (Summable.of_nonneg_of_le
    (fun n => norm_nonneg (F n)) hFnorm summable_geometric_two).of_norm
  let S : X := ∑' n, F n
  have hterm (n m : ℕ) : Q n (F m) = if m = n then x n else 0 := by
    by_cases hmn : m = n
    · subst m
      change ((Q n).comp (I n)) (x n) = _
      rw [hdiag]
      simp
    · change ((Q n).comp (I m)) (x m) = _
      rw [hoff n m (Ne.symm hmn)]
      simp [hmn]
  have hcoord (n : ℕ) : Q n S = x n := by
    calc
      _ = ∑' m, Q n (F m) := ((Q n).hasSum hs.hasSum).tsum_eq.symm
      _ = x n := by simp only [hterm]; simp
  have hl (n : ℕ) : (n : ℝ) + 1 < α S := by
    have hb : α (x n) ≤ (a n + 1) * α S := by
      rw [← hcoord]
      exact (hact n S).trans (by nlinarith [hnonneg S])
    exact (mul_lt_mul_iff_right₀ (by linarith [ha n] : 0 < a n + 1)).mp
      (by simpa only [mul_comm] using (hlarge n).trans_le hb)
  obtain ⟨n, hn⟩ := exists_nat_gt (α S)
  have := hl n
  linarith

end ThesisCommon
