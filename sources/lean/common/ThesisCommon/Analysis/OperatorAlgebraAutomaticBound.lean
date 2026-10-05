import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! An actual automatic boundedness argument for algebra seminorms on
operator algebras admitting countably many orthogonal self-copies. An
unbounded seminorm would give tiny operators in separate corners with
arbitrarily large extracted values, contradicting the finite seminorm of
their convergent operator sum. No target continuity is assumed. -/
noncomputable section
open Filter
open scoped Topology
namespace ThesisCommon
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_small_norm_large_value_of_unbounded
    (α : (E →L[𝕜] E) → ℝ) (hzero : α 0 = 0)
    (hsmul : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T)
    (hbad : ¬ ∃ C : ℝ, 0 < C ∧ ∀ T, α T ≤ C * ‖T‖)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ∃ T : E →L[𝕜] E, ‖T‖ ≤ δ ∧ R < α T := by
  have hex : ∃ T : E →L[𝕜] E, ((R + 1) / δ) * ‖T‖ < α T := by
    by_contra h
    push_neg at h
    exact hbad ⟨(R + 1) / δ, by positivity, h⟩
  obtain ⟨T, hT⟩ := hex
  have hTpos : 0 < ‖T‖ := by
    by_contra h
    have hn : ‖T‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    have hz : T = 0 := norm_eq_zero.mp hn
    simp only [hz, norm_zero, mul_zero, hzero, lt_self_iff_false] at hT
  let a : 𝕜 := ((δ / ‖T‖ : ℝ) : 𝕜)
  have ha : ‖a‖ = δ / ‖T‖ := by
    exact (RCLike.norm_ofReal _).trans (abs_of_pos (div_pos hδ hTpos))
  refine ⟨a • T, ?_, ?_⟩
  · rw [norm_smul, ha, div_mul_cancel₀ _ hTpos.ne']
  · rw [hsmul, ha]
    have hscaled := mul_lt_mul_of_pos_left hT (div_pos hδ hTpos)
    have heq : δ / ‖T‖ * ((R + 1) / δ * ‖T‖) = R + 1 := by
      field_simp
    rw [heq] at hscaled
    linarith

/-- Any nonnegative homogeneous submultiplicative function on `B(E)` is
bounded if `E` has countably many mutually orthogonal complemented copies
of itself. The maps and exact extraction identities are the only geometric
inputs. Completeness is used for the actual operator series. -/
theorem exists_algebra_seminorm_bound_of_orthogonal_selfCopies [CompleteSpace E]
    (J P : ℕ → E →L[𝕜] E)
    (hdiag : ∀ n, (P n).comp (J n) = ContinuousLinearMap.id 𝕜 E)
    (hoff : ∀ n m, n ≠ m → (P n).comp (J m) = 0)
    (α : (E →L[𝕜] E) → ℝ) (hnonneg : ∀ T, 0 ≤ α T) (hzero : α 0 = 0)
    (hsmul : ∀ (a : 𝕜) T, α (a • T) = ‖a‖ * α T)
    (hmul : ∀ S T, α (S.comp T) ≤ α S * α T) :
    ∃ C : ℝ, 0 < C ∧ ∀ T, α T ≤ C * ‖T‖ := by
  classical
  by_cases hId : α (ContinuousLinearMap.id 𝕜 E) = 0
  · refine ⟨1, zero_lt_one, fun T => ?_⟩
    have h := hmul (ContinuousLinearMap.id 𝕜 E) T
    rw [ContinuousLinearMap.id_comp, hId, zero_mul] at h
    exact h.trans (by simpa only [one_mul] using norm_nonneg T)
  by_contra hbad
  have hIdpos : 0 < α (ContinuousLinearMap.id 𝕜 E) :=
    lt_of_le_of_ne (hnonneg _) (Ne.symm hId)
  have hprod (n : ℕ) : 0 < α (P n) * α (J n) := by
    have h := hmul (P n) (J n)
    rw [hdiag] at h
    exact hIdpos.trans_le h
  have hex (n : ℕ) : ∃ T : E →L[𝕜] E,
      ‖T‖ ≤ (1 / 2 : ℝ) ^ n / (‖J n‖ * ‖P n‖ + 1) ∧
      ((n : ℝ) + 1) * (α (P n) * α (J n)) < α T :=
    exists_small_norm_large_value_of_unbounded α hzero hsmul hbad (by positivity)
      (mul_nonneg (by positivity) (hprod n).le)
  choose R hRnorm hRlarge using hex
  let F : ℕ → E →L[𝕜] E := fun n => (J n).comp ((R n).comp (P n))
  have hFnorm (n : ℕ) : ‖F n‖ ≤ (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ ‖J n‖ * (‖R n‖ * ‖P n‖) :=
        ((J n).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left ((R n).opNorm_comp_le _) (norm_nonneg _))
      _ ≤ ‖J n‖ * (((1 / 2 : ℝ) ^ n / (‖J n‖ * ‖P n‖ + 1)) * ‖P n‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hRnorm n) (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ (1 / 2 : ℝ) ^ n := by
        have hd : 0 < ‖J n‖ * ‖P n‖ + 1 := by positivity
        apply (le_of_mul_le_mul_right ?_ hd)
        field_simp
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  have hs : Summable F := (Summable.of_nonneg_of_le
    (fun n => norm_nonneg (F n)) hFnorm summable_geometric_two).of_norm
  let S : E →L[𝕜] E := ∑' n, F n
  have hterm (n m : ℕ) : (P n) * F m * (J n) = if m = n then R n else 0 := by
    by_cases hmn : m = n
    · subst m
      rw [if_pos rfl]
      change (P n).comp (((J n).comp ((R n).comp (P n))).comp (J n)) = R n
      calc
        _ = ((P n).comp (J n)).comp ((R n).comp ((P n).comp (J n))) := by
          simp only [ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [hdiag, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · rw [if_neg hmn]
      change ((P n).comp ((J m).comp ((R m).comp (P m)))).comp (J n) = 0
      rw [← ContinuousLinearMap.comp_assoc, hoff n m (Ne.symm hmn)]
      simp
  have hcoord (n : ℕ) : (P n) * S * (J n) = R n := by
    have hsum := (hs.hasSum.mul_left (P n)).mul_right (J n)
    calc
      _ = ∑' m, (P n) * F m * (J n) := hsum.tsum_eq.symm
      _ = R n := by simp only [hterm]; simp
  have hlarge (n : ℕ) : (n : ℝ) + 1 < α S := by
    have hbound : α (R n) ≤ (α (P n) * α (J n)) * α S := by
      rw [← hcoord]
      change α (((P n).comp S).comp (J n)) ≤ _
      calc
        _ ≤ α ((P n).comp S) * α (J n) := hmul _ _
        _ ≤ (α (P n) * α S) * α (J n) :=
          mul_le_mul_of_nonneg_right (hmul _ _) (hnonneg _)
        _ = _ := by ring
    exact (mul_lt_mul_iff_right₀ (hprod n)).mp (by
      simpa only [mul_comm] using (hRlarge n).trans_le hbound)
  obtain ⟨n, hn⟩ := exists_nat_gt (α S)
  have h := hlarge n
  linarith

end ThesisCommon
