import ThesisCommon.Analysis.LpDisjointSigns
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! The scalar block estimate used by LPCK's topological backward reduction.
Unit scalar phases make every summand positive, so the argument covers both
real and complex scalars without ordering the complex field. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem exists_small_scalar_block {N : ℕ} (J : Fin N → X →L[𝕜] Y)
    {B M ε : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ x : Fin N → X, (∀ i, ‖x i‖ ≤ 1) → ‖∑ i, J i (x i)‖ ≤ B)
    (T : Y →L[𝕜] 𝕜) (hT : ‖T‖ ≤ M) (hlarge : M * B < (N : ℝ) * ε) :
    ∃ i : Fin N, ‖T.comp (J i)‖ ≤ ε := by
  classical
  by_contra! hbad
  choose x hx hvalue using fun i => (T.comp (J i)).exists_lt_apply_of_lt_opNorm (hbad i)
  choose c hc hphase using fun i => RCLike.exists_norm_eq_mul_self (T (J i (x i)))
  let y : Fin N → X := fun i => c i • x i
  have hy : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    simpa only [y, norm_smul, hc i, one_mul] using (hx i).le
  have heval : T (∑ i, J i (y i)) = ((∑ i, ‖T (J i (x i))‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, y, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (hphase i).symm)
  have hevalnorm : ‖T (∑ i, J i (y i))‖ = ∑ i, ‖T (J i (x i))‖ := by
    rw [heval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  have hupper : (∑ i, ‖T (J i (x i))‖) ≤ M * B := by
    rw [← hevalnorm]
    exact (T.le_opNorm _).trans (mul_le_mul hT (hJ y hy) (norm_nonneg _) hM)
  have hlower : (N : ℝ) * ε ≤ ∑ i, ‖T (J i (x i))‖ := by
    calc
      _ = ∑ _i : Fin N, ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (hvalue i).le)
  exact (not_lt_of_ge (hlower.trans hupper)) hlarge

end ThesisCommon
