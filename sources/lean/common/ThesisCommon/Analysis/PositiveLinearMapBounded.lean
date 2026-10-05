import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-! Automatic boundedness of algebraic positive and regular linear maps
from a Banach lattice. Positivity is the only operator hypothesis. -/
noncomputable section
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
variable [IsOrderedAddMonoid E] [HasSolidNorm E] [IsOrderedModule ℝ E]
variable [CompleteSpace E] [OrderClosedTopology E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [Lattice F]
variable [IsOrderedAddMonoid F] [HasSolidNorm F]

/-- Algebraic regularity: the positive summands need not be continuous. -/
def IsRegularLinearMap (T : E →ₗ[ℝ] F) : Prop :=
  ∃ P Q : E →ₗ[ℝ] F, (∀ x, 0 ≤ x → 0 ≤ P x) ∧
    (∀ x, 0 ≤ x → 0 ≤ Q x) ∧ T = P - Q

omit [HasSolidNorm E] [IsOrderedModule ℝ E] [CompleteSpace E] [OrderClosedTopology E] [HasSolidNorm F] in
theorem positive_linearMap_monotone (T : E →ₗ[ℝ] F) (hT : ∀ x, 0 ≤ x → 0 ≤ T x) : Monotone T := by
  intro x y hxy
  have h := hT (y - x) (sub_nonneg.mpr hxy)
  simpa only [map_sub, sub_nonneg] using h

theorem positive_linearMap_exists_bound (T : E →ₗ[ℝ] F) (hT : ∀ x, 0 ≤ x → 0 ≤ T x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
  have hposbound : ∃ C : ℝ, ∀ x, 0 ≤ x → ‖T x‖ ≤ C * ‖x‖ := by
    by_contra h
    push_neg at h
    have hchoose : ∀ n : ℕ, ∃ u : E, 0 ≤ u ∧ ‖u‖ ≤ (1 / 2 : ℝ) ^ n ∧
        (n : ℝ) + 1 < ‖T u‖ := by
      intro n
      let r : ℝ := (1 / 2) ^ n
      have hr : 0 < r := pow_pos (by norm_num) n
      obtain ⟨v, hv, hTv⟩ := h (((n : ℝ) + 1) / r)
      have hvnorm : 0 < ‖v‖ := by
        apply norm_pos_iff.mpr
        intro hvzero
        simp only [hvzero, map_zero, norm_zero, mul_zero, lt_self_iff_false] at hTv
      let a : ℝ := r / ‖v‖
      have ha : 0 < a := div_pos hr hvnorm
      refine ⟨a • v, smul_nonneg ha.le hv, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        exact le_of_eq (div_mul_cancel₀ r hvnorm.ne')
      · rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        calc
          (n : ℝ) + 1 = a * ((((n : ℝ) + 1) / r) * ‖v‖) := by
            dsimp [a]
            field_simp
          _ < a * ‖T v‖ := mul_lt_mul_of_pos_left hTv ha
    choose u hupos hunorm huT using hchoose
    have hus : Summable u := summable_geometric_two.of_norm_bounded hunorm
    have huupper : ∀ n, u n ≤ ∑' j, u j := fun n => hus.le_tsum n (fun j _ => hupos j)
    have hTupper : ∀ n, ‖T (u n)‖ ≤ ‖T (∑' j, u j)‖ := by
      intro n
      have hn := positive_linearMap_monotone T hT (huupper n)
      apply norm_le_norm_of_abs_le_abs
      simpa only [abs_of_nonneg (hT _ (hupos n)),
        abs_of_nonneg ((hT _ (hupos n)).trans hn)] using hn
    obtain ⟨n, hn⟩ := exists_nat_gt ‖T (∑' j, u j)‖
    have hbad := (huT n).trans_le (hTupper n)
    linarith
  obtain ⟨C, hC⟩ := hposbound
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have habs : |T x| ≤ T |x| := by
    apply sup_le
    · exact positive_linearMap_monotone T hT (le_abs_self x)
    · simpa only [map_neg] using positive_linearMap_monotone T hT
        (show -x ≤ |x| from le_sup_right)
  calc
    ‖T x‖ ≤ ‖T |x|‖ := norm_le_norm_of_abs_le_abs (by
      simpa only [abs_of_nonneg (hT _ (abs_nonneg x))] using habs)
    _ ≤ C * ‖|x|‖ := hC |x| (abs_nonneg x)
    _ ≤ max C 0 * ‖x‖ := by
      rw [norm_abs_eq_norm]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

theorem continuous_positive_linearMap (T : E →ₗ[ℝ] F) (hT : ∀ x, 0 ≤ x → 0 ≤ T x) :
    Continuous T := by
  obtain ⟨C, _, hC⟩ := positive_linearMap_exists_bound T hT
  exact (T.mkContinuous C hC).continuous

theorem continuous_regular_linearMap (T : E →ₗ[ℝ] F)
    (hT : IsRegularLinearMap T) : Continuous T := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := hT
  exact (continuous_positive_linearMap P hP).sub (continuous_positive_linearMap Q hQ)

end ThesisCommon
