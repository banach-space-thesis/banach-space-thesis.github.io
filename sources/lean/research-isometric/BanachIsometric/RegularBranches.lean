import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Countable injective branches of the differentiable regular set

This uses the quantitative measurable partition in Mathlib's Jacobian proof.
It requires neither C¹ regularity nor a pre-existing system of inverse branches.
The approximation radius is selected from the inverse of each actual derivative.
-/

namespace BanachIsometric

open MeasureTheory Set Function
open scoped Topology NNReal Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def regularLinearEquiv (A : E →L[ℝ] E) (hA : A.det ≠ 0) : E ≃L[ℝ] E :=
  (A.toLinearMap.equivOfDetNeZero hA).toContinuousLinearEquiv

@[simp] theorem regularLinearEquiv_coe (A : E →L[ℝ] E) (hA : A.det ≠ 0) :
    (regularLinearEquiv A hA : E →L[ℝ] E) = A := by
  ext x
  rfl

variable [Nontrivial E]

theorem regularLinearEquiv_inverse_nnnorm_pos (A : E →L[ℝ] E) (hA : A.det ≠ 0) :
    0 < ‖((regularLinearEquiv A hA).symm : E →L[ℝ] E)‖₊ := by
  change (0 : ℝ) < ‖((regularLinearEquiv A hA).symm : E →L[ℝ] E)‖
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  apply hx
  apply (regularLinearEquiv A hA).symm.injective
  have hh := congrArg (fun T : E →L[ℝ] E => T x) hz
  simpa only [ContinuousLinearMap.zero_apply, map_zero] using hh

noncomputable def regularBranchRadius (A : E →L[ℝ] E) : ℝ≥0 :=
  if hA : A.det ≠ 0 then ‖((regularLinearEquiv A hA).symm : E →L[ℝ] E)‖₊⁻¹ / 2 else 1

theorem regularBranchRadius_pos (A : E →L[ℝ] E) : 0 < regularBranchRadius A := by
  classical
  unfold regularBranchRadius
  split_ifs with hA
  · exact div_pos (inv_pos.mpr (regularLinearEquiv_inverse_nnnorm_pos A hA)) (by norm_num)
  · exact zero_lt_one

variable [MeasurableSpace E] [BorelSpace E]

/-- Every measurable set on which a map has an invertible real derivative
within the set is partitioned into countably many measurable injective pieces.
The pieces are constructed, not assumed as an area-formula premise. -/
theorem exists_disjoint_measurable_injective_branches
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → E} {D : E → E →L[ℝ] E}
    {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hdet : ∀ x ∈ s, (D x).det ≠ 0) :
    ∃ t : ℕ → Set E,
      Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧
        (⋃ n, t n) = s ∧ ∀ n, InjOn f (t n) := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨t, A, hdisj, ht, hcover, happ, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s D hD
        regularBranchRadius (fun A => (regularBranchRadius_pos A).ne')
    refine ⟨fun n => s ∩ t n, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact (hdisj hij).mono inter_subset_right inter_subset_right
    · intro n
      exact hs.inter (ht n)
    · rw [← Set.inter_iUnion]
      exact Set.inter_eq_left.mpr hcover
    · intro n
      obtain ⟨x, hx, hAx⟩ := hactual hne n
      have hA : (A n).det ≠ 0 := by rw [hAx]; exact hdet x hx
      have happrox : ApproximatesLinearOn f
          (regularLinearEquiv (A n) hA : E →L[ℝ] E) (s ∩ t n) (regularBranchRadius (A n)) := by
        simpa only [regularLinearEquiv_coe] using happ n
      apply happrox.injOn (Or.inr ?_)
      simp only [regularBranchRadius, dif_pos hA]
      exact half_lt_self (inv_pos.mpr (regularLinearEquiv_inverse_nnnorm_pos (A n) hA))
  · refine ⟨fun _ => ∅, ?_, fun _ => MeasurableSet.empty, ?_, fun _ => injOn_empty f⟩
    · intro i j _
      exact disjoint_empty _
    · simp only [iUnion_empty, Set.not_nonempty_iff_eq_empty.mp hne]

end BanachIsometric
