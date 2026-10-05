import ThesisCommon.Analysis.ALFragmentHomogeneity
import ThesisCommon.Analysis.ALOrderCompleteness
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Disjoint families of fragments have summable norms.  Thus the homogeneous
fragment decomposition is genuinely countable and its ambient sum is the
original positive vector. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] {e : E} [Fact (0 ≤ e)]

omit [HasSolidNorm E] in
theorem positiveFragmentValue_finset_sup_of_disjoint
    (a : I → PositiveFragmentAlgebra e) (hd : Pairwise (fun i j => Disjoint (a i) (a j))) (s : Finset I) :
    positiveFragmentValue (s.sup a) = ∑ i ∈ s, positiveFragmentValue (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert, positiveFragmentValue_sup_of_disjoint, ih, Finset.sum_insert hi]
    exact Finset.disjoint_sup_right.mpr (fun j hj => hd (ne_of_mem_of_not_mem hj hi).symm)

theorem positiveFragment_finite_norm_sum_le
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (a : I → PositiveFragmentAlgebra e) (hd : Pairwise (fun i j => Disjoint (a i) (a j))) (s : Finset I) :
    ∑ i ∈ s, ‖positiveFragmentValue (a i)‖ ≤ ‖e‖ := by
  rw [← al_norm_sum hAL s _ (fun i _ => positiveFragmentValue_nonneg (a i)),
    ← positiveFragmentValue_finset_sup_of_disjoint a hd s]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (positiveFragmentValue_nonneg _), abs_of_nonneg (Fact.out : 0 ≤ e)]
  exact positiveFragmentValue_le _

theorem positiveFragment_summable_norm
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (a : I → PositiveFragmentAlgebra e) (hd : Pairwise (fun i j => Disjoint (a i) (a j))) :
    Summable (fun i => ‖positiveFragmentValue (a i)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _)
    (positiveFragment_finite_norm_sum_le hAL a hd)

theorem positiveFragment_disjoint_nonzero_countable
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    {s : Set (PositiveFragmentAlgebra e)} (hd : s.Pairwise Disjoint)
    (hn : ∀ a ∈ s, a ≠ ⊥) : s.Countable := by
  have hdp : Pairwise (fun a b : s => Disjoint a.val b.val) :=
    fun a b hab => hd a.property b.property (fun h => hab (Subtype.ext h))
  have hc := (positiveFragment_summable_norm hAL (fun a : s => a.val) hdp).countable_support
  apply (hc.image Subtype.val).mono
  intro a ha
  refine ⟨⟨a, ha⟩, ?_, rfl⟩
  change ‖positiveFragmentValue a‖ ≠ 0
  intro h
  apply hn a ha
  apply positiveFragmentValue_injective e
  simpa using norm_eq_zero.mp h

variable [CompleteSpace E] [OrderClosedTopology E]

theorem positiveFragment_hasSum_of_isLUB_top
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    {s : Set (PositiveFragmentAlgebra e)} (hd : s.Pairwise Disjoint)
    (htop : IsLUB s ⊤) : HasSum (fun a : s => positiveFragmentValue a.val) e := by
  have hdp : Pairwise (fun a b : s => Disjoint a.val b.val) :=
    fun a b hab => hd a.property b.property (fun h => hab (Subtype.ext h))
  have hs := (positiveFragment_summable_norm hAL (fun a : s => a.val) hdp).of_norm
  have hfrag : IsPositiveFragment (∑' a : s, positiveFragmentValue a.val) e := by
    apply (isClosed_positiveFragments e).mem_of_tendsto hs.hasSum
    apply Eventually.of_forall
    intro F
    rw [← positiveFragmentValue_finset_sup_of_disjoint (fun a : s => a.val) hdp F]
    exact positiveFragmentValue_isFragment _
  have hupper : ∀ a ∈ s, a ≤ positiveFragmentOf hfrag := by
    intro a ha
    change positiveFragmentValue a ≤ ∑' b : s, positiveFragmentValue b.val
    exact hs.le_tsum ⟨a, ha⟩ (fun b _ => positiveFragmentValue_nonneg b.val)
  have heq := (htop.2 hupper).antisymm le_top
  have hvalue := congrArg positiveFragmentValue heq
  have ht : (∑' a : s, positiveFragmentValue a.val) = e := hvalue.symm
  simpa only [ht] using hs.hasSum

theorem exists_countable_homogeneous_positiveFragment_decomposition
    (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
    (e : E) [Fact (0 ≤ e)] :
    ∃ s : Set (PositiveFragmentAlgebra e), s.Countable ∧
      (∀ a ∈ s, IsDensityHomogeneous a) ∧ s.Pairwise Disjoint ∧
      HasSum (fun a : s => positiveFragmentValue a.val) e := by
  obtain ⟨s, hh, hd, htop⟩ := exists_homogeneous_positiveFragment_decomposition e
  exact ⟨s, positiveFragment_disjoint_nonzero_countable hAL hd (fun a ha => (hh a ha).1),
    hh, hd, positiveFragment_hasSum_of_isLUB_top hAL hd htop⟩

end ThesisCommon

