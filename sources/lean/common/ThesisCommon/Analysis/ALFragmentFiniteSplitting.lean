import ThesisCommon.Analysis.ALFragmentNorm
import ThesisCommon.Analysis.ALFragmentMetric
import Mathlib.Data.Finset.Lattice.Fold

/-! Genuine finite extension data for atomless fragment algebras.  A fragment
can be split to any prescribed mass, and masses can be prescribed
simultaneously on every cell of a finite disjoint family.  No conditional
splitting over an infinite subalgebra is assumed by these statements. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
  [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
include hAL

theorem exists_positiveFragment_le_of_norm {e : E} [Fact (0 ≤ e)]
    (a : PositiveFragmentAlgebra e) (ha : NoPositiveAtomsBelow (positiveFragmentValue a))
    {r : ℝ} (hr : 0 ≤ r) (hra : r ≤ ‖positiveFragmentValue a‖) :
    ∃ b : PositiveFragmentAlgebra e, b ≤ a ∧ ‖positiveFragmentValue b‖ = r := by
  obtain ⟨v, hv, hnorm⟩ := al_exists_fragment_of_norm hAL
    (positiveFragmentValue_nonneg a) ha hr hra
  exact ⟨positiveFragmentOf (hv.trans (positiveFragmentValue_isFragment a)), hv.2.1, hnorm⟩

theorem exists_positiveFragment_finite_moments [Fintype I]
    {e : E} [Fact (0 ≤ e)] (a : I → PositiveFragmentAlgebra e)
    (hd : Pairwise (fun i j => Disjoint (a i) (a j)))
    (ha : ∀ i, NoPositiveAtomsBelow (positiveFragmentValue (a i)))
    (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (hra : ∀ i, r i ≤ ‖positiveFragmentValue (a i)‖) :
    ∃ b : PositiveFragmentAlgebra e, b ≤ Finset.univ.sup a ∧
      ∀ i, ‖positiveFragmentValue (b ⊓ a i)‖ = r i := by
  classical
  choose c hc hnorm using fun i => exists_positiveFragment_le_of_norm hAL
    (a i) (ha i) (hr i) (hra i)
  refine ⟨Finset.univ.sup c, Finset.sup_le (fun i _ =>
    (hc i).trans (Finset.le_sup (f := a) (Finset.mem_univ i))), ?_⟩
  intro i
  have heq : Finset.univ.sup c ⊓ a i = c i := by
    apply le_antisymm
    · rw [Finset.sup_inf_distrib_right]
      apply Finset.sup_le
      intro j _
      by_cases hji : j = i
      · subst j
        exact inf_le_left
      · have hdis : Disjoint (c j) (a i) := (hd hji).mono_left (hc j)
        rw [hdis.eq_bot]
        exact bot_le
    · exact le_inf (Finset.le_sup (f := c) (Finset.mem_univ i)) (hc i)
  rw [heq]
  exact hnorm i

/-- A simultaneous equal-halves split for any finite disjoint family. -/
theorem exists_positiveFragment_finite_half_split [Fintype I]
    {e : E} [Fact (0 ≤ e)] (a : I → PositiveFragmentAlgebra e)
    (hd : Pairwise (fun i j => Disjoint (a i) (a j)))
    (ha : ∀ i, NoPositiveAtomsBelow (positiveFragmentValue (a i))) :
    ∃ b : PositiveFragmentAlgebra e, b ≤ Finset.univ.sup a ∧
      ∀ i, ‖positiveFragmentValue (b ⊓ a i)‖ = ‖positiveFragmentValue (a i)‖ / 2 :=
  exists_positiveFragment_finite_moments hAL a hd ha
    (fun i => ‖positiveFragmentValue (a i)‖ / 2)
    (fun _ => by positivity) (fun i => by have := norm_nonneg (positiveFragmentValue (a i)); linarith)

end ThesisCommon
