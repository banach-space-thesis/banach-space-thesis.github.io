import ThesisCommon.Analysis.ALFragmentMetric
import ThesisCommon.Analysis.ALOrderCompleteness
import Mathlib.Order.CompleteBooleanAlgebra

/-! Arbitrary suprema of fragments are constructed as norm limits of finite
joins. This gives the actual fragment algebra its complete Boolean structure. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (e : E) [Fact (0 ≤ e)]
include hAL

theorem positiveFragment_exists_isLUB (s : Set (PositiveFragmentAlgebra e)) :
    ∃ a, IsLUB s a := by
  classical
  let v (t : Finset s) : PositiveFragmentAlgebra e := t.sup fun b => b.val
  let d : Set E := range fun t : Finset s => positiveFragmentValue (v t)
  have hd : d.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hpos : ∀ x ∈ d, 0 ≤ x := by
    rintro x ⟨t, rfl⟩
    exact positiveFragmentValue_nonneg _
  have hdir : DirectedOn (· ≤ ·) d := by
    rintro x ⟨t, rfl⟩ y ⟨u, rfl⟩
    refine ⟨_, ⟨t ∪ u, rfl⟩, ?_, ?_⟩
    · exact (show v t ≤ v (t ∪ u) from Finset.sup_mono Finset.subset_union_left)
    · exact (show v u ≤ v (t ∪ u) from Finset.sup_mono Finset.subset_union_right)
  have hb : BddAbove (norm '' d) := by
    refine ⟨‖e‖, ?_⟩
    rintro r ⟨x, ⟨t, rfl⟩, rfl⟩
    apply norm_le_norm_of_abs_le_abs
    simpa only [abs_of_nonneg (positiveFragmentValue_nonneg _),
      abs_of_nonneg (Fact.out : 0 ≤ e)] using positiveFragmentValue_le (v t)
  obtain ⟨x, hx, u, hu, ht, _⟩ :=
    al_exists_isLUB_of_directed_norm_bdd hAL hd hpos hdir hb
  have hxf : IsPositiveFragment x e := by
    apply (isClosed_positiveFragments e).mem_of_tendsto ht
    exact Filter.Eventually.of_forall fun n => by
      obtain ⟨t, ht⟩ := hu n
      rw [← ht]
      exact positiveFragmentValue_isFragment _
  refine ⟨positiveFragmentOf hxf, ?_, ?_⟩
  · intro a ha
    have h := hx.1 (show positiveFragmentValue (v {⟨a, ha⟩}) ∈ d from ⟨_, rfl⟩)
    simpa [v] using h
  · intro a ha
    change x ≤ positiveFragmentValue a
    apply hx.2
    rintro y ⟨t, rfl⟩
    exact (show v t ≤ a from Finset.sup_le fun b _ => ha b.property)

def positiveFragmentCompleteBoolean : CompleteBooleanAlgebra (PositiveFragmentAlgebra e) := by
  letI : SupSet (PositiveFragmentAlgebra e) :=
    ⟨fun s => (positiveFragment_exists_isLUB hAL e s).choose⟩
  let c : CompleteLattice (PositiveFragmentAlgebra e) := completeLatticeOfSup _
    (fun s => (positiveFragment_exists_isLUB hAL e s).choose_spec)
  exact { (inferInstance : BooleanAlgebra (PositiveFragmentAlgebra e)), c with }

end ThesisCommon
