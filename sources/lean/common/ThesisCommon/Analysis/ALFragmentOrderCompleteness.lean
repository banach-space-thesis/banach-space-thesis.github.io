import ThesisCommon.Analysis.ALFragmentHomogeneity
import ThesisCommon.Analysis.ALOrderCompleteness
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Data.Finset.Lattice.Fold

/-! Actual suprema of arbitrary fragment families are norm limits of finite
joins.  Consequently metric-closed Boolean subalgebras have their suprema
inside the subalgebra.  This is proved from AL norm additivity, without
postulating a complete probability algebra. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [HasSolidNorm E] [CompleteSpace E] [OrderClosedTopology E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
include hAL

theorem positiveFragment_exists_isLUB_finset_limit {e : E} [Fact (0 ≤ e)]
    (s : Set (PositiveFragmentAlgebra e)) :
    ∃ a : PositiveFragmentAlgebra e, IsLUB s a ∧
      ∃ F : ℕ → Finset (PositiveFragmentAlgebra e),
        (∀ n, (F n : Set (PositiveFragmentAlgebra e)) ⊆ s) ∧
        Tendsto (fun n => positiveFragmentValue ((F n).sup id)) atTop
          (𝓝 (positiveFragmentValue a)) := by
  classical
  let c : Set E := {x | ∃ F : Finset (PositiveFragmentAlgebra e),
    (F : Set (PositiveFragmentAlgebra e)) ⊆ s ∧ positiveFragmentValue (F.sup id) = x}
  have hc : c.Nonempty := ⟨0, ∅, by simp, by simp⟩
  have hpos : ∀ x ∈ c, 0 ≤ x := by
    rintro x ⟨F, _, rfl⟩
    exact positiveFragmentValue_nonneg _
  have hdir : DirectedOn (· ≤ ·) c := by
    rintro x ⟨F, hF, rfl⟩ y ⟨G, hG, rfl⟩
    refine ⟨positiveFragmentValue ((F ∪ G).sup id), ⟨F ∪ G, ?_, rfl⟩, ?_, ?_⟩
    · simpa only [Finset.coe_union, union_subset_iff] using And.intro hF hG
    · exact (Finset.sup_mono (Finset.subset_union_left (s₁ := F) (s₂ := G)) :
        F.sup id ≤ (F ∪ G).sup id)
    · exact (Finset.sup_mono (Finset.subset_union_right (s₁ := F) (s₂ := G)) :
        G.sup id ≤ (F ∪ G).sup id)
  have hbound : BddAbove (norm '' c) := by
    refine ⟨‖e‖, ?_⟩
    rintro _ ⟨x, ⟨F, _, rfl⟩, rfl⟩
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (positiveFragmentValue_nonneg _), abs_of_nonneg (Fact.out : 0 ≤ e)]
    exact positiveFragmentValue_le _
  obtain ⟨x, hx, u, hu, hlim, _⟩ := al_exists_isLUB_of_directed_norm_bdd hAL hc hpos hdir hbound
  choose F hF hFu using hu
  have hfrag : IsPositiveFragment x e := by
    apply (isClosed_positiveFragments e).mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    rw [← hFu n]
    exact positiveFragmentValue_isFragment _
  refine ⟨positiveFragmentOf hfrag, ⟨?_, ?_⟩, F, hF, ?_⟩
  · intro a ha
    change positiveFragmentValue a ≤ x
    apply hx.1
    exact ⟨{a}, by simpa using ha, by simp⟩
  · intro b hb
    change x ≤ positiveFragmentValue b
    apply hx.2
    rintro y ⟨F, hF, rfl⟩
    exact (Finset.sup_le (fun a ha => hb (hF ha)) : F.sup id ≤ b)
  · simpa only [hFu] using hlim

theorem positiveFragment_exists_isLUB_of_normCompletion {e : E} [Fact (0 ≤ e)]
    (s : Set (PositiveFragmentAlgebra e)) : ∃ a, IsLUB s a := by
  obtain ⟨a, ha, _⟩ := positiveFragment_exists_isLUB_finset_limit hAL s
  exact ⟨a, ha⟩

theorem positiveFragment_closedSubalgebra_exists_isLUB {e : E} [Fact (0 ≤ e)]
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (s : Set (PositiveFragmentAlgebra e)) (hs : s ⊆ S) :
    ∃ a ∈ S, IsLUB s a := by
  obtain ⟨a, ha, F, hF, hlim⟩ := positiveFragment_exists_isLUB_finset_limit hAL s
  have hclosed : IsClosed (positiveFragmentValue '' (S : Set (PositiveFragmentAlgebra e))) :=
    (isometry_positiveFragmentValue e).isClosedEmbedding.isClosedMap _ hS
  have hmem : positiveFragmentValue a ∈
      positiveFragmentValue '' (S : Set (PositiveFragmentAlgebra e)) := by
    apply hclosed.mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    refine ⟨(F n).sup id, ?_, rfl⟩
    exact (F n).sup_mem _ S.bot_mem (fun _ hx _ hy => S.sup_mem hx hy) _
      (fun b hb => hs (hF n hb))
  obtain ⟨b, hb, heq⟩ := hmem
  exact ⟨a, (positiveFragmentValue_injective e heq) ▸ hb, ha⟩

theorem positiveFragment_closedSubalgebra_exists_isGLB {e : E} [Fact (0 ≤ e)]
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (s : Set (PositiveFragmentAlgebra e)) (hs : s ⊆ S) :
    ∃ a ∈ S, IsGLB s a := by
  obtain ⟨a, ha, hL⟩ := positiveFragment_closedSubalgebra_exists_isLUB hAL S hS
    (compl '' s) (by rintro _ ⟨b, hb, rfl⟩; exact S.compl_mem (hs hb))
  refine ⟨aᶜ, S.compl_mem ha, ⟨?_, ?_⟩⟩
  · intro b hb
    have h := compl_le_compl (hL.1 ⟨b, hb, rfl⟩)
    simpa only [compl_compl] using h
  · intro b hb
    have h : a ≤ bᶜ := hL.2 (by
      rintro _ ⟨c, hc, rfl⟩
      exact compl_le_compl (hb hc))
    simpa only [compl_compl] using compl_le_compl h

/-- The least element of a closed subalgebra covering a specified fragment. -/
theorem positiveFragment_exists_relativeHull {e : E} [Fact (0 ≤ e)]
    (S : BooleanSubalgebra (PositiveFragmentAlgebra e))
    (hS : IsClosed (S : Set (PositiveFragmentAlgebra e)))
    (a : PositiveFragmentAlgebra e) :
    ∃ b ∈ S, a ≤ b ∧ ∀ c ∈ S, a ≤ c → b ≤ c := by
  obtain ⟨b, hb, hG⟩ := positiveFragment_closedSubalgebra_exists_isGLB hAL S hS
    {c | c ∈ S ∧ a ≤ c} (fun _ hc => hc.1)
  exact ⟨b, hb, hG.2 (fun _ hc => hc.2), fun c hc hac => hG.1 ⟨hc, hac⟩⟩

end ThesisCommon

