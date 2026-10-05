import ThesisCommon.Analysis.BandProjection
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Order-convergent nets and the source meaning of an order-closed ideal.

`OrderConverges f l x` uses the usual order-convergence criterion: there is
a nonempty downward-directed family of nonnegative errors with infimum zero,
and `|f i - x|` is eventually bounded by each error. The filter is proper.
The control family need not have the same index set as the converging net.
For a directed net its filter is `atTop`.

The two control-net lemmas relate this formulation to decreasing nets with
infimum zero. A control set is itself such a net, indexed by its order dual;
conversely the range of any antitone control net is a valid control set.
Thus the definition does not replace order convergence by norm convergence,
sequence convergence, or a restriction to monotone converging nets.

The closure proof uses the already constructed band projection. It assumes
neither order continuity of that projection nor closure under order limits.
-/
noncomputable section
open Set Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon

section Convergence
variable {E : Type*} [AddCommGroup E] [Lattice E]
variable {α : Type*} (f : α → E) (l : Filter α) (x : E)

/-- Order convergence along a proper filter, with an independent family of
positive controls decreasing to zero. -/
def OrderConverges : Prop :=
  NeBot l ∧ ∃ B : Set E, B.Nonempty ∧ (∀ b ∈ B, 0 ≤ b) ∧ DirectedOn (· ≥ ·) B ∧
    IsGLB B 0 ∧ ∀ b ∈ B, ∀ᶠ i in l, |f i - x| ≤ b

variable {f l x}

/-- Every usual antitone control net with infimum zero gives the control-set
form of order convergence. No countability of either index set is required. -/
theorem orderConverges_of_antitone_control [NeBot l] {β : Type*} [Preorder β]
    [Nonempty β] [IsDirected β (· ≤ ·)] (b : β → E) (hb : Antitone b)
    (hglb : IsGLB (range b) 0)
    (hbound : ∀ j, ∀ᶠ i in l, |f i - x| ≤ b j) : OrderConverges f l x := by
  refine ⟨inferInstance, range b, range_nonempty b, ?_, ?_, hglb, ?_⟩
  · exact fun y hy => hglb.1 hy
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨b k, ⟨k, rfl⟩, hb hik, hb hjk⟩
  · rintro _ ⟨j, rfl⟩
    exact hbound j

/-- Conversely, the controls of an order-convergent filter form a nonempty
directed index set under the reversed inherited order, and their inclusion
is an antitone control net with infimum zero. Together with
`orderConverges_of_antitone_control`, this gives the usual control-net
interpretation without a same-index or countability restriction. -/
theorem OrderConverges.exists_antitone_control (h : OrderConverges f l x) :
    ∃ B : Set E, B.Nonempty ∧ IsDirected Bᵒᵈ (· ≤ ·) ∧
      Antitone (fun b : Bᵒᵈ => (OrderDual.ofDual b).val) ∧
      IsGLB (range (fun b : Bᵒᵈ => (OrderDual.ofDual b).val)) 0 ∧
      ∀ b : Bᵒᵈ, ∀ᶠ i in l, |f i - x| ≤ (OrderDual.ofDual b).val := by
  obtain ⟨_, B, hB, _, hdir, hglb, hbound⟩ := h
  refine ⟨B, hB, ⟨?_⟩, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨c, hc, hac, hbc⟩ := hdir (OrderDual.ofDual a).val
      (OrderDual.ofDual a).property (OrderDual.ofDual b).val (OrderDual.ofDual b).property
    exact ⟨OrderDual.toDual ⟨c, hc⟩, hac, hbc⟩
  · intro a b hab
    exact hab
  · have hrange : range (fun b : Bᵒᵈ => (OrderDual.ofDual b).val) = B := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact (OrderDual.ofDual b).property
      · intro hy
        exact ⟨OrderDual.toDual ⟨y, hy⟩, rfl⟩
    rw [hrange]
    exact hglb
  · intro b
    exact hbound (OrderDual.ofDual b).val (OrderDual.ofDual b).property

end Convergence

section BandClosure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable {I : Submodule ℝ E}
namespace IsOrderClosedIdeal
variable (hI : IsOrderClosedIdeal I)
include hI

/-- An approximation criterion stronger than the required net closure.
The approximation errors need only have greatest lower bound zero; neither
directedness nor any convergence of the approximants is assumed here. -/
theorem mem_of_order_approximation {B : Set E} {x : E} (hB : IsGLB B 0)
    (hx : ∀ b ∈ B, ∃ y ∈ I, |x - y| ≤ b) : x ∈ I := by
  let Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - bandProjection hI
  have hQ : 0 ≤ Q := sub_nonneg.mpr hI.bandProjection_le_id
  have hQle : Q ≤ ContinuousLinearMap.id ℝ E := by
    intro z hz
    change z - bandProjection hI z ≤ z
    exact sub_le_self z (hI.bandProjection_nonneg z hz)
  have hzero : |Q x| ≤ 0 := hB.2 (by
    intro b hb
    obtain ⟨y, hy, hxy⟩ := hx b hb
    have hQy : Q y = 0 := by
      change y - bandProjection hI y = 0
      rw [hI.bandProjection_eq_self hy, sub_self]
    calc
      |Q x| = |Q (x - y)| := by rw [map_sub, hQy, sub_zero]
      _ ≤ Q |x - y| := abs_apply_le_of_positive hQ (x - y)
      _ ≤ |x - y| := hQle _ (abs_nonneg _)
      _ ≤ b := hxy)
  have hQx : Q x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_abs_eq_norm, le_antisymm hzero (abs_nonneg _), norm_zero]
  have hxP : x = bandProjection hI x := sub_eq_zero.mp hQx
  rw [hxP]
  exact hI.bandProjection_mem x

/-- The directed-supremum definition of `IsOrderClosedIdeal` implies the
source definition: every order limit of a net in the ideal belongs to it.
The stronger filter statement allows eventual, rather than everywhere,
membership in the ideal. -/
theorem mem_of_orderConverges {α : Type*} {f : α → E} {l : Filter α}
    {x : E} (hf : ∀ᶠ i in l, f i ∈ I) (hconv : OrderConverges f l x) : x ∈ I := by
  letI : NeBot l := hconv.1
  obtain ⟨_, B, _, _, _, hB, hbound⟩ := hconv
  apply hI.mem_of_order_approximation hB
  intro b hb
  obtain ⟨i, hiI, hib⟩ := (hf.and (hbound b hb)).exists
  exact ⟨f i, hiI, by simpa only [abs_sub_comm] using hib⟩

/-- Explicit net form, for arbitrary nonempty directed index preorders. -/
theorem mem_of_orderConverges_net {α : Type*} [Preorder α]
    [Nonempty α] [IsDirected α (· ≤ ·)] {f : α → E} {x : E}
    (hf : ∀ i, f i ∈ I) (hconv : OrderConverges f atTop x) : x ∈ I :=
  hI.mem_of_orderConverges (Eventually.of_forall hf) hconv

end IsOrderClosedIdeal
end BandClosure
end ThesisCommon
