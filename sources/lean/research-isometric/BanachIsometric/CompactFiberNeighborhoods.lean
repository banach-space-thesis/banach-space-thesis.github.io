import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Compact

/-!
# Actual disjoint neighborhoods of a finite compact-source fiber

The closed root balls are chosen inside the source interior and any supplied
positive radius bounds. Compactness of the source outside the union of open
root balls gives exact source excision for every target close to the original
value. No local inverse, index additivity or finite-fiber stability is assumed.
-/

namespace BanachIsometric

open Set Metric
open scoped Topology

noncomputable section

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

theorem exists_disjoint_compact_fiber_balls
    {f : E → F} (hf : Continuous f) {S : Set E} (hS : IsCompact S) (c : F)
    (hfin : {x : E | x ∈ S ∧ f x = c}.Finite)
    (hinterior : ∀ x ∈ S, f x = c → x ∈ interior S)
    (r : {x : E // x ∈ S ∧ f x = c} → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ s : {x : E // x ∈ S ∧ f x = c} → ℝ,
      (∀ x, 0 < s x ∧ s x ≤ r x) ∧
      (∀ x, closedBall x.val (s x) ⊆ interior S) ∧
      Pairwise (fun x y => Disjoint (closedBall x.val (s x)) (closedBall y.val (s y))) ∧
      ∃ δ > 0, ∀ y ∈ ball c δ, ∀ z, f z = y →
        (z ∈ S ↔ z ∈ ⋃ x, closedBall x.val (s x)) := by
  classical
  let R : Set E := {x | x ∈ S ∧ f x = c}
  obtain ⟨U, hU, hsep⟩ := hfin.t2_separation
  have hex (x : R) : ∃ ε > 0, ball x.val ε ⊆ U x.val ∩ interior S := by
    apply Metric.isOpen_iff.mp ((hU x.val).2.inter isOpen_interior)
    exact ⟨(hU x.val).1, hinterior x.val x.property.1 x.property.2⟩
  choose ε hε hεsub using hex
  let s : R → ℝ := fun x => min (r x) (ε x / 2)
  have hs (x : R) : 0 < s x ∧ s x ≤ r x :=
    ⟨lt_min (hr x) (half_pos (hε x)), min_le_left _ _⟩
  have hsU (x : R) : closedBall x.val (s x) ⊆ U x.val ∩ interior S := by
    apply (closedBall_subset_ball (show s x < ε x from
      (min_le_right _ _).trans_lt (half_lt_self (hε x)))).trans
    exact hεsub x
  have hdisjoint : Pairwise (fun x y : R =>
      Disjoint (closedBall x.val (s x)) (closedBall y.val (s y))) := by
    intro x y hxy
    have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    exact (hsep x.property y.property hne).mono (fun z hz => (hsU x hz).1)
      (fun z hz => (hsU y hz).1)
  let O : Set E := ⋃ x : R, ball x.val (s x)
  have hO : IsOpen O := isOpen_iUnion (fun _ => isOpen_ball)
  have hcompact : IsCompact (S \ O) := hS.diff hO
  have hc : c ∉ f '' (S \ O) := by
    rintro ⟨z, hz, hzc⟩
    let x : R := ⟨z, hz.1, hzc⟩
    apply hz.2
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hs x).1⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp
    (hcompact.image hf).isClosed.isOpen_compl c hc
  refine ⟨s, hs, (fun x z hz => (hsU x hz).2), hdisjoint, δ, hδ, ?_⟩
  intro y hy z hzy
  constructor
  · intro hz
    by_contra hnot
    have hzO : z ∉ O := by
      intro hzo
      obtain ⟨x, hzx⟩ := mem_iUnion.mp hzo
      exact hnot (mem_iUnion.mpr ⟨x, ball_subset_closedBall hzx⟩)
    exact hδsub hy ⟨z, ⟨hz, hzO⟩, hzy⟩
  · intro hz
    obtain ⟨x, hzx⟩ := mem_iUnion.mp hz
    exact interior_subset ((hsU x hzx).2)

end

end BanachIsometric
