import BanachIsometric.HomotopyRepetition
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Basic

/-! The actual identity component of a totally disconnected group is a
singleton. Its actual cubical homotopy groups are therefore trivial. -/

namespace BanachIsometric

open scoped Topology Topology.Homotopy

theorem connectedComponentOfOne_subsingleton_of_totallyDisconnected
    (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] : Subsingleton (Subgroup.connectedComponentOfOne G) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  exact (isPreconnected_connectedComponent (x := (1 : G))).subsingleton x.property y.property

theorem homotopyGroup_subsingleton_of_subsingleton
    (N X : Type*) [TopologicalSpace X] [Subsingleton X] (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  refine ⟨fun α β => ?_⟩
  refine Quotient.inductionOn₂ α β ?_
  intro f g
  have he : f = g := by
    ext u
    exact Subsingleton.elim _ _
  exact congrArg Quotient.mk' he

theorem isOfFinOrder_homotopyGroup_identityComponent_of_totallyDisconnected
    {G N : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [DecidableEq N] [Nonempty N]
    (α : HomotopyGroup N (Subgroup.connectedComponentOfOne G) 1) : IsOfFinOrder α := by
  letI := connectedComponentOfOne_subsingleton_of_totallyDisconnected G
  letI := homotopyGroup_subsingleton_of_subsingleton N (Subgroup.connectedComponentOfOne G) 1
  have he : α = 1 := Subsingleton.elim _ _
  rw [he]
  exact IsOfFinOrder.one

theorem isOfFinOrder_homotopyGroup_identityComponent_of_finite
    {G N : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] [Finite G] [DecidableEq N] [Nonempty N]
    (α : HomotopyGroup N (Subgroup.connectedComponentOfOne G) 1) : IsOfFinOrder α := by
  exact isOfFinOrder_homotopyGroup_identityComponent_of_totallyDisconnected α

end BanachIsometric
