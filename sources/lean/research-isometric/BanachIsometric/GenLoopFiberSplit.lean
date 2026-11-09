import BanachIsometric.CubeHalfCoordinates
import Mathlib.SetTheory.Cardinal.Finite

/-! The literal fiber of cubical concatenation over a non-basepoint is the
disjoint sum of the two literal fibers. The maps are the actual affine
half-cube embeddings, not an assumed degree/additivity law. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy unitInterval

variable {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x z : X}

omit [DecidableEq N] in
theorem genLoop_fiber_coordinate_pos (f : GenLoop N X x) (hz : z ≠ x)
    (u : {u : N → unitInterval // f u = z}) (i : N) : 0 < (u.val i : ℝ) := by
  have hne : (u.val i : ℝ) ≠ 0 := by
    intro he
    have hu : u.val ∈ Cube.boundary N := ⟨i, Or.inl (Subtype.ext he)⟩
    exact hz (u.property.symm.trans (f.property u.val hu))
  exact lt_of_le_of_ne (u.val i).property.1 (Ne.symm hne)

theorem leftHalfCube_coordinate_le (i : N) (u : N → unitInterval) :
    (leftHalfCube i u i : ℝ) ≤ 1 / 2 := by
  change (Function.update u i _ i : ℝ) ≤ 1 / 2
  rw [Function.update_self]
  change (u i : ℝ) / 2 ≤ 1 / 2
  linarith [(u i).property.2]

theorem rightHalfCube_fiber_coordinate_gt (i : N) (g : GenLoop N X x) (hz : z ≠ x)
    (u : {u : N → unitInterval // g u = z}) :
    1 / 2 < (rightHalfCube i u.val i : ℝ) := by
  change 1 / 2 < (Function.update u.val i _ i : ℝ)
  rw [Function.update_self]
  change 1 / 2 < ((u.val i : ℝ) + 1) / 2
  linarith [genLoop_fiber_coordinate_pos g hz u i]

def transAtLeftFiber (i : N) (f g : GenLoop N X x)
    (u : {u : N → unitInterval // f u = z}) :
    {v : N → unitInterval // GenLoop.transAt i f g v = z} := by
  refine ⟨leftHalfCube i u.val, ?_⟩
  have hu := leftHalfCube_coordinate_le i u.val
  simp only [GenLoop.transAt, GenLoop.coe_copy, if_pos hu]
  change f (leftExpandCube i (leftHalfCube i u.val)) = z
  rw [leftExpand_leftHalfCube]
  exact u.property

def transAtRightFiber (i : N) (f g : GenLoop N X x) (hz : z ≠ x)
    (u : {u : N → unitInterval // g u = z}) :
    {v : N → unitInterval // GenLoop.transAt i f g v = z} := by
  refine ⟨rightHalfCube i u.val, ?_⟩
  have hu := rightHalfCube_fiber_coordinate_gt i g hz u
  simp only [GenLoop.transAt, GenLoop.coe_copy, if_neg (not_le.mpr hu)]
  change g (rightExpandCube i (rightHalfCube i u.val)) = z
  rw [rightExpand_rightHalfCube]
  exact u.property

def transAtFiberMap (i : N) (f g : GenLoop N X x) (hz : z ≠ x) :
    ({u : N → unitInterval // f u = z} ⊕ {u : N → unitInterval // g u = z}) →
      {u : N → unitInterval // GenLoop.transAt i f g u = z} :=
  Sum.elim (transAtLeftFiber i f g) (transAtRightFiber i f g hz)

theorem transAtFiberMap_injective (i : N) (f g : GenLoop N X x) (hz : z ≠ x) :
    Function.Injective (transAtFiberMap i f g hz) := by
  rintro (u | u) (v | v) he
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hv := congrArg (fun w => leftExpandCube i w.val) he
    change leftExpandCube i (leftHalfCube i u.val) = leftExpandCube i (leftHalfCube i v.val) at hv
    simpa only [leftExpand_leftHalfCube] using hv
  · exfalso
    have he' := congrArg (fun w => (w.val i : ℝ)) he
    change (leftHalfCube i u.val i : ℝ) = (rightHalfCube i v.val i : ℝ) at he'
    have hl := leftHalfCube_coordinate_le i u.val
    have hr := rightHalfCube_fiber_coordinate_gt i g hz v
    linarith
  · exfalso
    have he' := congrArg (fun w => (w.val i : ℝ)) he
    change (rightHalfCube i u.val i : ℝ) = (leftHalfCube i v.val i : ℝ) at he'
    have hl := leftHalfCube_coordinate_le i v.val
    have hr := rightHalfCube_fiber_coordinate_gt i g hz u
    linarith
  · apply congrArg Sum.inr
    apply Subtype.ext
    have hv := congrArg (fun w => rightExpandCube i w.val) he
    change rightExpandCube i (rightHalfCube i u.val) = rightExpandCube i (rightHalfCube i v.val) at hv
    simpa only [rightExpand_rightHalfCube] using hv

theorem transAtFiberMap_surjective (i : N) (f g : GenLoop N X x) (hz : z ≠ x) :
    Function.Surjective (transAtFiberMap i f g hz) := by
  intro u
  by_cases hu : (u.val i : ℝ) ≤ 1 / 2
  · have hleft : f (leftExpandCube i u.val) = z := by
      have h := u.property
      simpa only [GenLoop.transAt, GenLoop.coe_copy, if_pos hu] using h
    refine ⟨Sum.inl ⟨leftExpandCube i u.val, hleft⟩, ?_⟩
    apply Subtype.ext
    exact leftHalf_leftExpandCube i u.val hu
  · have hright : g (rightExpandCube i u.val) = z := by
      have h := u.property
      simpa only [GenLoop.transAt, GenLoop.coe_copy, if_neg hu] using h
    refine ⟨Sum.inr ⟨rightExpandCube i u.val, hright⟩, ?_⟩
    apply Subtype.ext
    exact rightHalf_rightExpandCube i u.val (le_of_not_ge hu)

def transAtFiberEquiv (i : N) (f g : GenLoop N X x) (hz : z ≠ x) :
    ({u : N → unitInterval // f u = z} ⊕ {u : N → unitInterval // g u = z}) ≃
      {u : N → unitInterval // GenLoop.transAt i f g u = z} :=
  Equiv.ofBijective (transAtFiberMap i f g hz)
    ⟨transAtFiberMap_injective i f g hz, transAtFiberMap_surjective i f g hz⟩

end BanachIsometric
