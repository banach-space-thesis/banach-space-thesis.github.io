import BanachIsometric.BodyGroupConjugation
import BanachIsometric.LieGroupHomeomorphTransport
import BanachIsometric.ProductHigherHomotopy

/-! Continuous multiplicative equivalences transport the actual identity
components and the actual pinned Mathlib homotopy groups. The group maps on
homotopy classes are postcomposition of literal cubical loops. -/

noncomputable section
namespace BanachIsometric
open Set SphereGenerator
open scoped Topology Topology.Homotopy

section Components
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

def identityComponentMulEquiv (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm) :
    Subgroup.connectedComponentOfOne G ≃* Subgroup.connectedComponentOfOne H where
  toFun g := ⟨e g.val, by
    change g.val ∈ e ⁻¹' (Subgroup.connectedComponentOfOne H : Set H)
    rw [preimage_connectedComponentOfOne_of_mulEquiv e he hi]
    exact g.property⟩
  invFun h := ⟨e.symm h.val, by
    change h.val ∈ e.symm ⁻¹' (Subgroup.connectedComponentOfOne G : Set G)
    rw [preimage_connectedComponentOfOne_of_mulEquiv e.symm hi he]
    exact h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

@[simp] theorem identityComponentMulEquiv_coe (e : G ≃* H)
    (he : Continuous e) (hi : Continuous e.symm) (g : Subgroup.connectedComponentOfOne G) :
    (identityComponentMulEquiv e he hi g : H) = e g.val := rfl

theorem continuous_identityComponentMulEquiv (e : G ≃* H)
    (he : Continuous e) (hi : Continuous e.symm) :
    Continuous (identityComponentMulEquiv e he hi) :=
  (he.comp continuous_subtype_val).subtype_mk _

theorem continuous_symm_identityComponentMulEquiv (e : G ≃* H)
    (he : Continuous e) (hi : Continuous e.symm) :
    Continuous (identityComponentMulEquiv e he hi).symm :=
  (hi.comp continuous_subtype_val).subtype_mk _

def identityComponentHomeomorph (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm) :
    Subgroup.connectedComponentOfOne G ≃ₜ Subgroup.connectedComponentOfOne H :=
  mulEquivHomeomorph (identityComponentMulEquiv e he hi)
    (continuous_identityComponentMulEquiv e he hi) (continuous_symm_identityComponentMulEquiv e he hi)

end Components

section Homotopy
variable {N X Y : Type*} [DecidableEq N] [Nonempty N]
  [TopologicalSpace X] [TopologicalSpace Y]

def basedHomeomorphHomotopyEquiv (h : X ≃ₜ Y) (x : X) (y : Y) (hxy : h x = y) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y y := by
  have hyx : h.symm y = x := by rw [← hxy, h.symm_apply_apply]
  let f := basedHomotopyGroupMap (N := N) (⟨h, h.continuous⟩ : C(X, Y)) hxy
  let g := basedHomotopyGroupMap (N := N) (⟨h.symm, h.symm.continuous⟩ : C(Y, X)) hyx
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_mul' := f.map_mul }
  · intro a
    induction a using Quotient.inductionOn with
    | h α =>
      change genLoopClass (mapGenLoop ⟨h.symm, h.symm.continuous⟩ hyx
        (mapGenLoop ⟨h, h.continuous⟩ hxy α)) = genLoopClass α
      congr 1
      ext u
      exact h.symm_apply_apply (α u)
  · intro a
    induction a using Quotient.inductionOn with
    | h α =>
      change genLoopClass (mapGenLoop ⟨h, h.continuous⟩ hxy
        (mapGenLoop ⟨h.symm, h.symm.continuous⟩ hyx α)) = genLoopClass α
      congr 1
      ext u
      exact h.apply_symm_apply (α u)

end Homotopy

section ComponentHomotopy
variable {N G H : Type*} [DecidableEq N] [Nonempty N]
  [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

def identityComponentHomotopyEquiv (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm) :
    HomotopyGroup N (Subgroup.connectedComponentOfOne G) 1 ≃*
      HomotopyGroup N (Subgroup.connectedComponentOfOne H) 1 :=
  basedHomeomorphHomotopyEquiv (identityComponentHomeomorph e he hi) 1 1
    (identityComponentMulEquiv e he hi).map_one

theorem isOfFinOrder_identityComponentHomotopyEquiv_iff
    (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm)
    (α : HomotopyGroup N (Subgroup.connectedComponentOfOne G) 1) :
    IsOfFinOrder (identityComponentHomotopyEquiv e he hi α) ↔ IsOfFinOrder α :=
  (identityComponentHomotopyEquiv e he hi).injective.isOfFinOrder_iff

end ComponentHomotopy
end BanachIsometric
