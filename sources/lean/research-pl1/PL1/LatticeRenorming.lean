import PL1.LatticeBridge
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Topology.Bases

/-!+# Realization of equivalent lattice norms

The predicate in `LatticeDefinitions` is realized by a separate type carrying
the new norm. The equivalence retains the original addition and real action.
No order-completeness or atomicity assertion is used here.
-/

noncomputable section
open TopologicalSpace
universe u

namespace PL1.LatticeRenorming

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A copy of the original vector space on which a separating seminorm is used
as the norm. Keeping a separate type prevents changing the source norm. -/
def Space (p : Seminorm ℝ E) (_hsep : ∀ x, p x = 0 → x = 0) : Type u := E

variable (p : Seminorm ℝ E) (hsep : ∀ x, p x = 0 → x = 0)

instance : AddCommGroup (Space p hsep) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (Space p hsep) := inferInstanceAs (Module ℝ E)

instance : NormedAddCommGroup (Space p hsep) :=
  (show AddGroupNorm (Space p hsep) from
    { p.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := hsep }).toNormedAddCommGroup

@[simp] theorem norm_eq (x : Space p hsep) : ‖x‖ = p x := rfl

instance : NormedSpace ℝ (Space p hsep) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le

/-- The unchanged linear coordinates between the original and renormed spaces. -/
def linearEquiv : E ≃ₗ[ℝ] Space p hsep :=
  { toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] theorem linearEquiv_symm_apply (x : Space p hsep) :
    (linearEquiv p hsep).symm x = (show E from x) := rfl

/-- Equivalence of norms gives a continuous linear equivalence to the new norm. -/
def equiv (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ x : E, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖) :
    E ≃L[ℝ] Space p hsep :=
  { linearEquiv p hsep with
    continuous_toFun := ((linearEquiv p hsep).toLinearMap.mkContinuous b
      (fun x => (hbounds x).2)).continuous
    continuous_invFun := ((linearEquiv p hsep).symm.toLinearMap.mkContinuous a⁻¹
      (fun x => by
        change _ ≤ a⁻¹ * p x
        rw [← div_eq_inv_mul]
        apply (le_div_iff₀ ha).mpr
        convert (hbounds ((linearEquiv p hsep).symm x)).1 using 1 <;>
          first | rfl | exact mul_comm (_ : ℝ) _)).continuous }

theorem completeSpace [CompleteSpace E] (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ x : E, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖) :
    CompleteSpace (Space p hsep) := by
  let e := equiv p hsep a b ha hbounds
  let e' : E ≃ᵤ Space p hsep :=
    { e.toEquiv with
      uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous }
  exact e'.completeSpace_iff.mp inferInstance

theorem separableSpace [SeparableSpace E] (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ x : E, a * ‖x‖ ≤ p x ∧ p x ≤ b * ‖x‖) :
    SeparableSpace (Space p hsep) := by
  let e := equiv p hsep a b ha hbounds
  exact e.surjective.denseRange.separableSpace e.continuous

instance [Lattice E] : Lattice (Space p hsep) := inferInstanceAs (Lattice E)
instance [Lattice E] [IsOrderedAddMonoid E] : IsOrderedAddMonoid (Space p hsep) :=
  inferInstanceAs (IsOrderedAddMonoid E)
instance [Lattice E] [PosSMulMono ℝ E] : PosSMulMono ℝ (Space p hsep) :=
  inferInstanceAs (PosSMulMono ℝ E)

/-- The assumed solid seminorm becomes an actual normed vector lattice. -/
@[reducible] def normedVectorLattice [Lattice E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]
    (hsolid : ∀ x y : E, |x| ≤ |y| → p x ≤ p y) :
    NormedVectorLattice (Space p hsep) where
  solid := fun {x y} hxy => hsolid x y hxy
  norm_smul := fun a x => map_smul_eq_mul p a x

end PL1.LatticeRenorming

namespace PL1

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Existence of an actual BanLat Banach lattice continuously linearly
equivalent to the given real normed space, in the same universe. -/
def HasBanachLatticeModel (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ (F : Type u) (nF : NormedAddCommGroup F),
    letI := nF
    ∃ lF : Lattice F,
      letI := lF
      ∃ oF : IsOrderedAddMonoid F,
        letI := oF
        ∃ bF : BanachLattice F,
          letI := bF
          Nonempty (E ≃L[ℝ] F)

/-- The reviewed equivalent-norm predicate really produces an actual Banach
lattice, preserving the vector-space operations and completeness. -/
theorem HasEquivalentRealLatticeNorm.hasBanachLatticeModel [CompleteSpace E]
    (h : HasEquivalentRealLatticeNorm E) : HasBanachLatticeModel E := by
  obtain ⟨lE, ho, hs, p, hsolid, a, b, ha, _hb, hbounds⟩ := h
  let : Lattice E := lE
  let : IsOrderedAddMonoid E := ho
  let : PosSMulMono ℝ E := hs
  have hsep : ∀ x : E, p x = 0 → x = 0 := by
    intro x hx
    apply norm_eq_zero.mp
    have hl := (hbounds x).1
    rw [hx] at hl
    have hle : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact le_antisymm hle (norm_nonneg x)
  let : NormedVectorLattice (LatticeRenorming.Space p hsep) :=
    LatticeRenorming.normedVectorLattice p hsep hsolid
  let : CompleteSpace (LatticeRenorming.Space p hsep) :=
    LatticeRenorming.completeSpace p hsep a b ha hbounds
  let : BanachLattice (LatticeRenorming.Space p hsep) := {}
  exact ⟨LatticeRenorming.Space p hsep, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨LatticeRenorming.equiv p hsep a b ha hbounds⟩⟩

/-- Exact equivalence between the reviewed predicate and existence of an
isomorphic BanLat model. Completeness is assumed only for the forward direction. -/
theorem hasEquivalentRealLatticeNorm_iff_hasBanachLatticeModel [CompleteSpace E] :
    HasEquivalentRealLatticeNorm E ↔ HasBanachLatticeModel E := by
  constructor
  · exact HasEquivalentRealLatticeNorm.hasBanachLatticeModel
  · rintro ⟨F, nF, lF, oF, bF, ⟨e⟩⟩
    let := nF
    let := lF
    let := oF
    let := bF
    exact hasEquivalentRealLatticeNorm_of_continuousLinearEquiv e

/-- A separable source transfers its separability to any Banach lattice model.
This form allows applying isomorphism-invariant conclusions without exporting
an auxiliary choice of norm or lattice order on the original type. -/
theorem HasEquivalentRealLatticeNorm.elim_separable [CompleteSpace E] [SeparableSpace E]
    (h : HasEquivalentRealLatticeNorm E) {P : Prop}
    (hP : ∀ (F : Type u) [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
      [BanachLattice F] [SeparableSpace F], (E ≃L[ℝ] F) → P) : P := by
  obtain ⟨F, nF, lF, oF, bF, ⟨e⟩⟩ := h.hasBanachLatticeModel
  let := nF
  let := lF
  let := oF
  let := bF
  let : SeparableSpace F := e.surjective.denseRange.separableSpace e.continuous
  exact hP F e

end PL1
