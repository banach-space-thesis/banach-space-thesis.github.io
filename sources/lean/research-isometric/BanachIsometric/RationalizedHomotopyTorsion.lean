import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.GroupTheory.OrderOfElement

/-!
# Actual rationalization detects the precise remaining homotopy obstruction

An actual class has finite order exactly when its image in the localization
of its additive group at the nonzero integers is zero. Thus only rational
vanishing, not finite generation or finiteness of the integral homotopy group,
is needed in the bundle argument. This file proves that algebraic equivalence;
it does not assume or prove rational vanishing for a compact Lie group.
-/

noncomputable section
namespace BanachIsometric

open scoped Topology.Homotopy

theorem localized_int_map_eq_zero_iff_finAddOrder
    {M : Type*} [AddCommGroup M] (x : M) (s : nonZeroDivisors ℤ) :
    LocalizedModule.mk x s = 0 ↔ IsOfFinAddOrder x := by
  rw [← LocalizedModule.zero_mk (1 : nonZeroDivisors ℤ), LocalizedModule.mk_eq]
  simp only [one_smul, smul_zero]
  constructor
  · rintro ⟨s, hs⟩
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨s.val, mem_nonZeroDivisors_iff_ne_zero.mp s.property, hs⟩
  · intro h
    obtain ⟨s, hs, hsmul⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp h
    exact ⟨⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr hs⟩, hsmul⟩

theorem subsingleton_localized_int_iff_finAddOrder
    (M : Type*) [AddCommGroup M] :
    Subsingleton (LocalizedModule (nonZeroDivisors ℤ) M) ↔ ∀ x : M, IsOfFinAddOrder x := by
  constructor
  · intro h x
    exact (localized_int_map_eq_zero_iff_finAddOrder x 1).mp (h.elim _ _)
  · intro h
    have hz : ∀ z : LocalizedModule (nonZeroDivisors ℤ) M, z = 0 := by
      intro z
      induction z using LocalizedModule.induction_on with
      | _ m s => exact (localized_int_map_eq_zero_iff_finAddOrder m s).mpr (h m)
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

local instance compatibleHigherHomotopyCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) :
    CommGroup (HomotopyGroup (Fin (n + 2)) X x) where
  __ := HomotopyGroup.group (Fin (n + 2))
  mul_comm a b := by
    letI : CommGroup (HomotopyGroup (Fin (n + 2)) X x) :=
      HomotopyGroup.commGroup
    exact mul_comm a b

abbrev RationalizedHigherHomotopy (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) :=
  LocalizedModule (nonZeroDivisors ℤ) (Additive (HomotopyGroup (Fin (n + 2)) X x))

def rationalizedHigherHomotopyRatModule
    (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) :
    Module ℚ (RationalizedHigherHomotopy n X x) := inferInstance

theorem rationalizedHigherHomotopy_map_eq_zero_iff
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (α : HomotopyGroup (Fin (n + 2)) X x) :
    LocalizedModule.mk (Additive.ofMul α) (1 : nonZeroDivisors ℤ) = 0 ↔
      IsOfFinOrder α := by
  rw [localized_int_map_eq_zero_iff_finAddOrder]
  rw [isOfFinAddOrder_iff_nsmul_eq_zero, isOfFinOrder_iff_pow_eq_one]
  rfl

theorem subsingleton_rationalizedHigherHomotopy_iff
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X) :
    Subsingleton (RationalizedHigherHomotopy n X x) ↔
      ∀ α : HomotopyGroup (Fin (n + 2)) X x, IsOfFinOrder α := by
  rw [subsingleton_localized_int_iff_finAddOrder]
  constructor
  · intro h α
    exact (rationalizedHigherHomotopy_map_eq_zero_iff n x α).mp
      ((localized_int_map_eq_zero_iff_finAddOrder (Additive.ofMul α) 1).mpr (h _))
  · intro h α
    exact (localized_int_map_eq_zero_iff_finAddOrder α 1).mp
      ((rationalizedHigherHomotopy_map_eq_zero_iff n x (Additive.toMul α)).mpr (h _))

end BanachIsometric
