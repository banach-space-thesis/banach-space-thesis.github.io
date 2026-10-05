import ThesisCommon.Analysis.BanachLattice
import Mathlib.Algebra.Module.Shrink
import Mathlib.Order.Shrink
import Mathlib.Logic.Small.Basic

/-! Transport of an arbitrary real Banach lattice to a smaller universe.
The target has the transported norm, so this does not assume that the
original norm of an isomorphic space is solid. -/
noncomputable section
universe u v w
namespace ThesisCommon

def shrinkLatticeNormedGroup (F : RealBanachLattice.{u}) [Small.{v} F] :
    NormedAddCommGroup (Shrink.{v} F) :=
  NormedAddCommGroup.induced _ _ (Shrink.linearEquiv ℝ F).toAddEquiv.toAddMonoidHom
    (Shrink.linearEquiv ℝ F).injective

attribute [local instance] shrinkLatticeNormedGroup

def shrinkLatticeNormedSpace (F : RealBanachLattice.{u}) [Small.{v} F] :
    NormedSpace ℝ (Shrink.{v} F) :=
  NormedSpace.induced ℝ _ _ (Shrink.linearEquiv ℝ F)

attribute [local instance] shrinkLatticeNormedSpace

def shrinkLatticeIsometry (F : RealBanachLattice.{u}) [Small.{v} F] :
    Shrink.{v} F ≃ₗᵢ[ℝ] F :=
  { Shrink.linearEquiv ℝ F with norm_map' := fun _ => rfl }

def shrinkLatticeComplete (F : RealBanachLattice.{u}) [Small.{v} F] :
    CompleteSpace (Shrink.{v} F) :=
  (shrinkLatticeIsometry F).toIsometryEquiv.completeSpace

def shrinkLatticeOrder (F : RealBanachLattice.{u}) [Small.{v} F] :
    Lattice (Shrink.{v} F) where
  __ := inferInstanceAs (PartialOrder (Shrink.{v} F))
  sup x y := equivShrink F ((equivShrink F).symm x ⊔ (equivShrink F).symm y)
  inf x y := equivShrink F ((equivShrink F).symm x ⊓ (equivShrink F).symm y)
  le_sup_left x y := by change _ ≤ (equivShrink F).symm _; simp
  le_sup_right x y := by change _ ≤ (equivShrink F).symm _; simp
  sup_le x y z hx hy := by
    change (equivShrink F).symm _ ≤ _
    simpa using sup_le hx hy
  inf_le_left x y := by change (equivShrink F).symm _ ≤ _; simp
  inf_le_right x y := by change (equivShrink F).symm _ ≤ _; simp
  le_inf x y z hy hz := by
    change _ ≤ (equivShrink F).symm _
    simpa using le_inf hy hz

attribute [local instance] shrinkLatticeOrder

def shrinkLatticeOrderedAdd (F : RealBanachLattice.{u}) [Small.{v} F] :
    IsOrderedAddMonoid (Shrink.{v} F) where
  add_le_add_left a b hab c := by
    change (Shrink.linearEquiv ℝ F) (c + a) ≤ (Shrink.linearEquiv ℝ F) (c + b)
    rw [map_add, map_add]
    have hab' : (Shrink.linearEquiv ℝ F) a ≤ (Shrink.linearEquiv ℝ F) b := hab
    exact add_le_add_left hab' _

def shrinkLatticeOrderedModule (F : RealBanachLattice.{u}) [Small.{v} F] :
    IsOrderedModule ℝ (Shrink.{v} F) where
  smul_le_smul_of_nonneg_left a ha b c hbc := by
    change (Shrink.linearEquiv ℝ F) (a • b) ≤ (Shrink.linearEquiv ℝ F) (a • c)
    rw [map_smul, map_smul]
    exact smul_le_smul_of_nonneg_left hbc ha
  smul_le_smul_of_nonneg_right b hb a c hac := by
    change (Shrink.linearEquiv ℝ F) (a • b) ≤ (Shrink.linearEquiv ℝ F) (c • b)
    rw [map_smul, map_smul]
    have hb' : 0 ≤ (Shrink.linearEquiv ℝ F) b := by
      change (Shrink.linearEquiv ℝ F) 0 ≤ (Shrink.linearEquiv ℝ F) b at hb
      simpa only [map_zero] using hb
    exact smul_le_smul_of_nonneg_right hac hb'

theorem shrinkLattice_map_abs (F : RealBanachLattice.{u}) [Small.{v} F]
    (x : Shrink.{v} F) :
    (Shrink.linearEquiv ℝ F) |x| = |(Shrink.linearEquiv ℝ F) x| := by
  change (equivShrink F).symm
    (equivShrink F ((equivShrink F).symm x ⊔ (equivShrink F).symm (-x))) = _
  rw [Equiv.symm_apply_apply]
  change (Shrink.linearEquiv ℝ F) x ⊔ (Shrink.linearEquiv ℝ F) (-x) = _
  rw [map_neg]
  rfl

def shrinkLatticeSolid (F : RealBanachLattice.{u}) [Small.{v} F] :
    HasSolidNorm (Shrink.{v} F) where
  solid x y h := by
    change ‖(Shrink.linearEquiv ℝ F) x‖ ≤ ‖(Shrink.linearEquiv ℝ F) y‖
    apply norm_le_norm_of_abs_le_abs
    change (Shrink.linearEquiv ℝ F) |x| ≤ (Shrink.linearEquiv ℝ F) |y| at h
    simpa only [shrinkLattice_map_abs] using h

/-- A small Banach lattice admits a lattice representative in the smaller
universe, with an actual linear isometry to the original lattice. -/
def shrinkRealBanachLattice (F : RealBanachLattice.{u}) [Small.{v} F] :
    RealBanachLattice.{v} where
  Carrier := Shrink.{v} F
  normedAddCommGroup := shrinkLatticeNormedGroup F
  normedSpace := shrinkLatticeNormedSpace F
  completeSpace := shrinkLatticeComplete F
  lattice := shrinkLatticeOrder F
  orderedAdd := shrinkLatticeOrderedAdd F
  orderedModule := shrinkLatticeOrderedModule F
  solidNorm := shrinkLatticeSolid F

def shrinkRealBanachLatticeEquiv (F : RealBanachLattice.{u}) [Small.{v} F] :
    shrinkRealBanachLattice F ≃L[ℝ] F :=
  (shrinkLatticeIsometry F).toContinuousLinearEquiv

/-- Existence of a Banach lattice model does not depend on allowing larger
universes for the representative. -/
theorem isomorphicToBanachLattice_of_equiv_any_universe
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : RealBanachLattice.{v}) (e : E ≃L[ℝ] F) : IsomorphicToBanachLattice E := by
  letI : Small.{u} F := small_of_injective e.symm.injective
  exact ⟨shrinkRealBanachLattice F, ⟨e.trans (shrinkRealBanachLatticeEquiv F).symm⟩⟩

theorem not_isomorphicToBanachLattice_of_equiv
    {E : Type u} {G : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] G) (h : ¬ IsomorphicToBanachLattice E) :
    ¬ IsomorphicToBanachLattice G := by
  rintro ⟨F, ⟨f⟩⟩
  exact h (isomorphicToBanachLattice_of_equiv_any_universe E F (e.trans f))

end ThesisCommon
