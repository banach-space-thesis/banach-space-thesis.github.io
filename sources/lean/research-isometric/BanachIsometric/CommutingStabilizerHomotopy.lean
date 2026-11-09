import BanachIsometric.StabilizerExponentialComponent
import BanachIsometric.ConnectedGroupLocalCovering
import BanachIsometric.CoveringHigherHomotopy
import BanachIsometric.VectorHigherHomotopy

/-!
# Actual vanishing of higher homotopy for commuting stabilizer directions

When the actual kernel directions commute in the ambient algebra, their
actual exponential is a group homomorphism from the additive kernel. The
proved identity-component chart makes it a genuine covering. Actual higher
homotopy invariance and vector-space contraction then give vanishing in
every degree at least two. No compact-Lie homotopy assertion is a premise.
-/

noncomputable section
namespace BanachIsometric.StabilizerLieCoordinates

open scoped Topology Topology.Homotopy

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def commutingExponentialHom
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hComm : ∀ X Y : kernel ρ v,
      Commute (UnitaryOrbit.inclusion A (kernel ρ v) X) (UnitaryOrbit.inclusion A (kernel ρ v) Y)) :
    Multiplicative (kernel ρ v) →*
      Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) where
  toFun X := exponentialIdentityComponent ρ v horbit X.toAdd
  map_one' := exponentialIdentityComponent_zero ρ v horbit
  map_mul' X Y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) (X.toAdd + Y.toAdd)) =
      NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) X.toAdd) *
        NormedSpace.exp ℝ (UnitaryOrbit.inclusion A (kernel ρ v) Y.toAdd)
    rw [map_add, NormedSpace.exp_add_of_commute (hComm X.toAdd Y.toAdd)]

theorem isCoveringMap_commutingExponentialHom
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hComm : ∀ X Y : kernel ρ v,
      Commute (UnitaryOrbit.inclusion A (kernel ρ v) X) (UnitaryOrbit.inclusion A (kernel ρ v) Y)) :
    IsCoveringMap (commutingExponentialHom ρ v horbit hComm) := by
  letI : ConnectedSpace (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_connectedComponent (x := (1 : unitaryRepresentationStabilizer ρ v)))
  obtain ⟨e, he0, _he1, he, _hg⟩ :=
    exists_identityComponent_exponential_openPartialHomeomorph ρ v horbit
  let emul : OpenPartialHomeomorph (Multiplicative (kernel ρ v))
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) := e
  have he0mul : (1 : Multiplicative (kernel ρ v)) ∈ emul.source := he0
  have hfun : (emul : Multiplicative (kernel ρ v) →
      Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) =
      commutingExponentialHom ρ v horbit hComm := by
    funext X
    exact congrFun he X.toAdd
  exact isCoveringMap_groupHom_of_identity_chart _ emul he0mul hfun

theorem subsingleton_higherHomotopy_identityComponent_of_commuting_kernel
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hComm : ∀ X Y : kernel ρ v,
      Commute (UnitaryOrbit.inclusion A (kernel ρ v) X) (UnitaryOrbit.inclusion A (kernel ρ v) Y))
    (n : ℕ) : Subsingleton (HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) 1) := by
  let p := commutingExponentialHom ρ v horbit hComm
  have hp : IsCoveringMap p := isCoveringMap_commutingExponentialHom ρ v horbit hComm
  letI : Subsingleton (HomotopyGroup (Fin (n + 2)) (Multiplicative (kernel ρ v)) 1) :=
    subsingleton_homotopyGroup_realVector (V := kernel ρ v) (0 : kernel ρ v)
  have h := (coveringHigherHomotopyEquiv hp (1 : Multiplicative (kernel ρ v)) n).symm.injective.subsingleton
  simpa only [map_one] using h

theorem isOfFinOrder_higherHomotopy_identityComponent_of_commuting_kernel
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v))
    (hComm : ∀ X Y : kernel ρ v,
      Commute (UnitaryOrbit.inclusion A (kernel ρ v) X) (UnitaryOrbit.inclusion A (kernel ρ v) Y))
    (n : ℕ) (α : HomotopyGroup (Fin (n + 2))
      (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) 1) : IsOfFinOrder α := by
  letI := subsingleton_higherHomotopy_identityComponent_of_commuting_kernel ρ v horbit hComm n
  have he : α = 1 := Subsingleton.elim _ _
  rw [he]
  exact IsOfFinOrder.one

end BanachIsometric.StabilizerLieCoordinates
