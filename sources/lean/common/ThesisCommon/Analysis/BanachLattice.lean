import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Topology.ContinuousMap.Compact

/-! Real Banach lattices and isomorphism, with their actual norm and order structures. -/
universe u
namespace ThesisCommon

/-- A real Banach space. No order or special representation is assumed. -/
structure RealBanachSpace where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] RealBanachSpace.normedAddCommGroup RealBanachSpace.normedSpace
  RealBanachSpace.completeSpace
instance : CoeSort RealBanachSpace (Type u) := ⟨RealBanachSpace.Carrier⟩

/-- A real vector lattice with a complete solid norm. Scalar positivity is explicit. -/
structure RealBanachLattice extends RealBanachSpace.{u} where
  [lattice : Lattice Carrier]
  [orderedAdd : IsOrderedAddMonoid Carrier]
  [orderedModule : IsOrderedModule ℝ Carrier]
  [solidNorm : HasSolidNorm Carrier]

attribute [instance] RealBanachLattice.lattice RealBanachLattice.orderedAdd
  RealBanachLattice.orderedModule RealBanachLattice.solidNorm
instance : CoeSort RealBanachLattice (Type u) := ⟨fun E => E.Carrier⟩

/-- Isomorphism as Banach spaces; the original norm need not itself be a lattice norm.
The representative is allowed any lattice structure and equivalent complete norm. -/
def IsomorphicToBanachLattice (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ F : RealBanachLattice.{u}, Nonempty (E ≃L[ℝ] F)

/-- Compact Hausdorff spaces, without metrizability or separability restrictions. -/
structure Compactum where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [compactSpace : CompactSpace Carrier]
  [t2Space : T2Space Carrier]

attribute [instance] Compactum.topology Compactum.compactSpace Compactum.t2Space
instance : CoeSort Compactum (Type u) := ⟨Compactum.Carrier⟩

/-- The class of real C(K) spaces up to Banach-space isomorphism. -/
def IsomorphicToCK (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ K : Compactum.{u}, Nonempty (E ≃L[ℝ] C(K, ℝ))

end ThesisCommon
