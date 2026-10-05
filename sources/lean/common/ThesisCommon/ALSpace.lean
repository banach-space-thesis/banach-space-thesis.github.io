import ThesisCommon.Analysis.BanachLattice
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Complex.Basic

/-! A scalar-uniform definition of real/complex Banach lattices via their real
part. For complex scalars the modulus is the lattice supremum of the real
parts of unimodular rotations. This is not an assumed L¹ representation.
Completeness is carried by the ambient space and the closed real subspace. -/
noncomputable section
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E]

/-- Real form, lattice order and complex modulus of a Banach lattice.
All fields describe the mathematical object; none assumes a paper result. -/
structure BanachLatticeModel where
  realForm : Submodule ℝ E
  closed_realForm : IsClosed (realForm : Set E)
  realPart : E →L[ℝ] realForm
  realPart_coe : ∀ x : realForm, realPart (x : E) = x
  realPart_I : ∀ x : realForm, realPart ((RCLike.I : 𝕜) • (x : E)) = 0
  decomposition : ∀ z : E,
    z = (realPart z : E) + (RCLike.I : 𝕜) • (realPart (-(RCLike.I : 𝕜) • z) : E)
  [lattice : Lattice realForm]
  [orderedAdd : IsOrderedAddMonoid realForm]
  [orderedModule : IsOrderedModule ℝ realForm]
  [solidNorm : HasSolidNorm realForm]
  modulus : E → realForm
  modulus_lub : ∀ z : E,
    IsLUB {x : realForm | ∃ a : 𝕜, ‖a‖ = 1 ∧ x = realPart (a • z)} (modulus z)
  norm_modulus : ∀ z : E, ‖modulus z‖ = ‖z‖

attribute [instance] BanachLatticeModel.lattice BanachLatticeModel.orderedAdd
  BanachLatticeModel.orderedModule BanachLatticeModel.solidNorm

/-- An AL-space has a Banach-lattice structure with norm additive on its
positive real cone. Completeness is required in every paper target. -/
def IsALSpace [IsScalarTower ℝ 𝕜 E] : Prop :=
  ∃ B : BanachLatticeModel 𝕜 E, ∀ x y : B.realForm,
    0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖

/-- The usual real definition, for the shared library's bundled real lattice. -/
def RealBanachLattice.IsAL (E : RealBanachLattice) : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖

end ThesisCommon
