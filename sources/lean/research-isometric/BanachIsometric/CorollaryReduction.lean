import BanachIsometric.MetricReduction
import BanachIsometric.LocalToGlobal
import BanachIsometric.Functional
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Reduction of the full complex normed result to codimension one

The finite-dimensional codimension-one theorem is an explicit argument of the
main reduction. It is not proved or postulated as an axiom by this module.
-/

universe u

namespace BanachIsometric

/-- The complex functional theorem, if established, gives the precise normed
target retaining the original complex scalar action. -/
theorem complexCorollaryB_of_functional
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (hfunctional : ComplexFunctionalStatement (X := X)) (n : ℕ) :
    ComplexCorollaryBAt X n := by
  intro hn hdim hsections
  apply hasCompatibleInnerProduct_iff_givenScalarAction.mp
  exact complexFunctionalStatement_implies_corollaryB hfunctional n hn hdim hsections

/-- Once the finite-dimensional geometric core is proved, Corollary B follows
for every complex normed space, including incomplete and infinite-dimensional
ones. The core hypothesis is deliberately visible in the theorem's type. -/
theorem complexCorollaryB_of_codimensionOne
    (hcore : ComplexCodimensionOne.{u})
    (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] (n : ℕ) :
    ComplexCorollaryBAt X n := by
  intro hn hdim hsections
  have hrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ X := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Cardinal.natCast_add_one_le_iff.mpr hdim)
  apply hasCompatibleInnerProduct_iff_givenScalarAction.mp
  apply innerProductSpace_of_local (K := ℂ) (n + 1) (by omega) hrank
  intro Y hfinite hY
  letI : FiniteDimensional ℂ Y := hfinite
  obtain ⟨hinner, _⟩ := hcore Y n hn hY (hsections.submodule Y)
  exact ⟨hinner⟩

/-- The completion clause of Corollary B, conditional only on the compatible
inner product on the original given normed space. -/
theorem HasCompatibleInnerProduct.completion
    {𝕜 : Type*} [RCLike 𝕜] {X : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (h : HasCompatibleInnerProduct 𝕜 X) :
    HasCompatibleInnerProduct 𝕜 (UniformSpace.Completion X) := by
  obtain ⟨hinner⟩ := h
  letI : InnerProductSpace 𝕜 X := hinner
  exact ⟨inferInstance⟩

/-- The completion conclusion with its original extended scalar action fixed
explicitly, as in the original normed-space target. -/
theorem HasInnerProductForGivenScalarAction.completion
    {𝕜 : Type*} [RCLike 𝕜] {X : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (h : HasInnerProductForGivenScalarAction 𝕜 X) :
    HasInnerProductForGivenScalarAction 𝕜 (UniformSpace.Completion X) := by
  apply hasCompatibleInnerProduct_iff_givenScalarAction.mp
  exact (hasCompatibleInnerProduct_iff_givenScalarAction.mpr h).completion

end BanachIsometric
