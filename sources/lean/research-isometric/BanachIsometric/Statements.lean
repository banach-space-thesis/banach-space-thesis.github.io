import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Normed-space statements from Acuaviva--Kania, arXiv:2608.18257v1

The central conjecture below is a proposition definition, not a proved theorem.
`Module.rank` retains the infinite-dimensional case. `IsometryEquiv` includes
surjectivity and does not impose linearity, scalar compatibility, or fixing zero.
The existing normed-space structure is retained in the conclusion.
-/

universe u

namespace BanachIsometric

variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- All subspaces of the specified finite dimension are bijectively isometric.
The dimension is over `𝕜`; the isometries are purely metric. -/
def MetricSubspaceHomogeneity (n : ℕ) : Prop :=
  ∀ (E F : Submodule 𝕜 X),
    Module.rank 𝕜 E = (n : Cardinal) →
    Module.rank 𝕜 F = (n : Cardinal) → Nonempty (E ≃ᵢ F)

/-- Existence of an inner product compatible with the already specified norm.
`InnerProductSpace` packages its own scalar action; the equivalence below checks
that a witness can be reconstructed for the original scalar action as well.
No completeness assumption is part of this definition. -/
def HasCompatibleInnerProduct : Prop := Nonempty (InnerProductSpace 𝕜 X)

/-- An inner-product witness which explicitly retains the existing scalar
action as well as the existing norm. -/
def HasInnerProductForGivenScalarAction : Prop :=
  ∃ h : InnerProductSpace 𝕜 X, h.toNormedSpace = (inferInstance : NormedSpace 𝕜 X)

variable {𝕜 X}

/-- Norm compatibility is exactly the parallelogram law, over `ℝ` or `ℂ`.
This lemma does not infer the law from subspace homogeneity. -/
theorem hasCompatibleInnerProduct_iff_parallelogram :
    HasCompatibleInnerProduct 𝕜 X ↔
      ∀ x y : X,
        ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
          2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  constructor
  · rintro ⟨h⟩
    letI := h
    exact parallelogram_law_with_norm 𝕜
  · intro h
    exact ⟨InnerProductSpace.ofNorm (𝕜 := 𝕜) h⟩

/-- A formal semantic check of the bundled-class subtlety: an inner product
for some norm-compatible scalar action yields one for the specified action. -/
theorem hasCompatibleInnerProduct_iff_givenScalarAction :
    HasCompatibleInnerProduct 𝕜 X ↔ HasInnerProductForGivenScalarAction 𝕜 X := by
  constructor
  · intro h
    exact ⟨InnerProductSpace.ofNorm (𝕜 := 𝕜)
      (hasCompatibleInnerProduct_iff_parallelogram.mp h), rfl⟩
  · rintro ⟨h, _⟩
    exact ⟨h⟩

/-- Trivial reflexive case, included to expose the quantifiers of the hypothesis. -/
theorem MetricSubspaceHomogeneity.refl (E : Submodule 𝕜 X) :
    Nonempty (E ≃ᵢ E) := ⟨IsometryEquiv.refl E⟩

variable (X)

/-- The complex conclusion of Corollary B for a specified dimension.
This is the exact target, not a proof of Corollary B. -/
def ComplexCorollaryBAt [NormedSpace ℂ X] (n : ℕ) : Prop :=
  2 ≤ n → (n : Cardinal) < Module.rank ℂ X →
    MetricSubspaceHomogeneity ℂ X n → HasInnerProductForGivenScalarAction ℂ X

/-- The finite-dimensional codimension-one case needed for Corollary B.
This proposition remains a proof obligation. -/
def ComplexCodimensionOne : Prop :=
  ∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [FiniteDimensional ℂ Y] (n : ℕ),
    2 ≤ n → Module.finrank ℂ Y = n + 1 →
      MetricSubspaceHomogeneity ℂ Y n → HasInnerProductForGivenScalarAction ℂ Y

end BanachIsometric
