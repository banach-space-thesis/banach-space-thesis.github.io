import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
Concrete tensor spaces for the JFA statements. The epsilon tensor product is the
closed span of the rank-one operators phi ↦ phi(e) • x in B(E*,X).
By Hahn-Banach, its operator norm is the supremum over the two closed dual unit
balls used in the paper. Pairing its values with psi gives phi(e) * psi(x).

We deliberately do not use mathlib's PiTensorProduct.injectiveSeminorm: in the
pinned release that construction tests ALL bounded multilinear maps, whereas
the paper tests products of linear functionals.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxRecDepth 8000
open scoped TensorProduct
namespace JFA

universe u

section ConcreteInjective
variable (𝕜 : Type*) [RCLike 𝕜]
variable (E X : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

abbrev DualOperators := (E →L[𝕜] 𝕜) →L[𝕜] X

-- Supply this projection explicitly: the pinned release's instance search does
-- not find ContinuousAdd for these nested operator spaces on its own.
instance dualOperatorsContinuousAdd : ContinuousAdd (DualOperators 𝕜 E X) :=
  (ContinuousLinearMap.topologicalAddGroup :
    IsTopologicalAddGroup (DualOperators 𝕜 E X)).toContinuousAdd

instance dualOperatorsNormedAddCommGroup : NormedAddCommGroup (DualOperators 𝕜 E X) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance dualOperatorsNormedSpace : NormedSpace 𝕜 (DualOperators 𝕜 E X) :=
  ContinuousLinearMap.toNormedSpace

/-- The rank-one form associated with e ⊗ x. -/
def rankOneForm (e : E) (x : X) : DualOperators 𝕜 E X :=
  (ContinuousLinearMap.apply 𝕜 𝕜 e).smulRight x

@[simp] theorem rankOneForm_apply (e : E) (x : X)
    (φ : E →L[𝕜] 𝕜) :
    rankOneForm 𝕜 E X e x φ = φ e • x := rfl

/-- Algebraic tensor pairing; sums are independent of their representation. -/
def tensorPairing : E ⊗[𝕜] X →ₗ[𝕜] DualOperators 𝕜 E X :=
  TensorProduct.lift {
    toFun := fun e => {
      toFun := fun x => rankOneForm 𝕜 E X e x
      map_add' := by
        intro x y; ext φ
        exact smul_add (φ e) x y
      map_smul' := by
        intro a x; ext φ
        exact smul_comm (φ e) a x }
    map_add' := by
      intro e f; ext x φ
      change φ (e + f) • x = φ e • x + φ f • x
      rw [map_add, add_smul]
    map_smul' := by
      intro a e; ext x φ
      change φ (a • e) • x = a • (φ e • x)
      rw [map_smul, smul_eq_mul, mul_smul] }

@[simp] theorem tensorPairing_tmul (e : E) (x : X) :
    tensorPairing 𝕜 E X (e ⊗ₜ[𝕜] x) = rankOneForm 𝕜 E X e x := rfl

/-- For complete X, the completed injective tensor product, inside B(E*,X). -/
abbrev InjectiveTensor := (LinearMap.range (tensorPairing 𝕜 E X)).topologicalClosure

/-- The canonical map from the algebraic tensor product to its epsilon completion. -/
def injectiveInclusion : E ⊗[𝕜] X →ₗ[𝕜] InjectiveTensor 𝕜 E X :=
  (tensorPairing 𝕜 E X).codRestrict _ (fun z =>
    Submodule.le_topologicalClosure _ ⟨z, rfl⟩)

def injectivePure (e : E) (x : X) : InjectiveTensor 𝕜 E X :=
  injectiveInclusion 𝕜 E X (e ⊗ₜ[𝕜] x)

@[simp] theorem injectivePure_apply (e : E) (x : X)
    (φ : E →L[𝕜] 𝕜) (ψ : X →L[𝕜] 𝕜) :
    ψ ((injectivePure 𝕜 E X e x).val φ) = φ e * ψ x := by
  change ψ (φ e • x) = _
  simp

end ConcreteInjective

section Crossnorms
variable (𝕜 : Type u) [RCLike 𝕜]

/-- A reasonable crossnorm, including positive definiteness. The second bound
is the dual condition of Definition 2.3, written without a circular operator norm. -/
structure ReasonableCrossnorm (E X : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  seminorm : Seminorm 𝕜 (E ⊗[𝕜] X)
  definite : ∀ z, seminorm z = 0 → z = 0
  pure_le : ∀ e x, seminorm (e ⊗ₜ[𝕜] x) ≤ ‖e‖ * ‖x‖
  dual_le : ∀ z (φ : E →L[𝕜] 𝕜) (ψ : X →L[𝕜] 𝕜),
    ‖ψ (tensorPairing 𝕜 E X z φ)‖ ≤ (‖φ‖ * ‖ψ‖) * seminorm z

/-- Definition 2.4: one assignment on all pairs of Banach spaces, with the
operator mapping bound for every four spaces and every pair of operators.
All spaces live in an arbitrary common universe; this is not a countability restriction. -/
structure UniformCrossnorm where
  normFor : ∀ (E X : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X], ReasonableCrossnorm 𝕜 E X
  map_le : ∀ (E X F Y : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (U : E →L[𝕜] F) (R : X →L[𝕜] Y) (z : E ⊗[𝕜] X),
    (normFor F Y).seminorm (TensorProduct.map U.toLinearMap R.toLinearMap z) ≤
      (‖U‖ * ‖R‖) * (normFor E X).seminorm z

/-- A completion of the specified norm, expressed by its defining dense isometry.
This is a fully specified model, not an unspecified tensor-product predicate.
Completeness of A is required by each statement that uses this predicate. -/
def IsTensorCompletion (E X A : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A) : Prop :=
  Function.Injective ι ∧ DenseRange ι ∧ ∀ z, ‖ι z‖ = p.seminorm z

end Crossnorms
end JFA
