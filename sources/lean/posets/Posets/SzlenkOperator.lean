import Posets.SzlenkDerivation
import Mathlib.Analysis.RCLike.Basic
import Mathlib.SetTheory.Ordinal.Exponential

/-! Szlenk bounds for an operator are bounds on the actual adjoint image of
the dual unit ball. This definition does not assert any ideal property. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]

def weakStarAdjoint (T : E →L[𝕜] F) (φ : WeakDual 𝕜 F) : WeakDual 𝕜 E :=
  StrongDual.toWeakDual ((WeakDual.toStrongDual φ).comp T)

@[simp] theorem weakStarAdjoint_apply (T : E →L[𝕜] F) (φ : WeakDual 𝕜 F) (x : E) :
    weakStarAdjoint T φ x = φ (T x) := rfl

theorem weakStarAdjoint_continuous (T : E →L[𝕜] F) : Continuous (weakStarAdjoint T) :=
  WeakDual.continuous_of_continuous_eval (fun x => WeakDual.eval_continuous (T x))

@[simp] theorem weakStarAdjoint_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F)
    (φ : WeakDual 𝕜 G) : weakStarAdjoint (S.comp T) φ =
      weakStarAdjoint T (weakStarAdjoint S φ) := rfl

@[simp] theorem weakStarAdjoint_id (φ : WeakDual 𝕜 E) :
    weakStarAdjoint (ContinuousLinearMap.id 𝕜 E) φ = φ := by
  apply DFunLike.ext
  intro x
  rfl

def weakStarUnitBall (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Set (WeakDual 𝕜 E) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1

theorem weakStarUnitBall_isCompact : IsCompact (weakStarUnitBall 𝕜 E) :=
  WeakDual.isCompact_closedBall 𝕜 0 1

def adjointUnitBall (T : E →L[𝕜] F) : Set (WeakDual 𝕜 E) :=
  weakStarAdjoint T '' weakStarUnitBall 𝕜 F

theorem adjointUnitBall_isCompact (T : E →L[𝕜] F) : IsCompact (adjointUnitBall T) :=
  weakStarUnitBall_isCompact.image (weakStarAdjoint_continuous T)

@[simp] theorem adjointUnitBall_id :
    adjointUnitBall (ContinuousLinearMap.id 𝕜 E) = weakStarUnitBall 𝕜 E := by
  change weakStarAdjoint (ContinuousLinearMap.id 𝕜 E) '' _ = _
  simp only [weakStarAdjoint_id, Set.image_id']

/-- Sz(T) ≤ α, directly in terms of the weak-star derivation. -/
def OperatorSzlenkBound (T : E →L[𝕜] F) (α : Ordinal) : Prop :=
  HasSzlenkBound (adjointUnitBall T) α

/-- The class SZ_α in the paper and Brooker's operator-ideal theorem. -/
def SzlenkOperatorClass (α : Ordinal) : Set (E →L[𝕜] F) :=
  {T | OperatorSzlenkBound T (Ordinal.omega0 ^ α)}

theorem OperatorSzlenkBound.mono {T : E →L[𝕜] F} {α β : Ordinal}
    (h : OperatorSzlenkBound T α) (hαβ : α ≤ β) : OperatorSzlenkBound T β :=
  HasSzlenkBound.mono h hαβ

end Posets
