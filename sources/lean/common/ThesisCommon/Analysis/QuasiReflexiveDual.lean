import ThesisCommon.Analysis.QuotientDualAnnihilator
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The defect of a dual Banach space is algebraically the continuous dual
of the original defect, via canonical restriction and its canonical section.
Finite-dimensionality then yields preservation of quasi-reflexive order. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

local instance quasiDualBidualGroup : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance quasiDualBidualSpace : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 X) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance quasiDualTripleGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 (StrongDual 𝕜 X)) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)
local instance quasiDualTripleSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X))) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 X)) (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)
local instance quasiDualTripleQuotient :
    HasQuotient (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)))
      (Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)))) :=
  @Submodule.hasQuotient 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)))
    inferInstance inferInstance inferInstance

/-- Restriction of a triple-dual functional to the canonical copy of X. -/
def bidualRestriction : StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) →L[𝕜]
    StrongDual 𝕜 X :=
  banachAdjoint (NormedSpace.inclusionInDoubleDual 𝕜 X)

theorem bidualRestriction_rightInverse :
    Function.RightInverse (NormedSpace.inclusionInDoubleDual 𝕜 (StrongDual 𝕜 X))
      (bidualRestriction (𝕜 := 𝕜) (X := X)) := by
  intro f
  ext x
  rfl

theorem ker_bidualRestriction :
    LinearMap.ker (bidualRestriction (𝕜 := 𝕜) (X := X)).toLinearMap =
      LinearMap.ker (banachAdjoint (bidualImage 𝕜 X).subtypeL).toLinearMap := by
  ext f
  constructor
  · intro hf
    apply ContinuousLinearMap.ext
    rintro ⟨x, ⟨y, rfl⟩⟩
    exact congrArg (fun g : StrongDual 𝕜 X => g y) hf
  · intro hf
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun g : bidualImage 𝕜 X →L[𝕜] 𝕜 =>
      g ⟨NormedSpace.inclusionInDoubleDual 𝕜 X x, ⟨x, rfl⟩⟩) hf

set_option maxHeartbeats 3000000 in
/-- The actual quotient X***/κ(X*) identifies with the continuous dual of
the actual quotient X**/κ(X). No representation or dimension hypothesis
is built into this map. -/
def residuumDualLinearEquiv :
    ResiduumSpace 𝕜 (StrongDual 𝕜 X) ≃ₗ[𝕜] StrongDual 𝕜 (ResiduumSpace 𝕜 X) := by
  let r := bidualRestriction (𝕜 := 𝕜) (X := X)
  let s := NormedSpace.inclusionInDoubleDual 𝕜 (StrongDual 𝕜 X)
  have h := range_isCompl_ker_of_rightInverse r s bidualRestriction_rightInverse
  exact ((Submodule.quotientEquivOfIsCompl (LinearMap.range s.toLinearMap)
    (LinearMap.ker r.toLinearMap) h).trans
      (LinearEquiv.ofEq _ _ ker_bidualRestriction)).trans
        (quotientDualAnnihilatorEquiv (bidualImage 𝕜 X)).symm

/-- Passing to the continuous dual preserves every finite quasi-reflexive
order, proved on the canonical bidual quotient. -/
theorem IsQuasiReflexiveOfOrder.dual [CompleteSpace X] {n : ℕ}
    (h : IsQuasiReflexiveOfOrder 𝕜 X n) :
    IsQuasiReflexiveOfOrder 𝕜 (StrongDual 𝕜 X) n := by
  letI := h.finiteDimensional
  let a : StrongDual 𝕜 (ResiduumSpace 𝕜 X) ≃ₗ[𝕜]
      Module.Dual 𝕜 (ResiduumSpace 𝕜 X) := LinearMap.toContinuousLinearMap.symm
  let e := (residuumDualLinearEquiv (𝕜 := 𝕜) (X := X)).trans a
  letI : FiniteDimensional 𝕜 (ResiduumSpace 𝕜 (StrongDual 𝕜 X)) :=
    e.symm.finiteDimensional
  change Module.rank 𝕜 (ResiduumSpace 𝕜 (StrongDual 𝕜 X)) = n
  rw [← Module.finrank_eq_rank, e.finrank_eq, Subspace.dual_finrank_eq,
    Module.finrank_eq_rank]
  exact h

end ThesisCommon
