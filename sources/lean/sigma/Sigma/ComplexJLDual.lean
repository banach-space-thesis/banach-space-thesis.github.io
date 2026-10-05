import Sigma.ComplexContinuousRepresentation
import Sigma.AtomicRepresentation
import ThesisCommon.Analysis.SigmaComplexDualTransport

/-! The full complex dual representation, including the infinity coordinate,
is obtained from the proved scalar-generic Rudin theorem. -/
noncomputable section
open scoped ZeroAtInfty
open ThesisCommon
namespace SigmaNonprimarity

local instance complexJLSpace (B : Set (Set Point)) : NormedSpace ℂ (ComplexJL B) := inferInstance
local instance complexJLGroup (B : Set (Set Point)) : NormedAddCommGroup (ComplexJL B) := inferInstance
local instance complexJLDualGroup (B : Set (Set Point)) :
    NormedAddCommGroup (ComplexJL B →L[ℂ] ℂ) := inferInstance
local instance complexJLDualSpace (B : Set (Set Point)) :
    NormedSpace ℂ (ComplexJL B →L[ℂ] ℂ) := inferInstance

theorem complexAUAtomicDualModel {B : Set (Set Point)} (hB : AlmostDisjoint B) :
    Nonempty (JLMS.AtomicDualModel ℂ (AUCompactum B)) := by
  letI := mrowkaT2 hB
  exact JLMS.exists_atomicDualModel (auScattered B)

def complexCompactCZeroEquiv (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    C(K,ℂ) ≃ₗᵢ[ℂ] C₀(K,ℂ) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_add' := by intros; ext p; rfl
  map_smul' := by intros; ext p; rfl
  norm_map' := by intro f; rfl

def complexJLDualEquiv {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    (ComplexJL B →L[ℂ] ℂ) ≃ₗᵢ[ℂ] JLMS.ellOneOn ℂ (AUCompactum B) :=
  (complexDualIsometryEquiv ((complexJLContinuousEquiv hB hInf).trans
    (complexCompactCZeroEquiv (AUCompactum B)))).trans
      (Classical.choice (complexAUAtomicDualModel hB)).representation

theorem complexJLDual_apply_hasSum {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (φ : ComplexJL B →L[ℂ] ℂ) (f : ComplexJL B) :
    HasSum (fun p => complexJLDualEquiv hB hInf φ p * complexJLContinuousEquiv hB hInf f p)
      (φ f) := by
  let e := (complexJLContinuousEquiv hB hInf).trans (complexCompactCZeroEquiv (AUCompactum B))
  have h := JLMS.atomicDual_apply_hasSum (Classical.choice (complexAUAtomicDualModel hB))
    (complexDualIsometryEquiv e φ) (e f)
  simpa only [complexDualIsometryEquiv_apply,LinearIsometryEquiv.symm_apply_apply] using h

end SigmaNonprimarity

