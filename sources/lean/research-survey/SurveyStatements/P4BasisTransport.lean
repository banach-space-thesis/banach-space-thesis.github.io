import SurveyStatements.P4Bidual
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! Reflexivity and the exact ordered Schauder property are invariant under
bounded linear equivalence. Universe lifting preserves both properties. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology

namespace SurveyStatements.P4

universe u v w z
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem reflexive_of_continuousLinearEquiv (e : E ≃L[𝕜] F)
    (hE : IsReflexiveNormedSpace 𝕜 E) : IsReflexiveNormedSpace 𝕜 F := by
  intro ξ
  obtain ⟨x, hx⟩ := hE (bidualMap e.symm.toContinuousLinearMap ξ)
  refine ⟨e x, ?_⟩
  have heq : bidualMap e.toContinuousLinearMap
      (bidualMap e.symm.toContinuousLinearMap ξ) = ξ := by
    apply ContinuousLinearMap.ext
    intro φ
    change ξ ((φ.comp e.toContinuousLinearMap).comp e.symm.toContinuousLinearMap) = ξ φ
    congr 1
    apply ContinuousLinearMap.ext
    intro y
    exact congrArg φ (e.apply_symm_apply y)
  rw [← heq, ← hx]
  rfl

lemma schauderPartialSum_map {I : Set ℕ} (b : I → E) (a : I → 𝕜)
    (e : E ≃L[𝕜] F) (N : ℕ) :
    schauderPartialSum 𝕜 (fun i => e (b i)) a N = e (schauderPartialSum 𝕜 b a N) := by
  classical
  simp only [schauderPartialSum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp only [map_smul, map_zero]

theorem HasSchauderBasis.map (hE : HasSchauderBasis 𝕜 E) (e : E ≃L[𝕜] F) :
    HasSchauderBasis 𝕜 F := by
  obtain ⟨I, b, hI, hb⟩ := hE
  refine ⟨I, fun i => e (b i), hI, ?_⟩
  intro y
  obtain ⟨a, ha, huniq⟩ := hb (e.symm y)
  refine ⟨a, ?_, ?_⟩
  · change Tendsto (schauderPartialSum 𝕜 (fun i => e (b i)) a) atTop (𝓝 y)
    have heq : schauderPartialSum 𝕜 (fun i => e (b i)) a =
        fun N => e (schauderPartialSum 𝕜 b a N) := funext (schauderPartialSum_map b a e)
    rw [heq]
    simpa only [Function.comp_def, e.apply_symm_apply] using e.continuous.tendsto _ |>.comp ha
  · intro c hc
    apply huniq c
    have ht := e.symm.continuous.tendsto y |>.comp hc
    simpa only [Function.comp_def, schauderPartialSum_map, e.symm_apply_apply] using ht

def ReflexiveBanachSpaceWithBasis.ulift (V : ReflexiveBanachSpaceWithBasis.{u,v} 𝕜) :
    ReflexiveBanachSpaceWithBasis.{u,max v z} 𝕜 where
  Carrier := ULift.{z} V.Carrier
  reflexive := reflexive_of_continuousLinearEquiv
    (LinearIsometryEquiv.ulift (R := 𝕜) (E := V.Carrier)).symm.toContinuousLinearEquiv V.reflexive
  schauderBasis := V.schauderBasis.map
    (LinearIsometryEquiv.ulift (R := 𝕜) (E := V.Carrier)).symm.toContinuousLinearEquiv

end SurveyStatements.P4
