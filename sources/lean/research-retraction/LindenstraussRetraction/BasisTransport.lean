import LindenstraussRetraction.SchauderBasisLemmas
import Mathlib.Topology.Algebra.Module.Equiv

/-! Schauder bases transport along continuous linear equivalences. -/

noncomputable section
open Filter Topology

namespace LindenstraussRetraction.SchauderBasis

universe u v w
variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Z : Type w} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def map (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Z) : SchauderBasis 𝕜 Z where
  vector n := e (b.vector n)
  coord n := (b.coord n).comp e.symm.toContinuousLinearMap
  biorthogonal n m := by simp [b.coord_vector]
  expansion z := by
    have h := e.continuous.tendsto (e.symm z) |>.comp (b.expansion (e.symm z))
    simpa only [Function.comp_def, map_sum, map_smul, e.apply_symm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using h

@[simp] theorem map_vector (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Z) (n : ℕ) :
    (b.map e).vector n = e (b.vector n) := rfl

@[simp] theorem map_coord (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Z) (n : ℕ) (z : Z) :
    (b.map e).coord n z = b.coord n (e.symm z) := rfl

@[simp] theorem map_partialSum_apply (b : SchauderBasis 𝕜 X) (e : X ≃L[𝕜] Z)
    (N : ℕ) (z : Z) : (b.map e).partialSum N z = e (b.partialSum N (e.symm z)) := by
  simp only [partialSum_apply, map_coord, map_vector, map_sum, map_smul]

end LindenstraussRetraction.SchauderBasis
