import BanachIsometric.AffineSubdivisionMesh
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual repeated subdivision has arbitrarily small mesh. The iterated
operator is the literal power of the constructed subdivision endomorphism. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineSubdivision_iterate_mesh {s : Set E} (hs : Convex ℝ s)
    (n k : ℕ) (D : ℝ) :
    affineMeshCarrier s D n ≤
      (affineMeshCarrier s (barycentricMeshFactor n ^ k * D) n).comap (affineSubdivision n ^ k) := by
  induction k with
  | zero =>
    simpa only [pow_zero, one_mul] using (le_refl (affineMeshCarrier s D n))
  | succ k ih =>
    intro c hc
    have h := affineSubdivision_mesh hs (barycentricMeshFactor n ^ k * D) n (ih hc)
    simpa only [pow_succ', Module.End.mul_apply, mul_assoc] using h

theorem exists_subdivision_mesh_factor_lt (n : ℕ) (D ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, barycentricMeshFactor n ^ k * D < ε := by
  have h : Tendsto (fun k : ℕ => barycentricMeshFactor n ^ k * D) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (barycentricMeshFactor_nonneg n)
        (barycentricMeshFactor_lt_one n)).mul_const D
  exact (h.eventually (gt_mem_nhds hε)).exists

theorem affineSubdivision_arbitrarily_small_mesh {s : Set E} (hs : Convex ℝ s)
    (n : ℕ) (D ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, affineMeshCarrier s D n ≤
      (affineMeshCarrier s ε n).comap (affineSubdivision n ^ k) := by
  obtain ⟨k, hk⟩ := exists_subdivision_mesh_factor_lt n D ε hε
  refine ⟨k, fun c hc => ?_⟩
  have h := affineSubdivision_iterate_mesh hs n k D hc
  apply Finsupp.supported_mono (M := ℚ) (R := ℚ) ?_ h
  intro v hv
  exact ⟨hv.1, fun i j => (hv.2 i j).trans hk.le⟩

end BanachIsometric.SingularPrism
