import BanachIsometric.CanonicalHemisphereCycle
import BanachIsometric.LipschitzAffineSimplex
import BanachIsometric.LipschitzNormalization
import BanachIsometric.RawLipschitzChains
import Mathlib.Analysis.Convex.StdSimplex

/-! The actual normalized affine sphere cycle is supported on Lipschitz
simplexes in the inherited Euclidean metric. -/

noncomputable section
namespace BanachIsometric.SingularPrism
open Set Metric NormedSpace
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem exists_lipschitz_affineHemisphereSimplex {n : ℕ} (pole : sphere (0 : V) 1)
    (vertices : Fin (n + 1) → V) (h : affineHemisphereAdmissible pole vertices) :
    ∃ L : ℝ≥0, LipschitzWith L (affineHemisphereSimplex pole vertices) := by
  letI : CompactSpace (Simplex n) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex (Fin (n + 1)))
  obtain ⟨L, hL⟩ := exists_lipschitz_affineSingularSimplex vertices
  obtain ⟨M, hM⟩ := exists_lipschitz_normalize_of_compact hL (fun x => (h x).1)
  refine ⟨M, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simpa only [Subtype.dist_eq, affineHemisphereSimplex_val pole vertices h] using hM.dist_le_mul x y

variable [FiniteDimensional ℝ V]

theorem canonicalHemisphereChain_mem_lipschitz
    (v pole : sphere (0 : V) 1) (hPole : pole = v ∨ pole = -v) (n : ℕ)
    (hdim : Module.finrank ℝ V = n + 3) :
    canonicalHemisphereChain v pole n hdim ∈ rawLipschitzCarrier (closedHemisphere pole) (n + 2) := by
  rw [canonicalHemisphereChain_eq_sum]
  apply Submodule.sum_mem
  intro i _
  apply (rawLipschitzCarrier (closedHemisphere pole) (n + 2)).toAddSubgroup.zsmul_mem
  exact Finsupp.single_mem_supported ℚ 1 (exists_lipschitz_affineHemisphereSimplex pole _
    (canonicalHemisphereFacet_admissible v pole hPole n hdim i))

theorem canonicalSuspensionCycle_mem_lipschitz
    (v : sphere (0 : V) 1) (n : ℕ) (hdim : Module.finrank ℝ V = n + 3) :
    (canonicalSuspensionCycle v n hdim).val ∈ rawLipschitzCarrier (sphere (0 : V) 1) (n + 2) := by
  change rawChainMap (closedHemisphereInclusion v) (n + 2) (canonicalHemisphereChain v v n hdim) -
    rawChainMap (closedHemisphereInclusion (-v)) (n + 2) (canonicalHemisphereChain v (-v) n hdim) ∈ _
  apply Submodule.sub_mem
  · exact rawChainMap_preserves_lipschitz (closedHemisphereInclusion v) (LipschitzWith.subtype_val _) _
      (canonicalHemisphereChain_mem_lipschitz v v (Or.inl rfl) n hdim)
  · exact rawChainMap_preserves_lipschitz (closedHemisphereInclusion (-v)) (LipschitzWith.subtype_val _) _
      (canonicalHemisphereChain_mem_lipschitz v (-v) (Or.inr rfl) n hdim)

end BanachIsometric.SingularPrism
