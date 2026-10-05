import Posets.AlspachCounterexampleCompactRows
import ThesisCommon.Analysis.CountableCompactRank
import JLMS.Rudin

/-! The actual surjective evaluation operator for every constructed compact
row family. Atomic duality is supplied by the proved Rudin representation:
countable compact Hausdorff spaces are metrizable and scattered. -/

noncomputable section
open Set Topology
namespace Posets

theorem alspach_countable_compact_scattered (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Countable K] : JLMS.IsScattered K := by
  letI : TopologicalSpace.MetrizableSpace K := alspach_countable_compact_metrizable K
  letI : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  intro s hs
  obtain ⟨x, hx, hn⟩ := ThesisCommon.countableCompact_exists_mem_not_mem_derivedSet
    (isClosed_closure (s := s)).isCompact (hs.mono subset_closure)
  have hxs : x ∈ s := by
    rw [closure_eq_self_union_derivedSet] at hx
    exact hx.resolve_right (fun h => hn (derivedSet_mono s (closure s) subset_closure h))
  rw [mem_derivedSet, accPt_iff_nhds] at hn
  push_neg at hn
  obtain ⟨U, hU, hu⟩ := hn
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  refine ⟨x, hxs, V, hV, ?_⟩
  ext y
  constructor
  · intro hy
    exact mem_singleton_iff.mpr (hu y ⟨hVU hy.2, subset_closure hy.1⟩)
  · rintro rfl
    exact ⟨hxs, hxV⟩

namespace AlspachCompactRows
variable {𝕜 : Type*} [RCLike 𝕜] (F : AlspachCompactRows 𝕜)

def pointAtomicModel : JLMS.AtomicDualModel 𝕜 F.Point :=
  (JLMS.exists_atomicDualModel (𝕜 := 𝕜) (alspach_countable_compact_scattered F.Point)).some

def indexAtomicModel : JLMS.AtomicDualModel 𝕜 F.Index :=
  (JLMS.exists_atomicDualModel (𝕜 := 𝕜) (alspach_countable_compact_scattered F.Index)).some

theorem atomicRows_continuous (f : JLMS.CZero 𝕜 F.Point) :
    Continuous (fun i => F.pointAtomicModel.representation.symm (F.rows.forest.row i) f) := by
  change Continuous (fun i => F.pointAtomicModel.representation.symm (F.rows.row i).vector f)
  simp_rw [AlspachProbability.representation_symm_apply]
  exact F.continuousRows f.toContinuousMap

def evaluation : JLMS.CZero 𝕜 F.Point →L[𝕜] JLMS.CZero 𝕜 F.Index :=
  alspachEvaluation (fun i => F.pointAtomicModel.representation.symm (F.rows.forest.row i))
    F.atomicRows_continuous (fun i => by
      simpa only [F.pointAtomicModel.representation.symm.norm_map] using F.rows.forest.row_norm_le i)

theorem evaluation_surjective : Function.Surjective F.evaluation :=
  alspachForestEvaluation_surjective F.pointAtomicModel F.indexAtomicModel
    F.rows.forest F.atomicRows_continuous

theorem evaluation_norm_le : ‖F.evaluation‖ ≤ 1 := alspachEvaluation_norm_le _ _ _

@[simp] theorem evaluation_apply (f : JLMS.CZero 𝕜 F.Point) (i : F.Index) :
    F.evaluation f i = (F.rows.row i).eval f :=
  AlspachProbability.representation_symm_apply F.pointAtomicModel _ _

end AlspachCompactRows
end Posets
