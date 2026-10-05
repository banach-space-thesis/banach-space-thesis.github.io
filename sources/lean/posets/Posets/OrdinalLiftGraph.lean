import Posets.OrdinalLiftDualBall
import JLMS.BoundedBelowDual
import ThesisCommon.Analysis.ContinuousMapSmallSets

/-! The compact graph of all bounded Hahn--Banach lifts of point evaluations.
No continuous choice is assumed in this graph construction. -/
noncomputable section
open Set Topology TopologicalSpace
namespace Posets
variable {𝕜 K E : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def ordinalLiftGraphSet (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) :
    Set (K × ordinalLiftDualBall 𝕜 E r) :=
  {z | ∀ a : C(K, 𝕜), z.2.val (J a) = a z.1}

theorem ordinalLiftGraphSet_isClosed (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) :
    IsClosed (ordinalLiftGraphSet J r) := by
  unfold ordinalLiftGraphSet
  simp only [setOf_forall]
  apply isClosed_iInter
  intro a
  exact isClosed_eq ((WeakDual.eval_continuous (J a)).comp
    (continuous_subtype_val.comp continuous_snd)) (a.continuous.comp continuous_fst)

abbrev OrdinalLiftGraph (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) := ordinalLiftGraphSet J r

instance ordinalLiftGraph_compactSpace (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) :
    CompactSpace (OrdinalLiftGraph J r) :=
  isCompact_iff_compactSpace.mp (ordinalLiftGraphSet_isClosed J r).isCompact

theorem ordinalLiftGraph_metrizable [MetrizableSpace K] [SeparableSpace E]
    (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) : MetrizableSpace (OrdinalLiftGraph J r) := by
  letI instBallMetric : MetrizableSpace (ordinalLiftDualBall 𝕜 E r) :=
    ordinalLiftDualBall_metrizable 𝕜 E r
  infer_instance

def ordinalLiftGraphProjection (J : C(K, 𝕜) →L[𝕜] E) (r : ℝ) :
    C(OrdinalLiftGraph J r, K) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

theorem ordinalLiftGraphProjection_surjective (J : C(K, 𝕜) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    Function.Surjective (ordinalLiftGraphProjection J (1 / c)) := by
  intro x
  obtain ⟨φ, hφ, heq⟩ := JLMS.exists_dual_extension_of_bounded_below J hc hlower
    (ContinuousMap.evalCLM (M := 𝕜) 𝕜 x)
  have hn : ‖φ‖ ≤ 1 / c := hφ.trans
    ((div_le_div_iff_of_pos_right hc).mpr (ThesisCommon.norm_continuousMap_evalCLM_le x))
  exact ⟨⟨⟨x, StrongDual.toWeakDual φ, hn⟩, heq⟩, rfl⟩

end Posets
