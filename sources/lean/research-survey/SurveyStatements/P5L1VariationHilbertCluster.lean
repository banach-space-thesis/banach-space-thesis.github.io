import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Genuine weak compactness for bounded Hilbert-space sequences. A
cluster vector represents every scalar pairing that already has a full
sequence limit. No sequential compactness assumption is introduced. -/

noncomputable section
set_option autoImplicit false
open Filter Set Topology Metric
namespace SurveyStatements.P5L1Variation

theorem pairing_limit_of_cluster {X : Type*} [TopologicalSpace X] [T2Space X]
    (u : ℕ → X) (a c : X) (ha : MapClusterPt a atTop u)
    (hc : Tendsto u atTop (𝓝 c)) : a = c := by
  exact (Inseparable.of_nhds_neBot (ha.clusterPt.mono hc)).eq

theorem exists_hilbert_pairing_cluster (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (f : ℕ → E) (B : ℝ) (hf : ∀ n, ‖f n‖ ≤ B) :
    ∃ m : E, ‖m‖ ≤ B ∧ ∀ x : E, ∀ c : 𝕜,
      Tendsto (fun n => inner 𝕜 (f n) x) atTop (𝓝 c) → inner 𝕜 m x = c := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  let w : ℕ → WeakDual 𝕜 E := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual 𝕜 E (f n))
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) B := by
    change ‖InnerProductSpace.toDual 𝕜 E (f n) - 0‖ ≤ B
    simpa only [sub_zero, (InnerProductSpace.toDual 𝕜 E).norm_map] using hf n
  have hcompact := WeakDual.isCompact_closedBall 𝕜 (0 : StrongDual 𝕜 E) B
  have hevent : ∀ᶠ n : ℕ in atTop,
      w n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) B :=
    Eventually.of_forall hw
  obtain ⟨ξ, hξ, hcluster⟩ := hcompact.exists_mapClusterPt_of_frequently
    hevent.frequently
  let m : E := (InnerProductSpace.toDual 𝕜 E).symm (WeakDual.toStrongDual ξ)
  refine ⟨m, ?_, ?_⟩
  · have hnorm : ‖WeakDual.toStrongDual ξ‖ ≤ B := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hξ
    simpa only [m, (InnerProductSpace.toDual 𝕜 E).symm.norm_map] using hnorm
  · intro x c hlim
    have hcl := hcluster.continuousAt_comp (WeakDual.eval_continuous x).continuousAt
    have hcl' : MapClusterPt (inner 𝕜 m x) atTop (fun n => inner 𝕜 (f n) x) := by
      simpa only [m, Function.comp_apply, w, InnerProductSpace.toDual_apply,
        InnerProductSpace.toDual_symm_apply, StrongDual.coe_toWeakDual] using hcl
    exact pairing_limit_of_cluster _ _ _ hcl' hlim

end SurveyStatements.P5L1Variation
