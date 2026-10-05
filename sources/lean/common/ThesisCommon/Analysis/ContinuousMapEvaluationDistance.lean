import ThesisCommon.Analysis.ContinuousMapSmallSets
import Mathlib.Topology.UrysohnsLemma

/-! Distinct point evaluations on C(K) have dual norm distance exactly
two. The real Urysohn separator is embedded into either scalar field. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

theorem norm_continuousMap_eval_sub (s t : K) (hst : s ≠ t) :
    ‖ContinuousMap.evalCLM (M := 𝕜) 𝕜 s - ContinuousMap.evalCLM (M := 𝕜) 𝕜 t‖ = 2 := by
  have hu : ‖ContinuousMap.evalCLM (M := 𝕜) 𝕜 s - ContinuousMap.evalCLM (M := 𝕜) 𝕜 t‖ ≤ 2 := by
    apply (norm_sub_le (ContinuousMap.evalCLM (M := 𝕜) 𝕜 s) (ContinuousMap.evalCLM (M := 𝕜) 𝕜 t)).trans
    linarith [norm_continuousMap_evalCLM_le (𝕜 := 𝕜) s, norm_continuousMap_evalCLM_le (𝕜 := 𝕜) t]
  obtain ⟨φ, hφs, hφt, hφ⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({s} : Set K)) isClosed_singleton
    (Set.disjoint_singleton.2 hst)
  let f : C(K, 𝕜) := ⟨fun x => ((1-2*φ x : ℝ) : 𝕜), by fun_prop⟩
  have hf : ‖f‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro x
    change ‖((1-2*φ x : ℝ) : 𝕜)‖ ≤ 1
    rw [RCLike.norm_ofReal, abs_le]
    constructor <;> linarith [(hφ x).1, (hφ x).2]
  have hs : φ s = 0 := hφs (Set.mem_singleton s)
  have ht : φ t = 1 := hφt (Set.mem_singleton t)
  have hv : ‖(ContinuousMap.evalCLM (M := 𝕜) 𝕜 s - ContinuousMap.evalCLM (M := 𝕜) 𝕜 t) f‖ = 2 := by
    change ‖((1-2*φ s : ℝ) : 𝕜) - ((1-2*φ t : ℝ) : 𝕜)‖ = 2
    rw [hs, ht]
    norm_num
  apply le_antisymm hu
  rw [← hv]
  apply ((ContinuousMap.evalCLM (M := 𝕜) 𝕜 s - ContinuousMap.evalCLM (M := 𝕜) 𝕜 t).le_opNorm f).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hf
    (norm_nonneg (ContinuousMap.evalCLM (M := 𝕜) 𝕜 s - ContinuousMap.evalCLM (M := 𝕜) 𝕜 t))

end ThesisCommon
