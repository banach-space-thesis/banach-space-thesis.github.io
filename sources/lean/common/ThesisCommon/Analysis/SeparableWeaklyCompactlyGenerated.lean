import ThesisCommon.Analysis.UniformPrimariness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases

/-! A concrete compact generating set for every separable normed space.
Rescaling a dense sequence gives a norm-null sequence; adjoining its limit
is norm compact and hence weakly compact. Completeness is not required. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace ThesisCommon
variable (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeparableSpace X]

theorem exists_compact_generatingSet_of_separable :
    ∃ K : Set X, IsCompact K ∧ (Submodule.span 𝕜 K).topologicalClosure = ⊤ := by
  let d : ℕ → X := denseSeq X
  let c : ℕ → ℝ := fun n => (1 / (n + 1 : ℝ)) / (‖d n‖ + 1)
  let v : ℕ → X := fun n => (c n : 𝕜) • d n
  have hc (n : ℕ) : 0 < c n := by
    dsimp [c]
    positivity
  have hv (n : ℕ) : ‖v n‖ ≤ 1 / (n + 1 : ℝ) := by
    rw [show v n = (c n : 𝕜) • d n from rfl, norm_smul,
      RCLike.norm_ofReal, abs_of_pos (hc n)]
    dsimp [c]
    calc
      _ ≤ ((1 / (n + 1 : ℝ)) / (‖d n‖ + 1)) * (‖d n‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := div_mul_cancel₀ _ (by positivity)
  have hzero : Tendsto v atTop (𝓝 0) :=
    squeeze_zero_norm hv tendsto_one_div_add_atTop_nhds_zero_nat
  let K : Set X := insert 0 (range v)
  refine ⟨K, hzero.isCompact_insert_range, ?_⟩
  apply top_unique
  intro x _
  have hd : range d ⊆ (Submodule.span 𝕜 K).topologicalClosure := by
    rintro _ ⟨n, rfl⟩
    apply (Submodule.span 𝕜 K).le_topologicalClosure
    have hmem : v n ∈ Submodule.span 𝕜 K :=
      Submodule.subset_span (mem_insert_of_mem 0 (mem_range_self n))
    have hcn : (c n : 𝕜) ≠ 0 := by exact_mod_cast (hc n).ne'
    exact (Submodule.smul_mem_iff _ hcn).mp hmem
  exact closure_minimal hd (Submodule.isClosed_topologicalClosure _) (denseRange_denseSeq X x)

theorem isWeaklyCompactlyGenerated_of_separable : IsWeaklyCompactlyGenerated 𝕜 X := by
  obtain ⟨K, hK, hspan⟩ := exists_compact_generatingSet_of_separable 𝕜 X
  exact ⟨K, hK.image (toWeakSpaceCLM 𝕜 X).continuous, hspan⟩

end ThesisCommon
