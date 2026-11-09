import PL1.RealSchur

/-! # Separability of the concrete projection ranges -/

noncomputable section
open Filter Set TopologicalSpace
open scoped Topology ENNReal NNReal

namespace PL1

variable (𝕜 : Type*) [RCLike 𝕜]

/-- A countable ell1 sum of a separable normed space is separable. -/
theorem L1Sum.separableSpace (Y : Type*) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [SeparableSpace Y] : SeparableSpace (L1Sum Y) := by
  classical
  let A : Set (L1Sum Y) := ⋃ n : ℕ, range (lp.single (E := fun _ : ℕ => Y) 1 n)
  let M : Submodule 𝕜 (L1Sum Y) := Submodule.span 𝕜 A
  have hsep : IsSeparable A := by
    apply IsSeparable.iUnion
    intro n
    exact isSeparable_range (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => Y) 1 n).continuous
  have hdense : Dense (M : Set (L1Sum Y)) := by
    intro f
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp) f)
    apply Eventually.of_forall
    intro s
    apply subset_closure
    apply M.sum_mem
    intro n _
    exact Submodule.subset_span (mem_iUnion.mpr ⟨n, ⟨f n, rfl⟩⟩)
  apply isSeparable_univ_iff.mp
  rw [← hdense.closure_eq]
  exact hsep.span.closure

/-- The countable Walsh span supplies separability of the actual Haar L1 space. -/
theorem Walsh.separableSpace_scalarL1 :
    SeparableSpace (MeasureTheory.Lp 𝕜 1 Walsh.haar) := by
  apply isSeparable_univ_iff.mp
  rw [← (Walsh.dense_span_scalarCharacterLp 𝕜 1 (by norm_num)).closure_eq]
  exact (countable_range (Walsh.scalarCharacterLp 𝕜 1)).isSeparable.span.closure

theorem Noise.projection_range_separableSpace (rates : ℕ → ℝ≥0) :
    SeparableSpace (Noise.projection 𝕜 rates).range := by
  let : SeparableSpace (MeasureTheory.Lp 𝕜 1 Walsh.haar) := Walsh.separableSpace_scalarL1 𝕜
  let : SeparableSpace (L1Sum (MeasureTheory.Lp 𝕜 1 Walsh.haar)) := L1Sum.separableSpace 𝕜 _
  have := UniformSpace.secondCountable_of_separable (L1Sum (MeasureTheory.Lp 𝕜 1 Walsh.haar))
  infer_instance

theorem Noise.projection_range_underlyingReal_separableSpace (rates : ℕ → ℝ≥0) :
    SeparableSpace (UnderlyingReal 𝕜 (Noise.projection 𝕜 rates).range) :=
  Noise.projection_range_separableSpace 𝕜 rates

end PL1
