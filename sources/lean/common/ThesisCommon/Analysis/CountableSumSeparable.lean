import ThesisCommon.Analysis.CZeroArbitrarySingles
import Mathlib.Topology.Bases
import Mathlib.Tactic.FunProp

/-! Separability of genuine countable finite-p and c0 sums. The dense sets
are countable unions of continuous images of finite coefficient powers. -/
noncomputable section
open Filter Topology TopologicalSpace
open scoped ENNReal ZeroAtInfty BigOperators
namespace ThesisCommon
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [Countable Γ] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [SeparableSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem separableSpace_of_countable_synthesis (L : Γ → X →L[𝕜] Y)
    (hexp : ∀ y : Y, ∃ a : Γ → X, HasSum (fun i => L i (a i)) y) : SeparableSpace Y := by
  classical
  let f (s : Finset Γ) (a : s → X) : Y := ∑ i : s, L i (a i)
  have hf (s : Finset Γ) : Continuous (f s) := by
    apply continuous_finset_sum
    intro i _
    exact (L i).continuous.comp (continuous_apply i)
  have hsep : IsSeparable (⋃ s : Finset Γ, Set.range (f s)) :=
    IsSeparable.iUnion fun s => isSeparable_range (hf s)
  have hdense : Dense (⋃ s : Finset Γ, Set.range (f s)) := by
    intro y
    obtain ⟨a, ha⟩ := hexp y
    apply isClosed_closure.mem_of_tendsto ha
    apply Filter.Eventually.of_forall
    intro s
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨s, fun i : s => a i, ?_⟩
    exact Finset.sum_coe_sort s (fun i => L i (a i))
  exact hdense.isSeparable_iff.mp hsep

include 𝕜 in
theorem lp_separableSpace_of_countable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    SeparableSpace (lp (fun _ : Γ => X) p) := by
  classical
  apply separableSpace_of_countable_synthesis
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : Γ => X) p i)
  intro x
  exact ⟨x, lp.hasSum_single hp x⟩

include 𝕜 in
theorem cZero_separableSpace_of_countable [TopologicalSpace Γ] [DiscreteTopology Γ] :
    SeparableSpace C₀(Γ, X) := by
  apply separableSpace_of_countable_synthesis (fun i => cZeroSingleAtL (𝕜 := 𝕜) (X := X) i)
  intro x
  exact ⟨x, cZero_hasSum_singleAt (𝕜 := 𝕜) x⟩

end ThesisCommon
