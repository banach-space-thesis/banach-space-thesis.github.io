import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Topology
open scoped ZeroAtInfty OnePoint
namespace ThesisCommon

/-- Countably many separating Urysohn functions give a countable compact
Hausdorff space a countable base. -/
theorem countable_compact_secondCountable (K : Type*) [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [Countable K] : SecondCountableTopology K := by
  classical
  let I := {p : K × K // p.1 ≠ p.2}
  have hsep (i : I) : ∃ f : C(K, ℝ), f i.val.1 = 0 ∧ f i.val.2 = 1 := by
    obtain ⟨f, h0, h1, _⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton : IsClosed {i.val.1}) (isClosed_singleton : IsClosed {i.val.2})
      (Set.disjoint_singleton.mpr i.property)
    exact ⟨f, h0 (Set.mem_singleton _), h1 (Set.mem_singleton _)⟩
  choose f h0 h1 using hsep
  let g : K → I → ℝ := fun x i => f i x
  have hcont : Continuous g := continuous_pi (fun i => (f i).continuous)
  have hinj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    let i : I := ⟨(x, y), hne⟩
    have he := congrFun hxy i
    change f i i.val.1 = f i i.val.2 at he
    rw [h0, h1] at he
    exact zero_ne_one he
  exact (hcont.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

variable {𝕜 : Type} [RCLike 𝕜] (K : Type*) [TopologicalSpace K] [T2Space K]

/-- Extension by zero to infinity, as a continuous function on the compactification. -/
def cZeroAtInfinity (f : C₀(K, 𝕜)) : C(OnePoint K, 𝕜) :=
  OnePoint.continuousMapMk f.toContinuousMap 0
    (by simpa only [Filter.coclosedCompact_eq_cocompact] using zero_at_infty f)

def cZeroAtInfinityIsometry : C₀(K, 𝕜) →ₗᵢ[𝕜] C(OnePoint K, 𝕜) where
  toFun := cZeroAtInfinity K
  map_add' f g := by
    ext x
    cases x with
    | infty => exact (zero_add (0 : 𝕜)).symm
    | coe x => rfl
  map_smul' a f := by
    ext x
    cases x with
    | infty => exact (smul_zero a).symm
    | coe x => rfl
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      cases x with
      | infty => change ‖(0 : 𝕜)‖ ≤ ‖f‖; simpa only [norm_zero] using norm_nonneg f
      | coe x => exact f.toBCF.norm_coe_le_norm x
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg (cZeroAtInfinity K f))).mpr
      intro x
      exact (cZeroAtInfinity K f).norm_coe_le_norm (x : OnePoint K)

theorem countable_cZero_separable [LocallyCompactSpace K] [Countable K] :
    TopologicalSpace.SeparableSpace C₀(K, 𝕜) := by
  letI : Countable (OnePoint K) := inferInstanceAs (Countable (Option K))
  letI := countable_compact_secondCountable (OnePoint K)
  exact (cZeroAtInfinityIsometry (𝕜 := 𝕜) K).isometry.isEmbedding.separableSpace

end ThesisCommon
