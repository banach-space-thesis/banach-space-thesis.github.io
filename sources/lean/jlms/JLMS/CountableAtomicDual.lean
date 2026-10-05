import JLMS.Rudin
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Separability of countably indexed atomic duals

The coordinate vectors span a dense subspace of ℓ¹. For a countable index
set their span, and then its closure, are separable. The proved Rudin
isometry transfers this separability to the dual of C₀(K) when K is countable.
This is the analytic ingredient of the compact countable-image argument.
-/

noncomputable section

attribute [local instance] Classical.decEq

open Set Filter Topology TopologicalSpace

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {I : Type*}

theorem dense_span_ellOneOn_units :
    Dense (Submodule.span 𝕜 (range fun i : I =>
      (lp.single 1 i (1 : 𝕜) : ellOneOn 𝕜 I)) : Set (ellOneOn 𝕜 I)) := by
  classical
  let S := Submodule.span 𝕜 (range fun i : I => (lp.single 1 i (1 : 𝕜) : ellOneOn 𝕜 I))
  intro a
  have h := lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) a
  apply isClosed_closure.mem_of_tendsto h (Eventually.of_forall ?_)
  intro t
  apply subset_closure
  apply Submodule.sum_mem S
  intro i hi
  have hsingle : (lp.single 1 i (a i) : ellOneOn 𝕜 I) =
      a i • lp.single 1 i (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : I => 𝕜) 1 i (a i) (1 : 𝕜)
  rw [hsingle]
  exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

/-- ℓ¹ on a countable index set is separable. -/
theorem ellOneOn_separable [Countable I] : SeparableSpace (ellOneOn 𝕜 I) := by
  have hs : IsSeparable (range fun i : I => (lp.single 1 i (1 : 𝕜) : ellOneOn 𝕜 I)) :=
    (countable_range _).isSeparable
  exact (dense_span_ellOneOn_units (𝕜 := 𝕜) (I := I)).isSeparable_iff.mp hs.span

variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

/-- The dual of C₀(K) is separable when K is countable and scattered. -/
theorem cZero_dual_separable_of_countable [Countable K] (hK : IsScattered K) :
    SeparableSpace (CZero 𝕜 K →L[𝕜] 𝕜) := by
  letI : SeparableSpace (ellOneOn 𝕜 K) := ellOneOn_separable
  obtain ⟨M⟩ := exists_atomicDualModel (𝕜 := 𝕜) hK
  exact M.representation.symm.surjective.denseRange.separableSpace
    M.representation.symm.continuous

end JLMS
