import BanachIsometric.QuaternionicSeminormFactors
import BanachIsometric.CofinalQuotientDimension
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! The canonical inverse-limit representation for a complete Hausdorff
space defined by an increasing family of actual right-quaternionic seminorms.
The original topology and right action are preserved. No Hilbertianity of
the constructed completions is assumed in this structural theorem. -/

namespace BanachIsometric.Quaternionic

open UniformSpace ProjectiveOverRing
open scoped Topology Uniformity

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

section OriginalUniformity

variable [UniformSpace X] [IsUniformAddGroup X]

theorem seminormCompletionProduct_isUniformInducing (p : ℕ → RightSeminorm X)
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) :
    IsUniformInducing (projectiveProductMap (fun i => seminormCompletionMap (p i))) := by
  apply isUniformInducing_iff_uniformSpace.mpr
  have hcoord (i : ℕ) :
      UniformSpace.comap (seminormCompletionMap (p i))
        (inferInstance : UniformSpace (SeminormCompletion (p i))) =
      (p i).toRealSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace :=
    (seminormCompletionMap_isUniformInducing_model (p i)).comap_uniformSpace
  calc
    UniformSpace.comap (projectiveProductMap (fun i => seminormCompletionMap (p i)))
        (inferInstance : UniformSpace (∀ i, SeminormCompletion (p i))) =
        ⨅ i, UniformSpace.comap (seminormCompletionMap (p i))
          (inferInstance : UniformSpace (SeminormCompletion (p i))) := by
      simp only [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
      rfl
    _ = ⨅ i, (p i).toRealSeminorm.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace := iInf_congr hcoord
    _ = (inferInstance : UniformSpace X) :=
      (SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf (fun i => (p i).toRealSeminorm)).mp hp |>.symm

end OriginalUniformity

def seminormLimitSubmodule (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm)) :
    Submodule Hᵐᵒᵖ (∀ i, SeminormCompletion (p i)) :=
  projectiveCompatibleSubmodule (fun _ _ hij => completedSeminormFactor (hmono hij))

section CompleteOriginal

variable [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

def seminormInverseLimitEquiv (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) :
    X ≃L[Hᵐᵒᵖ] seminormLimitSubmodule p hmono :=
  projectiveComparisonEquivOfComplete
    (fun _ _ hij => completedSeminormFactor (hmono hij))
    (fun i => seminormCompletionMap (p i))
    (fun _ _ hij x => completedSeminormFactor_completionMap (hmono hij) x)
    (fun i => seminormCompletionMap_denseRange (p i))
    (seminormCompletionProduct_isUniformInducing p hp)

@[simp] theorem seminormInverseLimitEquiv_apply (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) (x : X) (i : ℕ) :
    (seminormInverseLimitEquiv p hmono hp x).val i = seminormCompletionMap (p i) x := rfl

end CompleteOriginal

theorem seminormKernel_antitone (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm)) : Antitone (fun i => seminormKernel (p i)) := by
  intro i j hij x hx
  rw [mem_seminormKernel] at hx ⊢
  exact le_antisymm ((hmono hij x).trans_eq hx) (apply_nonneg (p i).toRealSeminorm x)

theorem seminormKernel_iInf_eq_bot [TopologicalSpace X] [T1Space X]
    (p : ℕ → RightSeminorm X) (hp : WithSeminorms (fun i => (p i).toRealSeminorm)) :
    (⨅ i, seminormKernel (p i)) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  by_contra hx0
  obtain ⟨i, hi⟩ := hp.separating_of_T1 x hx0
  exact hi ((mem_seminormKernel (p i) x).mp ((Submodule.mem_iInf (fun i => seminormKernel (p i))).mp hx i))

theorem cofinal_seminorm_quotient_dimension [TopologicalSpace X] [T1Space X]
    (p : ℕ → RightSeminorm X) (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm))
    (n : ℕ) (hn : (n : Cardinal) < Module.rank Hᵐᵒᵖ X) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (n : Cardinal) < Module.rank Hᵐᵒᵖ (SeminormQuotient (p k)) := by
  obtain ⟨k₀, hk₀⟩ := cofinal_quotient_dimension
    (fun i => seminormKernel (p i)) (seminormKernel_antitone p hmono) (seminormKernel_iInf_eq_bot p hp) n hn
  refine ⟨k₀, ?_⟩
  intro k hk
  rw [← (seminormQuotientEquiv (p k)).rank_eq]
  exact hk₀ k hk

end
end BanachIsometric.Quaternionic
