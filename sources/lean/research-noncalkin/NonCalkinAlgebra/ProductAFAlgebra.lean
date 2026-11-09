import NonCalkinAlgebra.ProductBlockDiagram
import NonCalkinAlgebra.CompletedAFSimplicity
import NonCalkinAlgebra.FiniteBlockSimplicity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement NonCalkinAlgebra.NormedStarDirectLimit
open scoped Matrix.Norms.L2Operator NonCalkinAlgebra.NormedStarCompletion

universe u
variable {ι : Type u} (D : ι → RootedBlockDiagram.{u})

abbrev TensorStage (a : Level ι) := Blocks (TensorRow D a)

instance tensorStageFiniteDimensional (a : Level ι) :
    FiniteDimensional ℂ (TensorStage D a) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ c : TensorColor D a,
    Matrix (TensorRow D a c) (TensorRow D a c) ℂ))

instance tensorStageCStar (a : Level ι) : CStarAlgebra (TensorStage D a) where
  toCompleteSpace := FiniteDimensional.complete ℂ _

instance tensorStageNormOne (a : Level ι) : NormOneClass (TensorStage D a) := by
  change NormOneClass (∀ c : TensorColor D a, Matrix (TensorRow D a c) (TensorRow D a c) ℂ)
  infer_instance

instance tensorPreservesNorm : PreservesNorm (tensorConnecting D) where
  norm_map a b h x :=
    le_antisymm (NonUnitalStarAlgHom.norm_apply_le (tensorConnecting D a b h) x)
      (norm_le_starAlgHom_of_finiteDimensional (tensorConnecting D a b h)
        (tensorConnecting_injective D a b h) x)

abbrev TensorLimit := Completed (tensorConnecting D)

theorem tensorLimit_AF : IsApproximatelyFiniteDimensional (TensorLimit D) :=
  completed_AF (tensorConnecting D)

theorem tensorLimit_simple (hD : ∀ i, (D i).EventuallyMixes) :
    IsTopologicallySimple (TensorLimit D) := by
  apply completed_simple (tensorConnecting D)
  intro a
  obtain ⟨b, hab, hmix⟩ := tensorRefinement_eventually_mixes D hD a
  refine ⟨b, hab, fun B _ _ _ g => ?_⟩
  let f := tensorRefinement D a b hab
  let h := g.comp f.hom.toAlgHom
  change Function.Injective h
  apply (injective_iff_map_eq_zero h).2
  intro x hx
  by_contra! hne
  obtain ⟨c, hc⟩ : ∃ c, x c ≠ 0 := by
    by_contra! hc
    exact hne (funext hc)
  have hcomponents : ∀ d, f.hom x d ≠ 0 := by
    intro d hd
    obtain ⟨k, hcolor⟩ := hmix c d
    subst c
    apply hc
    apply Matrix.ext
    intro i j
    rw [← f.hom_apply_same x d k i j, hd]
    rfl
  exact (map_ne_zero_of_component_ne_zero g (f.hom x) hcomponents) hx

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
