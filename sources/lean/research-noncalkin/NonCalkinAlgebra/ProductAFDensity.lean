import NonCalkinAlgebra.ProductAFAlgebra
import NonCalkinAlgebra.SeparatedDensity
import NonCalkinAlgebra.MetricCardinality
import Mathlib.SetTheory.Cardinal.Finsupp

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
open NonCalkinAlgebra.FiniteBlockRefinement NonCalkinAlgebra.NormedStarDirectLimit
open UniformSpace
open scoped Matrix.Norms.L2Operator NonCalkinAlgebra.NormedStarCompletion

variable {ι : Type} [Nonempty ι] (D : ι → RootedBlockDiagram.{0})

theorem cardinal_tensorStage_le (a : Level ι) : Cardinal.mk (TensorStage D a) ≤ Cardinal.continuum := by
  let b := Module.finBasis ℂ (TensorStage D a)
  rw [b.equivFun.toEquiv.cardinal_eq, Cardinal.mk_arrow, Cardinal.mk_complex, Cardinal.mk_fin]
  simpa only [Cardinal.lift_id] using
    (Cardinal.power_nat_le (n := Module.finrank ℂ (TensorStage D a)) Cardinal.aleph0_le_continuum)

theorem cardinal_tensorLimit_le (hι : Cardinal.mk ι ≤ Cardinal.continuum) :
    Cardinal.mk (TensorLimit D) ≤ Cardinal.continuum := by
  have ha : Cardinal.mk (Level ι) ≤ Cardinal.continuum := by
    rw [Cardinal.mk_finsupp_nat]
    exact max_le hι Cardinal.aleph0_le_continuum
  have hc : Cardinal.mk (Σ a : Level ι, TensorStage D a) ≤ Cardinal.continuum := by
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : Level ι => Cardinal.continuum) :=
        Cardinal.sum_le_sum _ _ (cardinal_tensorStage_le D)
      _ = Cardinal.mk (Level ι) * Cardinal.continuum := Cardinal.sum_const' _ _
      _ ≤ Cardinal.continuum := cardinal_prod_le_continuum ha le_rfl
  let f : (Σ a : Level ι, TensorStage D a) → TensorLimit D :=
    fun p => completedEmbedding (tensorConnecting D) p.1 p.2
  have hdense : DenseRange f := by
    apply Completion.denseRange_coe.mono
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, x, rfl⟩ := DirectLimit.exists_eq_mk (tensorConnecting D) z
    exact ⟨⟨a, x⟩, rfl⟩
  have hcard := cardinal_closure_le_continuum (Set.range f) (Cardinal.mk_range_le.trans hc)
  rw [hdense.closure_range, Cardinal.mk_univ] at hcard
  exact hcard

theorem tensorLimit_density_of_separated (hι : Cardinal.mk ι ≤ Cardinal.continuum)
    {J : Type} (hJ : Cardinal.mk J = Cardinal.continuum) (x : J → TensorLimit D)
    (hx : ∀ i j, i ≠ j → 1 ≤ ‖x i - x j‖) :
    HasDensityCharacter (TensorLimit D) Cardinal.continuum := by
  have hmin (S : Set (TensorLimit D)) (hS : Dense S) :
      Cardinal.continuum ≤ Cardinal.mk S := by
    rw [← hJ]
    exact cardinal_le_dense_of_separated x (by simpa only [dist_eq_norm] using hx) S hS
  refine ⟨⟨Set.univ, dense_univ, ?_⟩, hmin⟩
  exact le_antisymm (by simpa only [Cardinal.mk_univ] using cardinal_tensorLimit_le D hι)
    (hmin Set.univ dense_univ)

end NonCalkinAlgebra.FiniteBlockRefinement.RootedBlockDiagram
