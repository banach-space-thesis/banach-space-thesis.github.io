import BanachIsometric.EilenbergZilberEquivalence
import BanachIsometric.RawTensorKunneth
import BanachIsometric.VectorChainHomologyEquiv

/-! Actual rational singular Künneth equivalence, with formulas on the
literal cycle classes in both directions. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW VectorChainSplitting

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

abbrev RawHomologyCycles (X : Type*) [TopologicalSpace X] (n : ℕ) :=
  VectorChainSplitting.cycles (rawFactorObjects X) (rawBoundary (X := X)) n

def rawEilenbergZilberHomologyEquiv (n : ℕ) : RawHomology (X × Y) n ≃ₗ[ℚ] RawTensorHomology X Y n :=
  chainHomologyEquiv (rawEilenbergZilberHomotopyEquiv X Y) n

def rawSingularKunnethEquiv (n : ℕ) : RawHomology (X × Y) n ≃ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  (rawEilenbergZilberHomologyEquiv X Y n).trans (rawTensorKunnethEquiv X Y n)

theorem rawSingularKunnethEquiv_cycle (n : ℕ) (c : RawHomologyCycles (X × Y) n) :
    rawSingularKunnethEquiv X Y n (rawFactorHomologyProjection (X × Y) n c.val) =
      rawTensorHomologyProjection X Y n (rawAlexanderWhitneyHomogeneous X Y n c.val) :=
  congrArg (rawSingularKunnethEquiv X Y n) (rawFactorHomologyProjection_cycle (X × Y) n c)

theorem rawSingularKunnethEquiv_symm_tensorCycle (n : ℕ) (c : rawTensorCycles X Y n) :
    (rawSingularKunnethEquiv X Y n).symm (rawTensorHomologyProjection X Y n c.val) =
      rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilber n c.val) := by
  apply (rawSingularKunnethEquiv X Y n).injective
  rw [LinearEquiv.apply_symm_apply]
  have he : rawEilenbergZilberHomologyEquiv X Y n
      (rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilber n c.val)) =
        Submodule.Quotient.mk c := by
    have h := chainHomologyMap_projection_cycle (hd := rawTensorBoundary_squared X Y)
      (he := rawBoundary_squared (X := X × Y)) (rawEilenbergZilberChainMap X Y) n c
    have hq : homologyProjection (rawTensorFactorObjects X Y) (rawTensorBoundary X Y)
        (rawTensorBoundary_squared X Y) n c.val = Submodule.Quotient.mk c :=
      congrArg (rawTensorBoundaries X Y n).mkQ
        (cycleProjection_cycle (rawTensorFactorObjects X Y) (rawTensorBoundary X Y)
          (rawTensorBoundary_squared X Y) n c)
    rw [hq] at h
    change (rawEilenbergZilberHomologyEquiv X Y n).symm (Submodule.Quotient.mk c) =
      rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilber n c.val) at h
    rw [← h, LinearEquiv.apply_symm_apply]
  change rawTensorHomologyProjection X Y n c.val =
    rawTensorKunnethEquiv X Y n (rawEilenbergZilberHomologyEquiv X Y n
      (rawFactorHomologyProjection (X × Y) n (rawSymmetricEilenbergZilber n c.val)))
  exact (congrArg (rawTensorKunnethEquiv X Y n) he).symm

end BanachIsometric.SingularEZ
