import BanachIsometric.EilenbergZilberProductHomotopy
import BanachIsometric.EilenbergZilberTensorHomotopy
import BanachIsometric.RawSingularChainComplex
import BanachIsometric.DegreeOneChainHomotopy

/-! The two actual acyclic-model homotopies give a chain homotopy
equivalence between product singular chains and the signed tensor complex. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW CategoryTheory

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorChainComplex : ChainComplex (ModuleCat.{u} ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ (rawTensorTotalDegree X Y n))
    (fun n => ModuleCat.ofHom (rawTensorBoundary X Y n))
    (fun n => ModuleCat.hom_ext_iff.mpr (rawTensorBoundary_squared X Y n))

theorem rawTensorChainComplex_d (n : ℕ) :
    (rawTensorChainComplex X Y).d (n + 1) n = ModuleCat.ofHom (rawTensorBoundary X Y n) :=
  ChainComplex.of_d _ _ _ n

def rawAlexanderWhitneyChainMap : rawRationalChainComplex (X × Y) ⟶ rawTensorChainComplex X Y where
  f n := ModuleCat.ofHom (rawAlexanderWhitneyHomogeneous X Y n)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    rw [rawTensorChainComplex_d, rawRationalChainComplex_d]
    exact ModuleCat.hom_ext_iff.mpr (rawAlexanderWhitneyHomogeneous_boundary j)

def rawEilenbergZilberChainMap : rawTensorChainComplex X Y ⟶ rawRationalChainComplex (X × Y) where
  f n := ModuleCat.ofHom (rawSymmetricEilenbergZilber n)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    rw [rawTensorChainComplex_d, rawRationalChainComplex_d]
    exact ModuleCat.hom_ext_iff.mpr (rawSymmetricEilenbergZilber_boundary j)

def rawProductChainHomotopy :
    Homotopy (rawAlexanderWhitneyChainMap X Y ≫ rawEilenbergZilberChainMap X Y)
      (𝟙 (rawRationalChainComplex (X × Y))) :=
  chainHomotopyOfDegreeOne (fun n => ModuleCat.ofHom (rawProductHomotopy n)) (by
    rw [rawRationalChainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro c
    change RawRationalChains (X × Y) 0 at c
    change rawProductComposite 0 c = rawBoundary 0 (rawProductHomotopy 0 c) + c
    exact sub_eq_iff_eq_add.mp (rawProductHomotopy_zero c).symm) (by
      intro n
      rw [rawRationalChainComplex_d, rawRationalChainComplex_d]
      apply ModuleCat.hom_ext_iff.mpr
      apply LinearMap.ext
      intro c
      change RawRationalChains (X × Y) (n + 1) at c
      change rawProductComposite (n + 1) c = rawProductHomotopy n (rawBoundary n c) +
        rawBoundary (n + 1) (rawProductHomotopy (n + 1) c) + c
      rw [add_comm (rawProductHomotopy n (rawBoundary n c))]
      exact sub_eq_iff_eq_add.mp (rawProductHomotopy_succ n c).symm)

def rawTensorChainHomotopy :
    Homotopy (rawEilenbergZilberChainMap X Y ≫ rawAlexanderWhitneyChainMap X Y)
      (𝟙 (rawTensorChainComplex X Y)) :=
  chainHomotopyOfDegreeOne (fun n => ModuleCat.ofHom (rawTensorEZHomotopy n)) (by
    rw [rawTensorChainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro c
    change ↥(rawTensorTotalDegree X Y 0) at c
    change rawTensorComposite 0 c = rawTensorBoundary X Y 0 (rawTensorEZHomotopy 0 c) + c
    exact sub_eq_iff_eq_add.mp (rawTensorEZHomotopy_zero c).symm) (by
      intro n
      rw [rawTensorChainComplex_d, rawTensorChainComplex_d]
      apply ModuleCat.hom_ext_iff.mpr
      apply LinearMap.ext
      intro c
      change ↥(rawTensorTotalDegree X Y (n + 1)) at c
      change rawTensorComposite (n + 1) c = rawTensorEZHomotopy n (rawTensorBoundary X Y n c) +
        rawTensorBoundary X Y (n + 1) (rawTensorEZHomotopy (n + 1) c) + c
      rw [add_comm (rawTensorEZHomotopy n (rawTensorBoundary X Y n c))]
      exact sub_eq_iff_eq_add.mp (rawTensorEZHomotopy_succ n c).symm)

def rawEilenbergZilberHomotopyEquiv :
    HomotopyEquiv (rawRationalChainComplex (X × Y)) (rawTensorChainComplex X Y) where
  hom := rawAlexanderWhitneyChainMap X Y
  inv := rawEilenbergZilberChainMap X Y
  homotopyHomInvId := rawProductChainHomotopy X Y
  homotopyInvHomId := rawTensorChainHomotopy X Y

end BanachIsometric.SingularEZ
