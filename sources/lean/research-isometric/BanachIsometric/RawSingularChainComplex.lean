import BanachIsometric.RawSingularHomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Topology.Category.TopCat.Basic

/-! The proved real-coordinate singular boundary gives a genuine
categorical chain complex and functor. Its maps remain the literal
pushforward maps on finitely supported continuous simplices. -/

noncomputable section
universe u
namespace BanachIsometric.SingularPrism

open CategoryTheory

def rawRationalChainComplex (X : Type u) [TopologicalSpace X] : ChainComplex (ModuleCat.{u} ℚ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℚ (RawRationalChains X n))
    (fun n => ModuleCat.ofHom (rawBoundary n))
    (fun n => ModuleCat.hom_ext_iff.mpr (rawBoundary_squared n))

theorem rawRationalChainComplex_d (X : Type*) [TopologicalSpace X] (n : ℕ) :
    (rawRationalChainComplex X).d (n + 1) n = ModuleCat.ofHom (rawBoundary n) :=
  ChainComplex.of_d _ _ _ n

def rawRationalChainMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : rawRationalChainComplex X ⟶ rawRationalChainComplex Y where
  f n := ModuleCat.ofHom (rawChainMap f n)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    rw [rawRationalChainComplex_d, rawRationalChainComplex_d]
    exact ModuleCat.hom_ext_iff.mpr (rawChainMap_boundary f j)

theorem rawRationalChainMap_f {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    (rawRationalChainMap f).f n = ModuleCat.ofHom (rawChainMap f n) := rfl

def rawRationalChainFunctor : TopCat.{0} ⥤ ChainComplex (ModuleCat ℚ) ℕ where
  obj X := rawRationalChainComplex X
  map f := rawRationalChainMap f.hom
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext_iff.mpr (rawChainMap_id (X := X) n)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext_iff.mpr (rawChainMap_comp f.hom g.hom n)

end BanachIsometric.SingularPrism
