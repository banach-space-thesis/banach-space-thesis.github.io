import BanachIsometric.SingularChainModelTransport
import BanachIsometric.RawSingularChainComplex

/-! A genuine natural isomorphism of chain complexes, not merely a
degreewise identification of their bases. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open CategoryTheory AlgebraicTopology

def rawNativeSingularChainIso (X : TopCat.{0}) :
    rawRationalChainComplex X ≅ rationalSingularChainComplex X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (rawNativeSingularChainEquiv X n).toModuleIso) (by
      intro i j hij
      have hi : j + 1 = i := hij
      subst i
      rw [rawRationalChainComplex_d]
      have hd : (rationalSingularChainComplex X).d (j + 1) j =
          ModuleCat.ofHom (rationalSingularBoundary X j) := by
        exact alternatingFaceMapComplex_obj_d (rationalSingularSimplicialFunctor.obj X) j
      rw [hd]
      exact ModuleCat.hom_ext_iff.mpr (rawNativeSingularChainEquiv_boundary X j))

def rawNativeSingularChainNatIso :
    rawRationalChainFunctor ≅ rationalSingularChainFunctor :=
  NatIso.ofComponents rawNativeSingularChainIso (by
    intro X Y f
    apply HomologicalComplex.Hom.ext
    funext n
    exact ModuleCat.hom_ext_iff.mpr (rawNativeSingularChainEquiv_map f n).symm)

end BanachIsometric.SingularPrism
