import BanachIsometric.RationalSingularChains
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Native categorical homology of the actual rational singular chain functor.
The free module model is literal finitely supported rational functions. -/

noncomputable section
namespace BanachIsometric

open CategoryTheory

def rationalSingularHomologyFunctor (n : ℕ) : TopCat.{0} ⥤ ModuleCat ℚ :=
  rationalSingularChainFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n

end BanachIsometric
