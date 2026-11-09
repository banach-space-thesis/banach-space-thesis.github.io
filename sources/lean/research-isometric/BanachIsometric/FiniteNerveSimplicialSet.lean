import BanachIsometric.FiniteNerveOrderedFaces
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! The actual contravariant ordered-simplex functor of the finite complex. -/

noncomputable section
namespace BanachIsometric.FiniteNerve
open CategoryTheory Simplicial Opposite
variable {ι : Type} [LinearOrder ι] [Fintype ι]

def orderedSimplicialSet (K : Complex ι) : SimplicialObject (Type) where
  obj Δ := OrderedSimplex K Δ.unop.len
  map θ := pullbackOrderedSimplex K θ.unop
  map_id Δ := by
    funext v
    apply Subtype.ext
    ext i
    rfl
  map_comp θ ψ := by
    funext v
    apply Subtype.ext
    ext i
    rfl

end BanachIsometric.FiniteNerve
