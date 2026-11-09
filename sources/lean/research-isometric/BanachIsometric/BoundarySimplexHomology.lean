import BanachIsometric.BoundarySimplexTopGenerator
import BanachIsometric.BoundarySimplexLowerHomology

/-! The full positive rational homology computation of the ACTUAL finite
boundary simplex: the explicit class gives ℚ in dimension n+1 and all other
positive degrees vanish. This is a finite simplicial computation, separate
from the still-required comparison with singular sphere homology. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve

theorem boundarySimplex_higher_chains_subsingleton (n q : ℕ) (hq : n + 1 < q) :
    Subsingleton (FiniteRationalChains (boundarySimplexComplex n) q) := by
  by_cases he : q = n + 2
  · subst q
    exact boundarySimplex_next_chains_subsingleton n
  · apply subsingleton_finiteRationalChains_of_card_le
    simp only [Fintype.card_fin]
    omega

theorem boundarySimplex_higher_homology_subsingleton (n q : ℕ) (hq : n + 1 < q) :
    Subsingleton (QuotientRationalHomology (boundarySimplexComplex n) q) := by
  letI := boundarySimplex_higher_chains_subsingleton n q hq
  apply (Submodule.Quotient.subsingleton_iff _).mpr
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx]
  exact (rationalBoundaries (boundarySimplexComplex n) q).zero_mem

theorem boundarySimplex_positive_homology_away_top (n d : ℕ) (hd : d ≠ n) :
    Subsingleton (QuotientRationalHomology (boundarySimplexComplex n) (d + 1)) := by
  rcases lt_or_gt_of_ne hd with h | h
  · exact boundarySimplex_lower_homology_subsingleton n d h
  · exact boundarySimplex_higher_homology_subsingleton n (d + 1) (by omega)

end BanachIsometric.SingularPrism
