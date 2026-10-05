import Sigma.ContinuousRepresentation
import Sigma.Assembly

noncomputable section
namespace SigmaNonprimarity
open ThesisCommon

def auCompactumBundle {B : Set (Set Point)} (hB : AlmostDisjoint B) : Compactum := by
  letI := mrowkaT2 hB
  exact { Carrier := AUCompactum B }

/-- Equation (3) in Section 3.3 for the concrete compactum and concrete split family. -/
def continuousSplitEquiv {ι : Type*} (J : ι → Set ℕ) (b : ι → Set Point)
    (hsplit : ∀ i, Splits (J i) (b i)) (hB : AlmostDisjoint (splitFamily J b))
    (hInf : (splitFamily J b).Infinite) :
    C(AUCompactum (splitFamily J b), ℝ) ≃L[ℝ]
      CylinderJL (cylinderFamily J) × antisymmetricJL (splitFamily J b) :=
  (jlContinuousEquiv hB hInf).symm.toContinuousLinearEquiv.trans (splitJLEquiv J b hsplit)

/-- All topological and decomposition inputs to the main assembly are now discharged.
The two nonlattice conclusions still require the simultaneous transfinite construction. -/
theorem theorem_1_1_of_split_families {ι κ : Type*}
    (J : ι → Set ℕ) (b : ι → Set Point) (Jt : κ → Set ℕ) (bt : κ → Set Point)
    (hsplit : ∀ i, Splits (J i) (b i)) (hsplitT : ∀ i, Splits (Jt i) (bt i))
    (hB : AlmostDisjoint (splitFamily J b)) (hBt : AlmostDisjoint (splitFamily Jt bt))
    (hInf : (splitFamily J b).Infinite) (hInfT : (splitFamily Jt bt).Infinite)
    (hX : ¬ IsomorphicToBanachLattice (CandidateX (splitFamily J b) (cylinderFamily Jt)))
    (hXt : ¬ IsomorphicToBanachLattice (CandidateX (splitFamily Jt bt) (cylinderFamily J))) :
    Theorem_1_1.{0} :=
  theorem_1_1_of_crossed_decompositions (auCompactumBundle hB) (auCompactumBundle hBt)
    { Carrier := CylinderJL (cylinderFamily J) } { Carrier := antisymmetricJL (splitFamily J b) }
    { Carrier := CylinderJL (cylinderFamily Jt) } { Carrier := antisymmetricJL (splitFamily Jt bt) }
    (continuousSplitEquiv J b hsplit hB hInf) (continuousSplitEquiv Jt bt hsplitT hBt hInfT) hX hXt

end SigmaNonprimarity
