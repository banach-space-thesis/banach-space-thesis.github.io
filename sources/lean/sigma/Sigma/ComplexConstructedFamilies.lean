import Sigma.ComplexConstructionState
import Sigma.ConstructedFamilies

/-! The complex-selected splitting families are infinite and almost disjoint. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem complex_threeLevelChoice_family_properties {I : Type} [Infinite I]
    (μ : I → ComplexAtomicRows) (R : I → Set ℕ) (d : ∀ i, ComplexThreeLevelChoice (μ i) (R i))
    (hpair : Pairwise (fun i j => (R i ∩ R j).Finite)) :
    AlmostDisjoint (splitFamily (fun i => (d i).J₁) (fun i => (d i).Z)) ∧
      (splitFamily (fun i => (d i).J₁) (fun i => (d i).Z)).Infinite := by
  have hinf (i : I) : (d i).J₁.Infinite := (d i).infinite_J₂.mono (d i).J₂_subset
  have hsub (i : I) : (d i).J₁ ⊆ R i := (d i).J₁_subset.trans (d i).J₀_subset
  have hJ : Pairwise (fun i j => ((d i).J₁ ∩ (d j).J₁).Finite) := by
    intro i j hij
    exact (hpair hij).subset (Set.inter_subset_inter (hsub i) (hsub j))
  exact ⟨splitFamily_almostDisjoint _ _ hinf (fun i => (d i).splits) hJ,
    splitFamily_infinite _ _ hinf (fun i => (d i).splits) hJ⟩


end SigmaNonprimarity

