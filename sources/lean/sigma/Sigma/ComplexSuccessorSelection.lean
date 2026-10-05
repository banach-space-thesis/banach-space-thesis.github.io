import Sigma.ComplexPairedChoice
import Sigma.ComplexSplitSelection
import Sigma.PointCoding

/-! One half of the actual successor step: choose three levels and a splitting
that create the new nonseparated pairs and preserve all previously listed pairs. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

def ComplexThreeLevelChoice.adjoin {μ : ℕ → lp (fun _ : Point => ℂ) 1} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) (B : BooleanSubalgebra (Set ℕ)) : BooleanSubalgebra (Set ℕ) :=
  adjoinSet (adjoinSet B (codedSet d.Z)) (codedSet (cylinder d.J₁ \ d.Z))

theorem complex_exists_successor_choice {I : Type}
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (M N : I → Set ComplexPairedMeasure) (hnsep : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) (M i) (N i))
    (C : Set ℕ) (hC : C.Infinite)
    (μ : ℕ → lp (fun _ : Point => ℂ) 1) (hμ : ComplexAdmissible μ)
    (ρ : ℕ → ComplexPairedMeasure) (B₀ Btilde₀ : BooleanSubalgebra (Set ℕ))
    (hB₀ : #B₀ ≤ κ) (hBtilde₀ : #Btilde₀ ≤ κ) :
    ∃ d : ComplexThreeLevelChoice μ C, d.PairedNonseparated ρ B₀ Btilde₀ ∧
      ∀ i, ¬ ComplexPairedSeparated (d.adjoin (B i)) (Btilde i) (M i) (N i) := by
  classical
  obtain ⟨S, hcard, hsub, hAD⟩ := continuum_almostDisjoint_subsets C hC
  have hex (A : S) : ∃ d : ComplexThreeLevelChoice μ A.val, d.PairedNonseparated ρ B₀ Btilde₀ :=
    complex_exists_threeLevelChoice_pairedNonseparated A.val (hsub A.val A.property).2 μ hμ ρ B₀ Btilde₀
      (hB₀.trans_lt hκlt) (hBtilde₀.trans_lt hκlt)
  choose d hd using hex
  let K : S → Set ℕ := fun A => (d A).J₁
  have hKsub (A : S) : K A ⊆ A.val := (d A).J₁_subset.trans (d A).J₀_subset
  have hKinf (A : S) : (K A).Infinite := (d A).infinite_J₂.mono (d A).J₂_subset
  have hKinj := (almostDisjoint_thinning S hAD K hKsub hKinf).1
  let T : S → Set ℕ := fun A => codedSet (cylinder (K A))
  have hTinj : Function.Injective T := codedSet_injective.comp (cylinder_injective.comp hKinj)
  have hTcard : #(range T) = 𝔠 := (Cardinal.mk_range_eq T hTinj).trans hcard
  have hTAD : (range T).Pairwise (fun U V => (U ∩ V).Finite) := by
    rintro _ ⟨A, rfl⟩ _ ⟨D, rfl⟩ hne
    apply codedCylinder_inter_finite
    apply (hAD A.property D.property (fun h => hne (congrArg T (Subtype.ext h)))).subset
    exact Set.inter_subset_inter (hKsub A) (hKsub D)
  obtain ⟨V, ⟨A, rfl⟩, hV⟩ := complex_split_haydon_selection B Btilde κ hκ hκlt hI
    hB hBtilde hfinite M N hnsep (range T) hTAD hTcard
  let choice : ComplexThreeLevelChoice μ C :=
    { d A with J₀_subset := (d A).J₀_subset.trans (hsub A.val A.property).1 }
  refine ⟨choice, hd A, ?_⟩
  intro i
  have h := hV (codedSet (d A).Z) (codedSet_mono (d A).splits.1) i
  simpa only [ComplexThreeLevelChoice.adjoin, codedSet_diff] using h

end SigmaNonprimarity
