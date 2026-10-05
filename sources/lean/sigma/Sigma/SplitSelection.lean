import Sigma.LocalizedSelection

/-! The successor-stage selection includes both halves of each new split. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem pairedSeparated_mono {B Btilde D Dtilde : BooleanSubalgebra (Set ℕ)}
    (hB : B ≤ D) (hBtilde : Btilde ≤ Dtilde) {M N : Set PairedMeasure}
    (h : PairedSeparated B Btilde M N) : PairedSeparated D Dtilde M N := by
  classical
  let inclusion : B ⊕ Btilde → D ⊕ Dtilde :=
    Sum.map (fun A => ⟨A.val, hB A.property⟩) (fun A => ⟨A.val, hBtilde A.property⟩)
  obtain ⟨ε, hε, F, _, hsep⟩ := h
  refine ⟨ε, hε, F.image inclusion, Set.subset_univ _, ?_⟩
  intro μ hμ ν hν
  obtain ⟨t, ht, hgap⟩ := hsep μ hμ ν hν
  refine ⟨inclusion t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  cases t <;> exact hgap

theorem split_haydon_selection {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (M N : I → Set PairedMeasure) (hnsep : ∀ i, ¬ PairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun C D => (C ∩ D).Finite)) (hcard : #S = 𝔠) :
    ∃ C ∈ S, ∀ Z ⊆ C, ∀ i,
      ¬ PairedSeparated (adjoinSet (adjoinSet (B i) Z) (C \ Z)) (Btilde i) (M i) (N i) := by
  obtain ⟨C, hCS, hC⟩ := localized_haydon_selection B Btilde κ hκ hκlt hI
    hB hBtilde hfinite M N hnsep S hS hcard
  exact ⟨C, hCS, fun Z hZ i h => hC i
    (pairedSeparated_mono (adjoin_split_le_localized (B i) hZ) le_rfl h)⟩

theorem split_haydon_selection_right {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set PairedMeasure) (hnsep : ∀ i, ¬ PairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun C D => (C ∩ D).Finite)) (hcard : #S = 𝔠) :
    ∃ C ∈ S, ∀ Z ⊆ C, ∀ i,
      ¬ PairedSeparated (B i) (adjoinSet (adjoinSet (Btilde i) Z) (C \ Z)) (M i) (N i) := by
  obtain ⟨C, hCS, hC⟩ := localized_haydon_selection_right B Btilde κ hκ hκlt hI
    hB hBtilde hfinite M N hnsep S hS hcard
  exact ⟨C, hCS, fun Z hZ i h => hC i
    (pairedSeparated_mono le_rfl (adjoin_split_le_localized (Btilde i) hZ) h)⟩

end SigmaNonprimarity
