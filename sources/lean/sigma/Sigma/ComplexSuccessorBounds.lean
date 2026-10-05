import Sigma.ComplexSuccessorSelection
import Sigma.SuccessorBounds

noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem ComplexThreeLevelChoice.adjoin_cardinal_bound {μ : ℕ → lp (fun _ : Point => ℂ) 1} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) (B : BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hB : #B ≤ κ) : #(d.adjoin B) ≤ κ :=
  adjoinSet_cardinal_bound _ _ κ hκ (adjoinSet_cardinal_bound B _ κ hκ hB)

theorem ComplexThreeLevelChoice.le_adjoin {μ : ℕ → lp (fun _ : Point => ℂ) 1} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) (B : BooleanSubalgebra (Set ℕ)) : B ≤ d.adjoin B := by
  intro A hA
  apply BooleanSubalgebra.subset_closure
  left
  exact BooleanSubalgebra.subset_closure (Or.inl hA)

theorem complex_exists_successor_choice_right {I : Type}
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set ComplexPairedMeasure) (hnsep : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) (M i) (N i))
    (C : Set ℕ) (hC : C.Infinite)
    (μ : ℕ → lp (fun _ : Point => ℂ) 1) (hμ : ComplexAdmissible μ)
    (ρ : ℕ → ComplexPairedMeasure) (B₀ Btilde₀ : BooleanSubalgebra (Set ℕ))
    (hB₀ : #B₀ ≤ κ) (hBtilde₀ : #Btilde₀ ≤ κ) :
    ∃ d : ComplexThreeLevelChoice μ C, d.PairedNonseparated ρ B₀ Btilde₀ ∧
      ∀ i, ¬ ComplexPairedSeparated (B i) (d.adjoin (Btilde i)) (M i) (N i) := by
  have hnsep' (i : I) :
      ¬ ComplexPairedSeparated (Btilde i) (B i) (complexSwapMeasure '' M i) (complexSwapMeasure '' N i) :=
    fun h => hnsep i ((complexPairedSeparated_swap_iff (B i) (Btilde i) (M i) (N i)).mp h)
  obtain ⟨d, hd, hpres⟩ := complex_exists_successor_choice Btilde B κ hκ hκlt hI hBtilde hB hfinite
    (fun i => complexSwapMeasure '' M i) (fun i => complexSwapMeasure '' N i) hnsep'
    C hC μ hμ (complexSwapMeasure ∘ ρ) Btilde₀ B₀ hBtilde₀ hB₀
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · intro h
    apply hd.1
    simpa [Set.image_image, Function.comp_def] using
      complexPairedSeparated_swap B₀ Btilde₀ (ρ '' d.J₂) (ρ '' (d.J₁ \ d.J₂)) h
  · intro h
    apply hd.2
    simpa [Set.image_image, Function.comp_def] using
      complexPairedSeparated_swap B₀ Btilde₀ (ρ '' d.J₁) (ρ '' (d.J₀ \ d.J₁)) h
  · intro i h
    exact hpres i (complexPairedSeparated_swap (B i) (d.adjoin (Btilde i)) (M i) (N i) h)

end SigmaNonprimarity
