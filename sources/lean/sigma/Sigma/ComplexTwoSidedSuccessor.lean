import Sigma.ComplexSuccessorBounds

/-! Simultaneous successor step with the four new nonseparation conditions.
The second selection includes the two new first-copy pairs among the pairs
it must preserve. Both split pieces are adjoined on each base. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem complex_exists_twoSided_successor {I : Type}
    (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (hfinite_tilde : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set ComplexPairedMeasure) (hnsep : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) (M i) (N i))
    (C Ctilde : Set ℕ) (hC : C.Infinite) (hCtilde : Ctilde.Infinite)
    (μ μtilde : ℕ → lp (fun _ : Point => ℂ) 1) (hμ : ComplexAdmissible μ) (hμtilde : ComplexAdmissible μtilde)
    (ρ σ : ℕ → ComplexPairedMeasure) (B₀ Btilde₀ : BooleanSubalgebra (Set ℕ))
    (hB₀ : #B₀ ≤ κ) (hBtilde₀ : #Btilde₀ ≤ κ)
    (hfinite₀ : ∀ F : Set ℕ, F.Finite → F ∈ Btilde₀) :
    ∃ (d : ComplexThreeLevelChoice μ C) (dtilde : ComplexThreeLevelChoice μtilde Ctilde),
      d.PairedNonseparated ρ B₀ (dtilde.adjoin Btilde₀) ∧
      dtilde.PairedNonseparated σ (d.adjoin B₀) Btilde₀ ∧
      ∀ i, ¬ ComplexPairedSeparated (d.adjoin (B i)) (dtilde.adjoin (Btilde i)) (M i) (N i) := by
  classical
  obtain ⟨d, hd, hpres⟩ := complex_exists_successor_choice B Btilde κ hκ hκlt hI
    hB hBtilde hfinite M N hnsep C hC μ hμ ρ B₀ Btilde₀ hB₀ hBtilde₀
  let L : I ⊕ Bool → BooleanSubalgebra (Set ℕ) := Sum.elim (fun i => d.adjoin (B i)) (fun _ => B₀)
  let R : I ⊕ Bool → BooleanSubalgebra (Set ℕ) := Sum.elim Btilde (fun _ => Btilde₀)
  let P : I ⊕ Bool → Set ComplexPairedMeasure := Sum.elim M (fun b =>
    match b with
    | false => ρ '' d.J₂
    | true => ρ '' d.J₁)
  let Q : I ⊕ Bool → Set ComplexPairedMeasure := Sum.elim N (fun b =>
    match b with
    | false => ρ '' (d.J₁ \ d.J₂)
    | true => ρ '' (d.J₀ \ d.J₁))
  have hLR (j : I ⊕ Bool) : ¬ ComplexPairedSeparated (L j) (R j) (P j) (Q j) := by
    cases j with
    | inl i => exact hpres i
    | inr b => cases b; exact hd.1; exact hd.2
  have hL (j : I ⊕ Bool) : #(L j) ≤ κ := by
    cases j with
    | inl i => exact d.adjoin_cardinal_bound (B i) κ hκ (hB i)
    | inr _ => exact hB₀
  have hR (j : I ⊕ Bool) : #(R j) ≤ κ := by
    cases j with
    | inl i => exact hBtilde i
    | inr _ => exact hBtilde₀
  have hRfin (j : I ⊕ Bool) (F : Set ℕ) (hF : F.Finite) : F ∈ R j := by
    cases j with
    | inl i => exact hfinite_tilde i F hF
    | inr _ => exact hfinite₀ F hF
  have hI' : #(I ⊕ Bool) ≤ κ := by
    have hbool : #Bool ≤ κ := Cardinal.mk_le_aleph0.trans hκ
    simpa using (add_le_add hI hbool).trans_eq (Cardinal.add_eq_self hκ)
  obtain ⟨dtilde, hdtilde, hpres'⟩ := complex_exists_successor_choice_right L R κ hκ hκlt hI'
    hL hR hRfin P Q hLR Ctilde hCtilde μtilde hμtilde σ (d.adjoin B₀) Btilde₀
    (d.adjoin_cardinal_bound B₀ κ hκ hB₀) hBtilde₀
  exact ⟨d, dtilde, ⟨hpres' (.inr false), hpres' (.inr true)⟩,
    hdtilde, fun i => hpres' (.inl i)⟩

end SigmaNonprimarity
