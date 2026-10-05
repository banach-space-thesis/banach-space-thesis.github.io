import Sigma.ThreeLevelSelection
import Sigma.MeasureSeparation
import ThesisCommon.Analysis.NonseparatedCut

/-! The two new nonseparation requirements at a construction stage, together
with the actual three-level splitting and all of its quantitative bounds. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

structure ThreeLevelChoice (μ : ℕ → lp (fun _ : Point => ℝ) 1) (C : Set ℕ) where
  J₀ : Set ℕ
  J₁ : Set ℕ
  J₂ : Set ℕ
  Z : Set Point
  a : ℝ
  delta : ℝ
  J₂_subset : J₂ ⊆ J₁
  J₁_subset : J₁ ⊆ J₀
  J₀_subset : J₀ ⊆ C
  infinite_J₂ : J₂.Infinite
  infinite_middle : (J₁ \ J₂).Infinite
  infinite_outer : (J₀ \ J₁).Infinite
  splits : Splits J₁ Z
  lower_a : (⨅ n, |μ n (n, false)|) ≤ a
  delta_pos : 0 < delta
  delta_small : delta < (⨅ n, |μ n (n, false)|) / 11
  positive_level : ∀ n ∈ J₂,
    |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) - 2*a| < 3*delta
  negative_level : ∀ n ∈ J₁ \ J₂,
    |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) + 2*a| < 3*delta
  zero_level : ∀ n ∈ J₀ \ J₁,
    |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z)| < 3*delta

def ThreeLevelChoice.Nonseparated {μ : ℕ → lp (fun _ : Point => ℝ) 1} {C : Set ℕ}
    (d : ThreeLevelChoice μ C) (ρ : ℕ → PairedMeasure)
    (B Btilde : BooleanSubalgebra (Set ℕ)) : Prop :=
  (¬ PairedSeparated B Btilde (ρ '' d.J₂) (ρ '' (d.J₁ \ d.J₂))) ∧
  (¬ PairedSeparated B Btilde (ρ '' d.J₁) (ρ '' (d.J₀ \ d.J₁)))

theorem exists_threeLevelChoice_nonseparated (C : Set ℕ) (hC : C.Infinite)
    (μ : ℕ → lp (fun _ : Point => ℝ) 1) (hμ : Admissible μ)
    (ρ : ℕ → PairedMeasure) (B Btilde : BooleanSubalgebra (Set ℕ))
    (hB : #B < 𝔠) (hBtilde : #Btilde < 𝔠) :
    ∃ d : ThreeLevelChoice μ C, d.Nonseparated ρ B Btilde := by
  classical
  let ev : ℕ → B ⊕ Btilde → ℝ := fun n t => ρ n (pairedTest B Btilde t)
  have hbound (n : ℕ) (t : B ⊕ Btilde) : |ev n t| ≤ 1 := (ρ n).abs_apply_le_one _
  have hI : #(B ⊕ Btilde) < 𝔠 := by
    simpa using Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hB hBtilde
  obtain ⟨J₀, H, a, δ, hHJ₀, hJ₀C, hH, hJ₀H, ha, hδ, hδsmall, hsmall, happ⟩ :=
    three_level_selection_control C μ hC hμ
  obtain ⟨J₁, hJ₁H, hJ₁, _, hnsep₁⟩ :=
    exists_infinite_nonseparated_cut ev hbound hI J₀ H hHJ₀ hH
  obtain ⟨J₂, hJ₂J₁, hJ₂, hmiddle, hnsep₂⟩ :=
    exists_infinite_nonseparated_cut ev hbound hI J₁ J₁ Set.Subset.rfl hJ₁
  have houter : (J₀ \ J₁).Infinite := by
    exact hJ₀H.mono (fun _ hx => ⟨hx.1, fun h => hx.2 (hJ₁H h)⟩)
  let Z := graphSplitter J₁ (levelChoice μ J₂)
  obtain ⟨hp, hn, hz⟩ := three_level_bounds_of_control μ hμ.2.1 J₀ H hHJ₀ a δ hδ
    hsmall happ J₁ J₂ hJ₁H hJ₂J₁
  let d : ThreeLevelChoice μ C :=
    ⟨J₀, J₁, J₂, Z, a, δ, hJ₂J₁, hJ₁H.trans hHJ₀, hJ₀C, hJ₂, hmiddle,
      houter, graphSplitter_splits _ _, ha, hδ, hδsmall, hp, hn, hz⟩
  refine ⟨d, ?_, ?_⟩
  · exact fun h => hnsep₂ ((finitelySeparated_image_iff _ ρ _ _ _).mp h)
  · exact fun h => hnsep₁ ((finitelySeparated_image_iff _ ρ _ _ _).mp h)

end SigmaNonprimarity
