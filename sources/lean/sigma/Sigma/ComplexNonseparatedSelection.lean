import Sigma.ComplexThreeLevelSelection
import Sigma.ComplexSeparation

/-! A single complex selection supplies both three-level bounds and both
nonseparation requirements. The test set may include both Boolean algebras
of the crossed construction, provided its cardinality is below continuum. -/
noncomputable section
open Set Cardinal
namespace SigmaNonprimarity

structure ComplexThreeLevelChoice (μ : ℕ → lp (fun _ : Point => ℂ) 1) (C : Set ℕ) where
  J₀ : Set ℕ
  J₁ : Set ℕ
  J₂ : Set ℕ
  Z : Set Point
  a : ℂ
  delta : ℝ
  J₂_subset : J₂ ⊆ J₁
  J₁_subset : J₁ ⊆ J₀
  J₀_subset : J₀ ⊆ C
  infinite_J₂ : J₂.Infinite
  infinite_middle : (J₁ \ J₂).Infinite
  infinite_outer : (J₀ \ J₁).Infinite
  splits : Splits J₁ Z
  lower_a : (⨅ n, ‖μ n (n,false)‖) ≤ ‖a‖
  delta_pos : 0 < delta
  delta_small : delta < (⨅ n, ‖μ n (n,false)‖) / 11
  positive_level : ∀ n ∈ J₂,
    ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z) - 2*a‖ < 3*delta
  negative_level : ∀ n ∈ J₁ \ J₂,
    ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z) + 2*a‖ < 3*delta
  zero_level : ∀ n ∈ J₀ \ J₁,
    ‖complexMass (μ n) Z - complexMass (μ n) (cylinder J₁ \ Z)‖ < 3*delta

def ComplexThreeLevelChoice.Nonseparated {μ : ℕ → lp (fun _ : Point => ℂ) 1} {C : Set ℕ}
    (d : ComplexThreeLevelChoice μ C) {I : Type} (ev : ℕ → I → ℂ) : Prop :=
  (¬ ComplexFinitelySeparated ev Set.univ d.J₂ (d.J₁ \ d.J₂)) ∧
  (¬ ComplexFinitelySeparated ev Set.univ d.J₁ (d.J₀ \ d.J₁))

theorem complex_exists_threeLevelChoice_nonseparated (C : Set ℕ) (hC : C.Infinite)
    (μ : ℕ → lp (fun _ : Point => ℂ) 1) (hμ : ComplexAdmissible μ)
    {I : Type} (ev : ℕ → I → ℂ) (hbound : ∀ n i, ‖ev n i‖ ≤ 1) (hI : #I < 𝔠) :
    ∃ d : ComplexThreeLevelChoice μ C, d.Nonseparated ev := by
  obtain ⟨J₀,H,a,δ,hHJ₀,hJ₀C,hH,hJ₀H,ha,hδ,hδsmall,hsmall,happ⟩ :=
    complex_three_level_selection_control C μ hC hμ
  obtain ⟨J₁,hJ₁H,hJ₁,_,hnsep₁⟩ :=
    complex_exists_infinite_nonseparated_cut ev hbound hI J₀ H hHJ₀ hH
  obtain ⟨J₂,hJ₂J₁,hJ₂,hmiddle,hnsep₂⟩ :=
    complex_exists_infinite_nonseparated_cut ev hbound hI J₁ J₁ Set.Subset.rfl hJ₁
  have houter : (J₀ \ J₁).Infinite :=
    hJ₀H.mono (fun _ hx => ⟨hx.1,fun h => hx.2 (hJ₁H h)⟩)
  obtain ⟨hp,hn,hz⟩ := complex_three_level_bounds_of_control μ hμ.2.1 J₀ H hHJ₀ a δ hδ
    hsmall happ J₁ J₂ hJ₁H hJ₂J₁
  let d : ComplexThreeLevelChoice μ C :=
    ⟨J₀,J₁,J₂,graphSplitter J₁ (complexLevelChoice J₂),a,δ,
      hJ₂J₁,hJ₁H.trans hHJ₀,hJ₀C,hJ₂,hmiddle,houter,
      graphSplitter_splits _ _,ha,hδ,hδsmall,hp,hn,hz⟩
  exact ⟨d,hnsep₂,hnsep₁⟩

end SigmaNonprimarity
