import Sigma.ComplexNonseparatedSelection
import Sigma.ComplexMeasureSeparation

/-! The complex three-level selection with the precise two-algebra charge
invariants used in the simultaneous recursion. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

def ComplexThreeLevelChoice.PairedNonseparated {μ : ℕ → lp (fun _ : Point => ℂ) 1}
    {C : Set ℕ} (d : ComplexThreeLevelChoice μ C) (ρ : ℕ → ComplexPairedMeasure)
    (B Btilde : BooleanSubalgebra (Set ℕ)) : Prop :=
  (¬ ComplexPairedSeparated B Btilde (ρ '' d.J₂) (ρ '' (d.J₁ \ d.J₂))) ∧
  (¬ ComplexPairedSeparated B Btilde (ρ '' d.J₁) (ρ '' (d.J₀ \ d.J₁)))

theorem complex_exists_threeLevelChoice_pairedNonseparated (C : Set ℕ) (hC : C.Infinite)
    (μ : ℕ → lp (fun _ : Point => ℂ) 1) (hμ : ComplexAdmissible μ)
    (ρ : ℕ → ComplexPairedMeasure) (B Btilde : BooleanSubalgebra (Set ℕ))
    (hB : #B < 𝔠) (hBtilde : #Btilde < 𝔠) :
    ∃ d : ComplexThreeLevelChoice μ C, d.PairedNonseparated ρ B Btilde := by
  let ev : ℕ → B ⊕ Btilde → ℂ := fun n t => ρ n (pairedTest B Btilde t)
  have hbound (n : ℕ) (t : B ⊕ Btilde) : ‖ev n t‖ ≤ 1 := (ρ n).norm_apply_le_one _
  have hI : #(B ⊕ Btilde) < 𝔠 := by
    simpa using Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum hB hBtilde
  obtain ⟨d,hd⟩ := complex_exists_threeLevelChoice_nonseparated C hC μ hμ ev hbound hI
  refine ⟨d,?_,?_⟩
  · intro h
    exact hd.1 ((complexFinitelySeparated_image_iff
      (fun (q : ComplexPairedMeasure) t => q (pairedTest B Btilde t))
      ρ Set.univ d.J₂ (d.J₁ \ d.J₂)).mp h)
  · intro h
    exact hd.2 ((complexFinitelySeparated_image_iff
      (fun (q : ComplexPairedMeasure) t => q (pairedTest B Btilde t))
      ρ Set.univ d.J₁ (d.J₀ \ d.J₁)).mp h)

end SigmaNonprimarity
