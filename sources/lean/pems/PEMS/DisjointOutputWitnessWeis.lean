import PEMS.DisjointOutputWitness
import PEMS.RealStrictlyLocalizableWeis
import PEMS.ComplexStrictlyLocalizableWeis

/-! Source Lemma 5.1 over both real and complex scalars. The numerical input
to the disjoint construction is discharged by the proved main theorem.
The stronger auxiliary statements need strict localizability only on the
input; the numbered statement retains both source hypotheses. -/
noncomputable section
open MeasureTheory Set Filter Topology Function ThesisCommon
namespace PEMS
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

def Lemma_5_1 {𝕜 : Type*} [RCLike 𝕜] (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) : Prop :=
  StrictlyLocalizable μ → StrictlyLocalizable ν → ¬IsWeaklyCompactOperator T →
    ∃ f : ℕ → LOne 𝕜 μ, ∃ A : ℕ → Set Y,
      ∃ hA : ∀ n, MeasurableSet (A n), ∃ l : ℝ,
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (A n) < ⊤) ∧ Pairwise (Disjoint on A) ∧
      weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 l)

theorem exists_real_disjointOutputWitness_weakEssentialNorm
    (hμ : StrictlyLocalizable μ) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν)
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ f : ℕ → LOne ℝ μ, ∃ A : ℕ → Set Y,
      ∃ hA : ∀ n, MeasurableSet (A n), ∃ l : ℝ,
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (A n) < ⊤) ∧ Pairwise (Disjoint on A) ∧
      weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 l) := by
  apply exists_disjointOutputWitness_limit T
  · exact lt_of_le_of_ne (weakEssentialNorm_nonneg T)
      (Ne.symm fun heq => hT ((weakEssentialNorm_eq_zero_iff T).mp heq))
  · intro Θ hΘ hfin
    rw [weakEssentialNorm_eq_localized_real_strictlyLocalizable hμ T]
    exact localizedWeakNoncompactness_le_alphaTheta T hΘ hfin

theorem exists_complex_disjointOutputWitness_weakEssentialNorm
    (hμ : StrictlyLocalizable μ) (T : LOne ℂ μ →L[ℂ] LOne ℂ ν)
    (hT : ¬IsWeaklyCompactOperator T) :
    ∃ f : ℕ → LOne ℂ μ, ∃ A : ℕ → Set Y,
      ∃ hA : ∀ n, MeasurableSet (A n), ∃ l : ℝ,
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, ν (A n) < ⊤) ∧ Pairwise (Disjoint on A) ∧
      weakEssentialNorm T ≤ l ∧
      Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop (𝓝 l) := by
  apply exists_disjointOutputWitness_limit T
  · exact lt_of_le_of_ne (weakEssentialNorm_nonneg T)
      (Ne.symm fun heq => hT ((weakEssentialNorm_eq_zero_iff T).mp heq))
  · intro Θ hΘ hfin
    rw [weakEssentialNorm_eq_localized_complex_strictlyLocalizable hμ T]
    exact localizedWeakNoncompactness_le_alphaTheta T hΘ hfin

theorem lemma_5_1_real (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) : Lemma_5_1 T := by
  intro hμ _ hT
  exact exists_real_disjointOutputWitness_weakEssentialNorm hμ T hT

theorem lemma_5_1_complex (T : LOne ℂ μ →L[ℂ] LOne ℂ ν) : Lemma_5_1 T := by
  intro hμ _ hT
  exact exists_complex_disjointOutputWitness_weakEssentialNorm hμ T hT

end PEMS
