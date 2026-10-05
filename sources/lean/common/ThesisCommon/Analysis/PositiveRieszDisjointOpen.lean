import ThesisCommon.Analysis.PositiveDualCluster
import ThesisCommon.Analysis.PositiveRieszOrder
import ThesisCommon.Analysis.RegularMeasureDisjointOpen

/-! Quantitative open selection for actual bounded positive functionals.
Banach--Alaoglu supplies the recurrent measure needed by the construction,
so the conclusion requires no regularity or compactness witness as input. -/
noncomputable section
open Set MeasureTheory Topology Filter
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem exists_disjoint_open_of_positiveRiesz_mass
    (φ : ℕ → C(K, ℝ) →L[ℝ] ℝ) (hφ : ∀ n, 0 ≤ φ n)
    {C : ℝ} (hC : ∀ n, ‖φ n‖ ≤ C)
    (A : ℕ → Set K) (hA : ∀ n, MeasurableSet (A n))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {c ε : ℝ}
    (hmass : ∀ n, c < (positiveContinuousMapRiesz (φ n) (hφ n)).real (A n))
    (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ U : ℕ → Set K,
      (∀ n, IsOpen (U n)) ∧ Pairwise (fun i j => Disjoint (U i) (U j)) ∧
        ∀ n, c - ε < (positiveContinuousMapRiesz (φ (k n)) (hφ (k n))).real (U n) := by
  obtain ⟨ψ, hψ, _, hrec⟩ := exists_positive_continuousMapDual_cluster φ hφ hC
  apply exists_disjoint_open_of_recurrent_regularMeasure
    (fun n => positiveContinuousMapRiesz (φ n) (hφ n))
    (positiveContinuousMapRiesz ψ hψ) ?_ A hA hAd hmass hε
  simpa only [integral_positiveContinuousMapRiesz] using hrec

end ThesisCommon
