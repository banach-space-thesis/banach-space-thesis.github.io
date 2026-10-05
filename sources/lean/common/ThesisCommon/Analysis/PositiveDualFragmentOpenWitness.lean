import ThesisCommon.Analysis.PositiveRieszDisjointOpen
import ThesisCommon.Analysis.PositiveRieszDisjoint
import ThesisCommon.Analysis.MutuallySingularSequenceSupports

/-! Disjoint positive fragments of bounded dual elements produce sharp
disjoint open mass witnesses. The measurable supports, cluster measure,
and open neighborhoods are all constructed. -/
noncomputable section
open Set MeasureTheory
open scoped ThesisCommon.PositiveOperatorOrder ThesisCommon.DualLattice
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

theorem exists_disjoint_open_of_positive_dual_fragments
    (φ ψ : ℕ → C(K, ℝ) →L[ℝ] ℝ) (hφ : ∀ n, 0 ≤ φ n) (hψ : ∀ n, 0 ≤ ψ n)
    (hle : ∀ n, ψ n ≤ φ n) (hd : Pairwise fun i j => ψ i ⊓ ψ j = 0)
    {C : ℝ} (hC : ∀ n, ‖φ n‖ ≤ C) {c ε : ℝ}
    (hc : ∀ n, c < ‖ψ n‖) (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ U : ℕ → Set K,
      (∀ n, IsOpen (U n)) ∧ Pairwise (fun i j => Disjoint (U i) (U j)) ∧
        ∀ n, c - ε < (positiveContinuousMapRiesz (φ (k n)) (hφ (k n))).real (U n) := by
  obtain ⟨A, hA, hAd, hAc, _⟩ :=
    exists_disjoint_measurable_supports_of_pairwise_mutuallySingular
      (fun n => positiveContinuousMapRiesz (ψ n) (hψ n))
      (fun i j hij => (positiveContinuousMapRiesz_mutuallySingular_iff _ _
        (hψ i) (hψ j)).mpr (hd hij))
  apply exists_disjoint_open_of_positiveRiesz_mass φ hφ hC A hA hAd ?_ hε
  intro n
  have hfull : positiveContinuousMapRiesz (ψ n) (hψ n) (A n) =
      positiveContinuousMapRiesz (ψ n) (hψ n) univ := by
    have h := measure_add_measure_compl (μ := positiveContinuousMapRiesz (ψ n) (hψ n)) (hA n)
    simpa only [hAc n, add_zero] using h
  have hnorm : (positiveContinuousMapRiesz (ψ n) (hψ n)).real (A n) = ‖ψ n‖ := by
    rw [measureReal_def, hfull]
    exact positiveContinuousMapRiesz_mass_norm (ψ n) (hψ n)
  have hc' := hc n
  rw [← hnorm] at hc'
  exact hc'.trans_le (ENNReal.toReal_mono (by finiteness)
    (((positiveContinuousMapRiesz_le_iff _ _ (hψ n) (hφ n)).mpr (hle n)) (A n)))

end ThesisCommon
