import PEMS.DisjointOutputWitness
import PEMS.ExtremalCutoffNorm

/-! On a finite output space the disjoint witness limit is exactly the
localized noncompactness value, by the small-cut upper estimate. -/
noncomputable section
open MeasureTheory Set Filter Topology Function ThesisCommon
namespace PEMS
variable {𝕜 X Y : Type*} [RCLike 𝕜] [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

theorem exists_disjointOutputWitness_extremal
    (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) (hc : 0 < localizedWeakNoncompactness T) :
    ∃ f : ℕ → LOne 𝕜 μ, ∃ A : ℕ → Set Y, ∃ hA : ∀ n, MeasurableSet (A n),
      (∀ n, ‖f n‖ = 1) ∧ Pairwise (Disjoint on A) ∧
      Tendsto (fun n => ‖lpCut (A n) (hA n) (T (f n))‖) atTop
        (𝓝 (localizedWeakNoncompactness T)) := by
  obtain ⟨f, A, hA, l, hf, _, hd, hl, hconv⟩ := exists_disjointOutputWitness_limit T hc
    (fun _ hΘ hfin => localizedWeakNoncompactness_le_alphaTheta T hΘ hfin)
  have hmass := measure_disjoint_sequence_tendsto_zero A hA hd (μ := ν)
  have hl' := cutoff_norm_limit_le_alphaTheta_univ T f (fun n => (hf n).le) A hA hmass hconv
  rw [← localizedWeakNoncompactness_eq_alphaTheta_univ] at hl'
  have heq : l = localizedWeakNoncompactness T := le_antisymm hl' hl
  exact ⟨f, A, hA, hf, hd, heq ▸ hconv⟩

end PEMS
