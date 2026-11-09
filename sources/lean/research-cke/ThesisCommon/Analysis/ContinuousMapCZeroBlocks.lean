import ThesisCommon.Analysis.CZeroColumnOperators
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Disjoint continuous-function blocks assemble into a genuine bounded
map from c0. The finite supremum estimate, rather than a sum of norms,
ensures uniform convergence for every null input sequence. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem continuousMap_disjoint_finiteColumnBound (F : ℕ → X →L[𝕜] C(K, 𝕜))
    (hF : ∀ n, ‖F n‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ (x y : X) t, F i x t = 0 ∨ F j y t = 0) :
    CZeroFiniteColumnBound F 1 := by
  classical
  intro s x b hb hx
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ hb).2
  intro t
  change ‖(ContinuousMap.evalCLM 𝕜 t) (∑ i ∈ s, F i (x i))‖ ≤ b
  rw [map_sum]
  change ‖∑ i ∈ s, F i (x i) t‖ ≤ b
  by_cases h : ∃ i ∈ s, F i (x i) t ≠ 0
  · obtain ⟨i, hi, hne⟩ := h
    rw [Finset.sum_eq_single_of_mem i hi]
    · exact ((F i (x i)).norm_coe_le_norm t).trans
        (((F i).le_opNorm _).trans (by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg (x i))).trans (by simpa using hx i hi)))
    · intro j hj hji
      exact (hdis i j hji.symm (x i) (x j) t).resolve_left hne
  · have hz : ∀ i ∈ s, F i (x i) t = 0 := by simpa using h
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact hb

def continuousMapCZeroInsert (F : ℕ → X →L[𝕜] C(K, 𝕜))
    (hF : ∀ n, ‖F n‖ ≤ 1)
    (hdis : ∀ i j, i ≠ j → ∀ (x y : X) t, F i x t = 0 ∨ F j y t = 0) :
    CZeroSum X →L[𝕜] C(K, 𝕜) :=
  cZeroColumns F 1 zero_le_one (continuousMap_disjoint_finiteColumnBound F hF hdis)

theorem norm_continuousMapCZeroInsert_le (F : ℕ → X →L[𝕜] C(K, 𝕜)) (hF hdis) :
    ‖continuousMapCZeroInsert F hF hdis‖ ≤ 1 := norm_cZeroColumns_le ..

theorem continuousMapCZeroInsert_single (F : ℕ → X →L[𝕜] C(K, 𝕜)) (hF hdis) (n : ℕ) (x : X) :
    continuousMapCZeroInsert F hF hdis (cZeroSingle n x) = F n x := cZeroColumns_single ..

end ThesisCommon
