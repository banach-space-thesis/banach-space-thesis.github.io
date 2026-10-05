import ThesisCommon.Analysis.CotypeOperators
import ThesisCommon.Analysis.DisjointSequenceBlocks

/-! Cotype backward reduction on the actual c₀ and ℓ∞ sequence spaces.
An infinite coordinate set is represented by its injective enumeration.
No compactness, separability or matrix determination is assumed.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Finite cotype of the target gives a small restriction to some infinite
coordinate set in ℓ∞. Proof: disjoint infinite blocks and signed unit vectors. -/
theorem HasFiniteCotype.infinity_backward_reduction (h : HasFiniteCotype X)
    (T : EllInfinitySum Y →L[𝕜] X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, ‖T.comp (lpExtend ∞ e)‖ < ε := by
  obtain ⟨q, C, h⟩ := h
  obtain ⟨n, hn⟩ := exists_cotype_power_threshold (q := q) (C := C) (M := ‖T‖) hε
  obtain ⟨i, hi⟩ := h.exists_small_block_power
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := Y) ∞ (disjointCoordinateEmbedding i))
    infinity_disjoint_blocks_sign_bound T hε (norm_nonneg T) le_rfl hn
  exact ⟨disjointCoordinateEmbedding i, hi⟩

/-- Finite cotype of the target gives the same infinite restriction in c₀. -/
theorem HasFiniteCotype.cZero_backward_reduction (h : HasFiniteCotype X)
    (T : CZeroSum Y →L[𝕜] X) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, ‖T.comp (cZeroExtend e)‖ < ε := by
  obtain ⟨q, C, h⟩ := h
  obtain ⟨n, hn⟩ := exists_cotype_power_threshold (q := q) (C := C) (M := ‖T‖) hε
  obtain ⟨i, hi⟩ := h.exists_small_block_power
    (fun i : Fin n => cZeroExtend (𝕜 := 𝕜) (X := Y) (disjointCoordinateEmbedding i))
    cZero_disjoint_blocks_sign_bound T hε (norm_nonneg T) le_rfl hn
  exact ⟨disjointCoordinateEmbedding i, hi⟩

end ThesisCommon
