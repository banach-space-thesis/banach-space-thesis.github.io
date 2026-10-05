import JLMS.DisjointWeakNull
import JLMS.MatrixSelection

/-!
# Matrix selection preserving a convergent functional subsequence

Restrict the norming matrix along a common weak-star-convergent subsequence.
Its column limit is a functional on c₀ and therefore tends to zero; its
individual rows also tend to zero. The gliding-hump selection makes all
off-diagonal entries small and preserves the weak-star convergence of the rows.
-/

noncomputable section

open Filter Topology

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_small_convergent_norming_matrix (R : cZero 𝕜 →L[𝕜] X)
    (φ : ℕ → (X →L[𝕜] 𝕜)) (ψ : X →L[𝕜] 𝕜)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (ht : ∀ x, Tendsto (fun n => φ (r n) x) atTop (𝓝 (ψ x)))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ i j, i ≠ j → ‖φ (s i) (R (cZeroUnit 𝕜 (s j)))‖ ≤ 2 * w j) ∧
      ∀ x, Tendsto (fun n => φ (s n) x) atTop (𝓝 (ψ x)) := by
  let B (i j : ℕ) := φ (r i) (R (cZeroUnit 𝕜 (r j)))
  let b (j : ℕ) := ψ (R (cZeroUnit 𝕜 (r j)))
  have hrow (i : ℕ) : Tendsto (B i) atTop (𝓝 0) :=
    (weakNull_cZero_units ((φ (r i)).comp R)).comp hr.tendsto_atTop
  have hcol (j : ℕ) : Tendsto (fun i => B i j) atTop (𝓝 (b j)) := ht _
  have hb : Tendsto b atTop (𝓝 0) :=
    (weakNull_cZero_units (ψ.comp R)).comp hr.tendsto_atTop
  obtain ⟨q, hq, hoff⟩ := exists_small_offDiagonal_subsequence B b hrow hcol hb w hw
  exact ⟨r ∘ q, hr.comp hq, hoff, fun x => (ht x).comp hq.tendsto_atTop⟩

end JLMS
