import JFA.TensorNormChecks
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-! A countable norming family of dual vectors for each separable normed space.
The construction uses Hahn--Banach on a dense sequence. It also covers the
zero space, and does not assume separability of the whole dual. -/

noncomputable section
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparableSpace E]

def normingSequence : ℕ → E →L[𝕜] 𝕜 :=
  fun n => Classical.choose (exists_dual_vector'' 𝕜 (denseSeq E n))

theorem norm_normingSequence_le (n : ℕ) :
    ‖normingSequence (𝕜 := 𝕜) (E := E) n‖ ≤ 1 :=
  (Classical.choose_spec (exists_dual_vector'' 𝕜 (denseSeq E n))).1

theorem normingSequence_denseSeq (n : ℕ) :
    normingSequence (𝕜 := 𝕜) (E := E) n (denseSeq E n) = (‖denseSeq E n‖ : 𝕜) :=
  (Classical.choose_spec (exists_dual_vector'' 𝕜 (denseSeq E n))).2

theorem norm_le_of_normingSequence_le (x : E) {c : ℝ}
    (h : ∀ n, ‖normingSequence (𝕜 := 𝕜) n x‖ ≤ c) : ‖x‖ ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := (denseRange_denseSeq E).exists_dist_lt x (half_pos hε)
  have hdist : ‖denseSeq E n - x‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn
  have hbound : ‖normingSequence (𝕜 := 𝕜) n (denseSeq E n - x)‖ ≤
      ‖denseSeq E n - x‖ := by
    exact ((normingSequence (𝕜 := 𝕜) n).le_opNorm _).trans
      (by simpa using (mul_le_mul_of_nonneg_right
        (norm_normingSequence_le (𝕜 := 𝕜) (E := E) n) (norm_nonneg (denseSeq E n - x))))
  have hnorm : ‖denseSeq E n‖ ≤ ‖denseSeq E n - x‖ + c := by
    calc
      ‖denseSeq E n‖ = ‖normingSequence (𝕜 := 𝕜) n (denseSeq E n)‖ := by
        rw [normingSequence_denseSeq, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      _ = ‖normingSequence (𝕜 := 𝕜) n (denseSeq E n - x) +
          normingSequence (𝕜 := 𝕜) n x‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖normingSequence (𝕜 := 𝕜) n (denseSeq E n - x)‖ +
          ‖normingSequence (𝕜 := 𝕜) n x‖ := norm_add_le _ _
      _ ≤ ‖denseSeq E n - x‖ + c := add_le_add hbound (h n)
  have htriangle : ‖x‖ ≤ ‖denseSeq E n‖ + ‖denseSeq E n - x‖ := by
    simpa only [norm_sub_rev] using norm_le_insert' x (denseSeq E n)
  linarith

theorem eq_zero_of_normingSequence_zero (x : E)
    (h : ∀ n, normingSequence (𝕜 := 𝕜) n x = 0) : x = 0 := by
  apply norm_le_zero_iff.mp
  exact norm_le_of_normingSequence_le (𝕜 := 𝕜) x (fun n => by rw [h n, norm_zero])

theorem eq_of_normingSequence_eq {x y : E}
    (h : ∀ n, normingSequence (𝕜 := 𝕜) n x = normingSequence (𝕜 := 𝕜) n y) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_normingSequence_zero (𝕜 := 𝕜)
  intro n
  rw [map_sub, h n, sub_self]

end JFA
