import ThesisCommon.Analysis.SelfSimilarSmallBlocks
import ThesisCommon.Analysis.CotypeUpperSelection

/-! LPCK Lemma 3.8: one c0 input coordinate and an infinite output set
with small restriction. The input coordinate may be chosen beyond any bound.
The finite sign averaging proof is shared with the UPFP manuscript. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem cZero_to_lp_forward_coordinate (hp : p ≠ ∞)
    (T : CZeroSum X →L[𝕜] lp (fun _ : ℕ => Y) p)
    (b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : ℕ ↪ ℕ), b < n ∧ ‖((lpRestrict p a).comp T).comp (cZeroSingleCLM n)‖ < ε := by
  have hp1 := finite_exponent_toReal_ge_one p hp
  obtain ⟨N, hN⟩ := exists_cotype_power_threshold (q := p.toReal) (C := 1) (M := ‖T‖) hε
  simp only [Real.one_rpow, one_mul] at hN
  let e : Fin N ↪ ℕ := Fin.valEmbedding.trans (coordinateTail (Function.Embedding.refl ℕ) b)
  obtain ⟨i, hi⟩ := lp_exists_small_restricted_block p hp1
    (fun i : Fin N => cZeroSingleCLM (𝕜 := 𝕜) (X := X) (e i))
    (fun x hx θ => cZero_single_embedding_sign_bound e x hx θ)
    T hε (norm_nonneg T) le_rfl hN
  refine ⟨e i, disjointCoordinateEmbedding i, ?_, hi⟩
  change b < b+1+i.val
  omega

end ThesisCommon
