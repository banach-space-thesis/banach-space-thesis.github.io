import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! Countable threshold formulas for limits, used in PEMS Lemma 4.3.
The unbuffered formula `{f > c} = ⋃ N, ⋂ n ≥ N, {f_n > c}` is false at
points where f=c. A rational intermediate threshold supplies the needed buffer.
The pointwise and almost-everywhere forms below make that repair explicit. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace ThesisCommon

/-- A limit is strictly above c exactly when the sequence is eventually above
some rational threshold strictly above c. -/
theorem lt_limit_iff_exists_rat_eventually {u : ℕ → ℝ} {a c : ℝ}
    (hu : Tendsto u atTop (𝓝 a)) :
    c < a ↔ ∃ q : ℚ, c < (q : ℝ) ∧ ∀ᶠ n in atTop, (q : ℝ) < u n := by
  constructor
  · intro hca
    obtain ⟨q, hcq, hqa⟩ := exists_rat_btwn hca
    exact ⟨q, hcq, hu.eventually_const_lt hqa⟩
  · rintro ⟨q, hcq, hq⟩
    exact hcq.trans_le (ge_of_tendsto hu (hq.mono fun _ h => le_of_lt h))

/-- Correct countable superlevel-set formula for a pointwise limit. The
additional union over rational q>c is essential, including at boundary points. -/
theorem superlevel_eq_iUnion_iInter_of_tendsto {X : Type*}
    (f : ℕ → X → ℝ) (g : X → ℝ) (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (c : ℝ) :
    {x | c < g x} = ⋃ (q : ℚ) (_ : c < (q : ℝ)) (N : ℕ),
      ⋂ (n : ℕ) (_ : N ≤ n), {x | (q : ℝ) < f n x} := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
  rw [lt_limit_iff_exists_rat_eventually (hlim x)]
  simp only [eventually_atTop]
  aesop

/-- The same formula modulo null sets, as required for transport in a measure
algebra. A single null set suffices; no uniform pointwise convergence is assumed. -/
theorem superlevel_ae_eq_iUnion_iInter_of_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (c : ℝ) :
    {x | c < g x} =ᵐ[μ] (⋃ (q : ℚ) (_ : c < (q : ℝ)) (N : ℕ),
      ⋂ (n : ℕ) (_ : N ≤ n), {x | (q : ℝ) < f n x}) := by
  filter_upwards [hlim] with x hx
  apply propext
  change (c < g x) ↔ x ∈ (⋃ (q : ℚ) (_ : c < (q : ℝ)) (N : ℕ),
    ⋂ (n : ℕ) (_ : N ≤ n), {x | (q : ℝ) < f n x})
  simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
  rw [lt_limit_iff_exists_rat_eventually hx]
  simp only [eventually_atTop]
  aesop

end ThesisCommon
