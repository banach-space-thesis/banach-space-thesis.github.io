import ThesisCommon.Analysis.LpHaarLevelTraces
import ThesisCommon.Analysis.LpHaarDiagonalBounds

/-! The common subsequential trace limit is actually finitely additive
on dyadic sets and does not depend on their finite-level representation.
Every bounded interval-Lp operator supplies such a trace from its diagonal. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpHaar_trace_limit_finitely_additive
    (d : ∀ n, Fin (2 ^ n) → 𝕜) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ n k, ‖d n k‖ ≤ M) :
    ∃ a : LpHaarDyadicSetIndex → 𝕜, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ i, ‖a i‖ ≤ M * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i)) ∧
      (∀ i, Tendsto (fun n => lpHaarLevelTrace d (r n) (lpHaarDyadicSet i)) atTop (𝓝 (a i))) ∧
      (∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j) ∧
      ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
        lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j := by
  obtain ⟨a, r, hr, hbound, ha⟩ := lpHaarLevelTrace_cluster d hM hd
  refine ⟨a, r, hr, hbound, ha, ?_, ?_⟩
  · intro i j hij
    apply tendsto_nhds_unique (ha i)
    simpa only [hij] using ha j
  · intro i j k hdis hunion
    apply tendsto_nhds_unique (ha k)
    convert (ha i).add (ha j) using 1
    funext n
    rw [hunion, lpHaarLevelTrace_union d (r n) _ _
      (lpHaarDyadicSet_measurable i) (lpHaarDyadicSet_measurable j) hdis]

theorem lpHaar_operator_diagonal_trace_limit
    (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
    (T : IntervalLp 𝕜 p →L[𝕜] IntervalLp 𝕜 p) :
    ∃ a : LpHaarDyadicSetIndex → 𝕜, ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ i, ‖a i‖ ≤ (6 * ‖T‖) * (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i)) ∧
      (∀ i, Tendsto (fun n => lpHaarLevelTrace
        (fun l k => lpHaarDyadicCoefficient 𝕜 p l k (T (lpHaarDyadic 𝕜 p l k)))
          (r n) (lpHaarDyadicSet i)) atTop (𝓝 (a i))) ∧
      (∀ i j, lpHaarDyadicSet i = lpHaarDyadicSet j → a i = a j) ∧
      ∀ i j k, Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j) →
        lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j → a k = a i + a j := by
  exact lpHaar_trace_limit_finitely_additive _ (mul_nonneg (by norm_num) (norm_nonneg T))
    (lpHaar_operator_diagonal_norm_le 𝕜 p hp T)

end ThesisCommon
