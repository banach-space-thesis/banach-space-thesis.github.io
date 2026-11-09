import SurveyStatements.P5BiTreeStabilizationAverages

/-! Normalized block slice means converge to the actual slice traces and
the two iterated rectangle traces. These limits supply the finite level
constraints used in the signed-tree recursion. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def levelMean (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ)
    (P : LpHaarFiniteParent) : 𝕜 :=
  lpHaarLevelTrace d n P.set /
    ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜)

def rectangleMean {M : ℝ} (a : DyadicBiTrace 𝕜 M)
    (P Q : LpHaarFiniteParent) : 𝕜 :=
  a.value P.index Q.index /
    (((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜) *
      ((volume.restrict (Icc (0 : ℝ) 1)).real Q.set : 𝕜))

theorem splitDiagonal_eq_levelMean
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (S : LpHaarFiniteSplit) :
    lpHaarSplitDiagonal d S = levelMean d S.level S.parent :=
  lpHaarSplitDiagonal_trace d S

theorem finiteAverage_tendsto {ι : Type*} (S : Finset ι)
    (f : ℕ → ι → 𝕜) (a : ι → 𝕜)
    (hf : ∀ i ∈ S, Tendsto (fun n => f n i) atTop (𝓝 (a i))) :
    Tendsto (fun n => finiteAverage S (f n)) atTop (𝓝 (finiteAverage S a)) := by
  exact (tendsto_finset_sum S hf).const_mul (S.card : 𝕜)⁻¹

theorem levelTrace_finiteAverage {ι : Type*} (S : Finset ι)
    (d : ι → (n : ℕ) → Fin (2 ^ n) → 𝕜) (n : ℕ) (P : Set ℝ) :
    lpHaarLevelTrace (fun l k => finiteAverage S (fun i => d i l k)) n P =
      finiteAverage S (fun i => lpHaarLevelTrace (d i) n P) := by
  let w (k : Fin (2 ^ n)) : 𝕜 :=
    ((volume.restrict (Icc (0 : ℝ) 1)).real (P ∩ lpHaarCell n k) : 𝕜)
  change (∑ k : Fin (2 ^ n), w k * ((S.card : 𝕜)⁻¹ * ∑ i ∈ S, d i n k)) =
    (S.card : 𝕜)⁻¹ * ∑ i ∈ S, ∑ k : Fin (2 ^ n), w k * d i n k
  calc
    _ = ∑ k : Fin (2 ^ n), (S.card : 𝕜)⁻¹ * ∑ i ∈ S, w k * d i n k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
      ring
    _ = (S.card : 𝕜)⁻¹ * ∑ k : Fin (2 ^ n), ∑ i ∈ S, w k * d i n k :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [Finset.sum_comm]

theorem levelMean_limit
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (a : LpHaarDyadicSetIndex → 𝕜)
    (levels : ℕ → ℕ)
    (hlim : ∀ P, Tendsto (fun n => lpHaarLevelTrace d (levels n) (lpHaarDyadicSet P))
      atTop (𝓝 (a P))) (P : LpHaarFiniteParent) :
    Tendsto (fun n => levelMean d (levels n) P) atTop
      (𝓝 (lpHaarParentTrace a P)) :=
  (hlim P.index).div_const _

theorem levelMean_eventually_close
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (a : LpHaarDyadicSetIndex → 𝕜)
    (levels : ℕ → ℕ)
    (hlim : ∀ P, Tendsto (fun n => lpHaarLevelTrace d (levels n) (lpHaarDyadicSet P))
      atTop (𝓝 (a P))) (P : LpHaarFiniteParent) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖levelMean d (levels n) P - lpHaarParentTrace a P‖ < ε := by
  have h : Tendsto (fun n => ‖levelMean d (levels n) P - lpHaarParentTrace a P‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((levelMean_limit d a levels hlim P).sub
        (tendsto_const_nhds (x := lpHaarParentTrace a P))).norm
  exact (tendsto_order.mp h).2 ε hε

theorem IteratedTraceData.outer_block_limit
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (T : LpHaarFiniteSplit) (P : LpHaarDyadicSetIndex) :
    Tendsto (fun n => lpHaarLevelTrace
      (fun l k => finiteAverage T.atoms (fun j => d ⟨l, k⟩ ⟨T.level, j⟩))
      (H.outerLevels n) (lpHaarDyadicSet P)) atTop
      (𝓝 ((averageTraces H.outerTrace T).value P)) := by
  simp_rw [levelTrace_finiteAverage]
  exact finiteAverage_tendsto T.atoms _ _ (fun j _ => H.outerLimit ⟨T.level, j⟩ P)

theorem IteratedTraceData.inner_block_limit
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (S : LpHaarFiniteSplit) (Q : LpHaarDyadicSetIndex) :
    Tendsto (fun n => lpHaarLevelTrace
      (fun l k => finiteAverage S.atoms (fun i => d ⟨S.level, i⟩ ⟨l, k⟩))
      (H.innerLevels n) (lpHaarDyadicSet Q)) atTop
      (𝓝 ((averageTraces H.innerTrace S).value Q)) := by
  simp_rw [levelTrace_finiteAverage]
  exact finiteAverage_tendsto S.atoms _ _ (fun i _ => H.innerLimit ⟨S.level, i⟩ Q)

theorem IteratedTraceData.lower_rectangle_limit
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (P Q : LpHaarFiniteParent) :
    Tendsto (fun n => levelMean
      (fun l k => (H.outerTrace ⟨l, k⟩).value P.index)
      (H.innerLevels n) Q /
        ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜))
      atTop (𝓝 (rectangleMean H.lowerTrace P Q)) := by
  have h := ((H.lowerLimit P.index Q.index).div_const
    ((volume.restrict (Icc (0 : ℝ) 1)).real Q.set : 𝕜)).div_const
      ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜)
  convert h using 1
  simp only [rectangleMean, div_div, mul_comm]

theorem IteratedTraceData.upper_rectangle_limit
    (d : DyadicIndex → DyadicIndex → 𝕜) {M : ℝ} (H : IteratedTraceData d M)
    (P Q : LpHaarFiniteParent) :
    Tendsto (fun n => levelMean
      (fun l k => (H.innerTrace ⟨l, k⟩).value Q.index)
      (H.outerLevels n) P /
        ((volume.restrict (Icc (0 : ℝ) 1)).real Q.set : 𝕜))
      atTop (𝓝 (rectangleMean H.upperTrace P Q)) := by
  have h := ((H.upperLimit P.index Q.index).div_const
    ((volume.restrict (Icc (0 : ℝ) 1)).real P.set : 𝕜)).div_const
      ((volume.restrict (Icc (0 : ℝ) 1)).real Q.set : 𝕜)
  convert h using 1
  simp only [rectangleMean, div_div]

end SurveyStatements.P5.BiTree
