import SurveyStatements.P5BiTreeStabilizationTraces
import SurveyStatements.P5HaarBase

/-! The two possible orders of subsequential averaging give bounded,
separately finitely additive traces on actual dyadic rectangles. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩

def dyadicMass (P : LpHaarDyadicSetIndex) : ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarDyadicSet P)

theorem dyadicMass_nonneg (P : LpHaarDyadicSetIndex) : 0 ≤ dyadicMass P :=
  measureReal_nonneg

theorem dyadicMass_le_one (P : LpHaarDyadicSetIndex) : dyadicMass P ≤ 1 := by
  simpa only [dyadicMass, measureReal_univ_eq_one] using
    (measureReal_mono (μ := volume.restrict (Icc (0 : ℝ) 1))
      (subset_univ (lpHaarDyadicSet P)))

structure DyadicBiTrace (𝕜 : Type*) [RCLike 𝕜] (M : ℝ) where
  value : LpHaarDyadicSetIndex → LpHaarDyadicSetIndex → 𝕜
  norm_le : ∀ P Q, ‖value P Q‖ ≤ M * dyadicMass P * dyadicMass Q
  congr_left : ∀ P R Q, lpHaarDyadicSet P = lpHaarDyadicSet R → value P Q = value R Q
  congr_right : ∀ P Q R, lpHaarDyadicSet Q = lpHaarDyadicSet R → value P Q = value P R
  additive_left : ∀ P R S Q, Disjoint (lpHaarDyadicSet P) (lpHaarDyadicSet R) →
    lpHaarDyadicSet S = lpHaarDyadicSet P ∪ lpHaarDyadicSet R →
      value S Q = value P Q + value R Q
  additive_right : ∀ P Q R S, Disjoint (lpHaarDyadicSet Q) (lpHaarDyadicSet R) →
    lpHaarDyadicSet S = lpHaarDyadicSet Q ∪ lpHaarDyadicSet R →
      value P S = value P Q + value P R

theorem iterated_trace_cluster {M : ℝ} (hM : 0 ≤ M)
    (a : DyadicIndex → DyadicTrace 𝕜 M)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels) :
    ∃ b : DyadicBiTrace 𝕜 M, ∃ r : ℕ → ℕ, StrictMono r ∧
      ∀ P Q, Tendsto (fun n => lpHaarLevelTrace
        (fun l k => (a ⟨l, k⟩).value P) (levels (r n)) (lpHaarDyadicSet Q))
          atTop (𝓝 (b.value P Q)) := by
  let d (P : LpHaarDyadicSetIndex) (n : ℕ) (k : Fin (2 ^ n)) := (a ⟨n, k⟩).value P
  have hd (P : LpHaarDyadicSetIndex) (n : ℕ) (k : Fin (2 ^ n)) : ‖d P n k‖ ≤ M := by
    exact ((a ⟨n, k⟩).norm_le P).trans (by
      change M * dyadicMass P ≤ M
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (dyadicMass_le_one P) hM)
  obtain ⟨b, r, hr, hlim⟩ := countable_trace_cluster d hM hd levels hlevels
  have hb (P Q : LpHaarDyadicSetIndex) :
      ‖(b P).value Q‖ ≤ M * dyadicMass P * dyadicMass Q := by
    apply le_of_tendsto (hlim P Q).norm
    apply Eventually.of_forall
    intro n
    exact lpHaarLevelTrace_norm_le (d P)
      (mul_nonneg hM (dyadicMass_nonneg P))
      (fun l k => (a ⟨l, k⟩).norm_le P) (levels (r n)) _
      (lpHaarDyadicSet_measurable Q)
  have heq (P R Q : LpHaarDyadicSetIndex)
      (hPR : lpHaarDyadicSet P = lpHaarDyadicSet R) :
      (b P).value Q = (b R).value Q := by
    apply tendsto_nhds_unique (hlim P Q)
    convert hlim R Q using 1
    funext n
    unfold lpHaarLevelTrace
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [d]
    rw [(a ⟨levels (r n), k⟩).congr P R hPR]
  have hadd (P R S Q : LpHaarDyadicSetIndex)
      (hdis : Disjoint (lpHaarDyadicSet P) (lpHaarDyadicSet R))
      (hunion : lpHaarDyadicSet S = lpHaarDyadicSet P ∪ lpHaarDyadicSet R) :
      (b S).value Q = (b P).value Q + (b R).value Q := by
    apply tendsto_nhds_unique (hlim S Q)
    convert (hlim P Q).add (hlim R Q) using 1
    funext n
    unfold lpHaarLevelTrace
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [d]
    rw [(a ⟨levels (r n), k⟩).additive P R S hdis hunion]
    ring
  refine ⟨⟨fun P Q => (b P).value Q, hb, heq,
    fun P => (b P).congr, hadd, fun P => (b P).additive⟩, r, hr, ?_⟩
  exact hlim

def DyadicBiTrace.flip {M : ℝ} (a : DyadicBiTrace 𝕜 M) : DyadicBiTrace 𝕜 M where
  value P Q := a.value Q P
  norm_le P Q := by
    have h := a.norm_le Q P
    convert h using 1 <;> ring
  congr_left P R Q := a.congr_right Q P R
  congr_right P Q R := a.congr_left Q R P
  additive_left P R S Q := a.additive_right Q P R S
  additive_right P Q R S := a.additive_left Q R S P

def DyadicBiTrace.leftSlice {M : ℝ} (hM : 0 ≤ M) (a : DyadicBiTrace 𝕜 M)
    (Q : LpHaarDyadicSetIndex) : DyadicTrace 𝕜 M where
  value P := a.value P Q
  norm_le P := (a.norm_le P Q).trans (by
    change M * dyadicMass P * dyadicMass Q ≤ M * dyadicMass P
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (dyadicMass_le_one Q)
      (mul_nonneg hM (dyadicMass_nonneg P)))
  congr P R := a.congr_left P R Q
  additive P R S := a.additive_left P R S Q

def DyadicBiTrace.rightSlice {M : ℝ} (hM : 0 ≤ M) (a : DyadicBiTrace 𝕜 M)
    (P : LpHaarDyadicSetIndex) : DyadicTrace 𝕜 M :=
  a.flip.leftSlice hM P

end SurveyStatements.P5.BiTree
