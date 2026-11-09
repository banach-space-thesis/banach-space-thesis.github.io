import SurveyStatements.P5BiTreeStabilizationDefinitions
import SurveyStatements.P5BiTreeStabilizationBiTraces

/-! Exact finite block averages and the two iterated common trace limits
of an arbitrary bounded two-parameter coefficient array. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5.BiTree
open P5Support
variable {𝕜 : Type*} [RCLike 𝕜]

def finiteAverage {ι : Type*} (S : Finset ι) (f : ι → 𝕜) : 𝕜 :=
  (S.card : 𝕜)⁻¹ * ∑ k ∈ S, f k

theorem finiteAverage_norm_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → 𝕜) {M : ℝ} (hf : ∀ k ∈ S, ‖f k‖ ≤ M) :
    ‖finiteAverage S f‖ ≤ M := by
  have hc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hs : ‖∑ k ∈ S, f k‖ ≤ (S.card : ℝ) * M := by
    calc
      _ ≤ ∑ k ∈ S, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ S, M := Finset.sum_le_sum hf
      _ = _ := by simp
  rw [finiteAverage, norm_mul, norm_inv, RCLike.norm_natCast]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * ((S.card : ℝ) * M) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le)
    _ = M := by field_simp

theorem finiteAverage_add {ι : Type*} (S : Finset ι) (f g : ι → 𝕜) :
    finiteAverage S (fun k => f k + g k) = finiteAverage S f + finiteAverage S g := by
  simp only [finiteAverage, Finset.sum_add_distrib, mul_add]

def averageTraces {M : ℝ} (a : DyadicIndex → DyadicTrace 𝕜 M)
    (S : LpHaarFiniteSplit) : DyadicTrace 𝕜 M where
  value P := finiteAverage S.atoms (fun k => (a ⟨S.level, k⟩).value P)
  norm_le P := finiteAverage_norm_le S.atoms S.nonempty _
    (fun k _ => (a ⟨S.level, k⟩).norm_le P)
  congr P R hPR := by
    unfold finiteAverage
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact (a ⟨S.level, k⟩).congr P R hPR
  additive P R U hdis hunion := by
    change finiteAverage S.atoms (fun k => (a ⟨S.level, k⟩).value U) = _
    have ht (k : Fin (2 ^ S.level)) : (a ⟨S.level, k⟩).value U =
        (a ⟨S.level, k⟩).value P + (a ⟨S.level, k⟩).value R :=
      (a ⟨S.level, k⟩).additive P R U hdis hunion
    simp_rw [ht]
    exact finiteAverage_add _ _ _

theorem blockAverage_eq_average (d : DyadicIndex → DyadicIndex → 𝕜)
    (S T : LpHaarFiniteSplit) : blockAverage d S T =
      finiteAverage S.atoms (fun k =>
        finiteAverage T.atoms (fun l => d ⟨S.level, k⟩ ⟨T.level, l⟩)) := by
  unfold blockAverage finiteAverage
  rw [← Finset.mul_sum]
  ring

theorem blockAverage_norm_le (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hd : ∀ I J, ‖d I J‖ ≤ M) (S T : LpHaarFiniteSplit) :
    ‖blockAverage d S T‖ ≤ M := by
  rw [blockAverage_eq_average]
  exact finiteAverage_norm_le S.atoms S.nonempty _ (fun k _ =>
    finiteAverage_norm_le T.atoms T.nonempty _ (fun l _ => hd _ _))

structure IteratedTraceData (d : DyadicIndex → DyadicIndex → 𝕜) (M : ℝ) where
  outerTrace : DyadicIndex → DyadicTrace 𝕜 M
  innerTrace : DyadicIndex → DyadicTrace 𝕜 M
  lowerTrace : DyadicBiTrace 𝕜 M
  upperTrace : DyadicBiTrace 𝕜 M
  outerLevels : ℕ → ℕ
  innerLevels : ℕ → ℕ
  outerLevels_strict : StrictMono outerLevels
  innerLevels_strict : StrictMono innerLevels
  outerLimit : ∀ J P, Tendsto (fun n => lpHaarLevelTrace
    (fun l k => d ⟨l, k⟩ J) (outerLevels n) (lpHaarDyadicSet P))
      atTop (𝓝 ((outerTrace J).value P))
  innerLimit : ∀ I Q, Tendsto (fun n => lpHaarLevelTrace
    (fun l k => d I ⟨l, k⟩) (innerLevels n) (lpHaarDyadicSet Q))
      atTop (𝓝 ((innerTrace I).value Q))
  lowerLimit : ∀ P Q, Tendsto (fun n => lpHaarLevelTrace
    (fun l k => (outerTrace ⟨l, k⟩).value P) (innerLevels n) (lpHaarDyadicSet Q))
      atTop (𝓝 (lowerTrace.value P Q))
  upperLimit : ∀ P Q, Tendsto (fun n => lpHaarLevelTrace
    (fun l k => (innerTrace ⟨l, k⟩).value Q) (outerLevels n) (lpHaarDyadicSet P))
      atTop (𝓝 (upperTrace.value P Q))

theorem exists_iterated_trace_data (d : DyadicIndex → DyadicIndex → 𝕜)
    {M : ℝ} (hM : 0 ≤ M) (hd : ∀ I J, ‖d I J‖ ≤ M) :
    Nonempty (IteratedTraceData d M) := by
  obtain ⟨ao, ro, hro, hlo⟩ := countable_trace_cluster
    (fun J l k => d ⟨l, k⟩ J) hM (fun J l k => hd _ J)
    (fun n => n) strictMono_id
  obtain ⟨ai, ri, hri, hli⟩ := countable_trace_cluster
    (fun I l k => d I ⟨l, k⟩) hM (fun I l k => hd I _)
    (fun n => n) strictMono_id
  obtain ⟨lower, si, hsi, hll⟩ := iterated_trace_cluster hM ao ri hri
  obtain ⟨upper, so, hso, hlu⟩ := iterated_trace_cluster hM ai ro hro
  refine ⟨⟨ao, ai, lower, upper.flip, ro ∘ so, ri ∘ si,
    hro.comp hso, hri.comp hsi, ?_, ?_, hll, ?_⟩⟩
  · intro J P
    exact (hlo J P).comp hso.tendsto_atTop
  · intro I Q
    exact (hli I Q).comp hsi.tendsto_atTop
  · intro P Q
    exact hlu Q P

end SurveyStatements.P5.BiTree
