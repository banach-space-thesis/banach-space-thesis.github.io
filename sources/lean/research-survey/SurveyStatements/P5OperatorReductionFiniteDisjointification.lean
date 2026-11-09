import SurveyStatements.P5OperatorReductionDisjointReaders
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Finite disjointification for actual L1 families. Arbitrarily large
finite disjoint witnesses are sufficient for the shadow randomization
contradiction; no infinite disjointification result is assumed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜]

theorem l1_restriction_eLpNorm (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp 𝕜 1 unitIntervalMeasure) :
    eLpNorm (s.indicator f) 1 unitIntervalMeasure =
      ENNReal.ofReal ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs f‖ := by
  calc
    _ = eLpNorm (vectorIndicatorMultiply (𝕜 := 𝕜) s hs f) 1 unitIntervalMeasure :=
      eLpNorm_congr_ae (vectorIndicatorMultiply_ae (𝕜 := 𝕜) s hs f).symm
    _ = ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs f‖ₑ := (Lp.enorm_def _).symm
    _ = _ := (ofReal_norm_eq_enorm _).symm

def UniformSmallRestrictions {ι : Type*} (f : ι → Lp 𝕜 1 unitIntervalMeasure) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i s (hs : MeasurableSet s),
    unitIntervalMeasure s ≤ ENNReal.ofReal δ →
      ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs (f i)‖ ≤ ε

theorem uniformSmallRestrictions_iff_unifIntegrable {ι : Type*}
    (f : ι → Lp 𝕜 1 unitIntervalMeasure) :
    UniformSmallRestrictions f ↔ UnifIntegrable (fun i x => f i x) 1 unitIntervalMeasure := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hsmall⟩ := h ε hε
    refine ⟨δ, hδ, fun i s hs hμ => ?_⟩
    rw [l1_restriction_eLpNorm s hs]
    exact ENNReal.ofReal_le_ofReal (hsmall i s hs hμ)
  · intro h ε hε
    obtain ⟨δ, hδ, hsmall⟩ := h hε
    refine ⟨δ, hδ, fun i s hs hμ => ?_⟩
    have h := hsmall i s hs hμ
    rw [l1_restriction_eLpNorm s hs] at h
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h

theorem finite_positive_lower_bound {ι : Type*} (F : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ F, 0 < d i) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ F, c ≤ d i := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨c, hc, hcd⟩ := ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))
    refine ⟨min (d i) c, lt_min (hd i (Finset.mem_insert_self _ _)) hc, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hcd j hj)

theorem l1_finite_absolute_continuity {n : ℕ}
    (f : Fin n → Lp 𝕜 1 unitIntervalMeasure) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i s (hs : MeasurableSet s),
      unitIntervalMeasure s ≤ ENNReal.ofReal δ →
        ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs (f i)‖ ≤ a i / 2 := by
  choose d hd hsmall using (fun i => (Lp.memLp (f i)).eLpNorm_indicator_le
    (by norm_num : (1 : ℝ≥0∞) ≤ 1) ENNReal.one_ne_top (half_pos (ha i)))
  obtain ⟨δ, hδ, hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  refine ⟨δ, hδ, fun i s hs hμ => ?_⟩
  have h := hsmall i s hs
    (hμ.trans (ENNReal.ofReal_le_ofReal (hδd i (Finset.mem_univ i))))
  rw [l1_restriction_eLpNorm s hs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (half_pos (ha i)).le).mp h

theorem finite_disjointification {ι : Type*}
    (f : ι → Lp 𝕜 1 unitIntervalMeasure) {ε : ℝ} (hε : 0 < ε)
    (hfail : ∀ δ : ℝ, 0 < δ → ∃ i, ∃ s, ∃ hs : MeasurableSet s,
      unitIntervalMeasure s ≤ ENNReal.ofReal δ ∧
        ε < ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs (f i)‖) :
    ∀ n : ℕ, ∃ v : Fin n → ι, ∃ s : Fin n → Set ℝ,
      (∀ i, MeasurableSet (s i)) ∧
      (∀ i j, i ≠ j → Disjoint (s i) (s j)) ∧
      ∀ i (hs : MeasurableSet (s i)),
        ε / 2 < ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s i) hs (f (v i))‖ := by
  intro n
  induction n with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨v, s, hs, hd, hm⟩ := ih
    let a (i : Fin n) := ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s i) (hs i) (f (v i))‖ - ε / 2
    have ha (i : Fin n) : 0 < a i := by dsimp [a]; linarith [hm i (hs i)]
    obtain ⟨δ, hδ, hsmall⟩ := l1_finite_absolute_continuity (fun i => f (v i)) a ha
    obtain ⟨v₀, s₀, hs₀, hμ₀, hm₀⟩ := hfail δ hδ
    refine ⟨Fin.cons v₀ v, Fin.cons s₀ (fun i => s i \ s₀), ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases hs₀ (fun j => (hs j).diff hs₀) i
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro h
          exact (h rfl).elim
        · intro _
          change Disjoint s₀ (s j \ s₀)
          exact Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          change Disjoint (s i \ s₀) s₀
          exact Set.disjoint_left.mpr (fun x hx hy => hx.2 hy)
        · intro hij
          change Disjoint (s i \ s₀) (s j \ s₀)
          exact (hd i j (fun h => hij (congrArg Fin.succ h))).mono diff_subset diff_subset
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro hsi
        change ε / 2 < ‖vectorIndicatorMultiply (𝕜 := 𝕜) s₀ hsi (f v₀)‖
        linarith
      · intro hsi
        change ε / 2 < ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s i \ s₀) hsi (f (v i))‖
        have hf := ((Lp.memLp (f (v i))).integrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 1)).norm
        have hsplit := integral_inter_add_diff hs₀ (hf.integrableOn (s := s i))
        have hcut : (∫ x in s i ∩ s₀, ‖f (v i) x‖ ∂unitIntervalMeasure) ≤
            ∫ x in s₀, ‖f (v i) x‖ ∂unitIntervalMeasure :=
          integral_mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
            (Eventually.of_forall (fun x => norm_nonneg (f (v i) x))) hf.integrableOn
        have hsmalli := hsmall i s₀ hs₀ hμ₀
        have hmassi := hm i (hs i)
        rw [norm_l1_restriction (s i) (hs i)] at hmassi
        rw [norm_l1_restriction s₀ hs₀] at hsmalli
        rw [norm_l1_restriction (s i \ s₀) hsi]
        have haeq : a i = (∫ x in s i, ‖f (v i) x‖ ∂unitIntervalMeasure) - ε / 2 := by
          dsimp [a]
          rw [norm_l1_restriction]
        rw [haeq] at hsmalli
        nlinarith

theorem finite_disjointification_of_not_uniformSmallRestrictions {ι : Type*}
    (f : ι → Lp 𝕜 1 unitIntervalMeasure) (h : ¬ UniformSmallRestrictions f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ v : Fin n → ι, ∃ s : Fin n → Set ℝ,
      (∀ i, MeasurableSet (s i)) ∧
      (∀ i j, i ≠ j → Disjoint (s i) (s j)) ∧
      ∀ i (hs : MeasurableSet (s i)),
        ε < ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s i) hs (f (v i))‖ := by
  simp only [UniformSmallRestrictions] at h
  push_neg at h
  obtain ⟨ε, hε, hfail⟩ := h
  exact ⟨ε / 2, half_pos hε, finite_disjointification f hε hfail⟩

end SurveyStatements.P5OperatorReduction
