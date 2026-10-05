import ThesisCommon.LpCut
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite-measure approximation and quantitative cutoff estimates for real or
complex L1, with no finiteness assumption on the underlying measure. -/
noncomputable section
open MeasureTheory Set Filter Topology Function
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem norm_rclike_lOneCut_eq_integral (A : Set X) (hA : MeasurableSet A)
    (f : Lp 𝕜 1 μ) : ‖lpCut A hA f‖ = ∫ x in A, ‖f x‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖lpCut A hA f x‖ ∂μ) = ∫ x, A.indicator (fun x => ‖f x‖) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [lpCut_coe A hA f] with x hx
      rw [hx]
      by_cases h : x ∈ A <;> simp [h]
    _ = _ := integral_indicator hA

theorem rclike_lOneCut_exists_finite_measure (f : Lp 𝕜 1 μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ A, ∃ hA : MeasurableSet A, μ A < ∞ ∧ ‖lpCut Aᶜ hA.compl f‖ < ε := by
  obtain ⟨A, hA, hμA, hcut⟩ := (Lp.memLp f).exists_eLpNorm_indicator_compl_lt
    (by norm_num : (1 : ENNReal) ≠ ∞) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨A, hA, hμA, ?_⟩
  change ‖((Lp.memLp f).indicator hA.compl).toLp (Aᶜ.indicator f)‖ < ε
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_lt_toReal ((Lp.memLp f).indicator hA.compl).2.ne
    ENNReal.ofReal_ne_top).mpr hcut |>.trans_eq (ENNReal.toReal_ofReal hε.le)

theorem rclike_lOneCut_small_measure (f : Lp 𝕜 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A, ∀ hA : MeasurableSet A,
      μ A ≤ ENNReal.ofReal δ → ‖lpCut A hA f‖ ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := (Lp.memLp f).eLpNorm_indicator_le le_rfl (by norm_num) hε
  refine ⟨δ, hδ, fun A hA hμA => ?_⟩
  change ‖((Lp.memLp f).indicator hA).toLp (A.indicator f)‖ ≤ ε
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (h A hA hμA)).trans_eq
    (ENNReal.toReal_ofReal hε.le)

theorem finite_rclike_lOneCut_small_measure {I : Type*} (F : Finset I)
    (f : I → Lp 𝕜 1 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ F, ∀ A, ∀ hA : MeasurableSet A,
      μ A ≤ ENNReal.ofReal δ → ‖lpCut A hA (f i)‖ ≤ ε := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨δ, hδ, hh⟩ := ih
    obtain ⟨η, hη, hg⟩ := rclike_lOneCut_small_measure (f i) hε
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro j hj A hA hμA
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hg A hA (hμA.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
    · exact hh j hj A hA (hμA.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))

theorem norm_rclike_lOneCut_mono {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (f : Lp 𝕜 1 μ) :
    ‖lpCut A hA f‖ ≤ ‖lpCut B hB f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpCut_coe A hA f, lpCut_coe B hB f] with x hxA hxB
  rw [hxA, hxB]
  by_cases hx : x ∈ A
  · simp [hx, hAB hx]
  · simp [hx]

theorem norm_rclike_lOneCut_sub_le_diff (A C : Set X) (hA : MeasurableSet A)
    (hC : MeasurableSet C) (f : Lp 𝕜 1 μ) :
    ‖lpCut A hA f‖ - ‖lpCut C hC f‖ ≤ ‖lpCut (A \ C) (hA.diff hC) f‖ := by
  have hmono := norm_rclike_lOneCut_mono (hA.inter hC) hC inter_subset_right f
  simp only [norm_rclike_lOneCut_eq_integral] at hmono ⊢
  have hsplit := integral_inter_add_diff hC (L1.integrable_coeFn f).norm.integrableOn
    (s := A)
  linarith

theorem norm_rclike_lOneCut_iUnion_le_of_hasSum (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n)) (f : Lp 𝕜 1 μ)
    {a : ℕ → ℝ} {b : ℝ} (ha : HasSum a b)
    (hbound : ∀ n, ‖lpCut (C n) (hC n) f‖ ≤ a n) :
    ‖lpCut (⋃ n, C n) (MeasurableSet.iUnion hC) f‖ ≤ b := by
  have hs := hasSum_integral_iUnion (MeasurableSet.disjointed hC)
    (disjoint_disjointed C) (L1.integrable_coeFn f).norm.integrableOn
  rw [iUnion_disjointed] at hs
  rw [norm_rclike_lOneCut_eq_integral]
  apply hasSum_le _ hs ha
  intro n
  rw [← norm_rclike_lOneCut_eq_integral _ (MeasurableSet.disjointed hC n)]
  exact (norm_rclike_lOneCut_mono (MeasurableSet.disjointed hC n) (hC n)
    (disjointed_le C n) f).trans (hbound n)

end ThesisCommon
