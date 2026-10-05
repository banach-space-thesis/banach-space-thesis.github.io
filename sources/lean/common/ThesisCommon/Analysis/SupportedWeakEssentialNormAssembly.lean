import ThesisCommon.Analysis.SupportedWeakEssentialNorm
import ThesisCommon.Analysis.ComplexWeakCompactL1SigmaFiniteRange
import Mathlib.Topology.Order.IsLUB

/-! Conditional final assembly, separated from the still substantive
existence of supported best approximants. Countably many genuine weakly
compact approximants share one measurable sigma-finite output support. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace ThesisCommon
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem sigmaFinite_restrict_countable_iUnion
    (Θ : ℕ → Set Y) (hΘ : ∀ n, MeasurableSet (Θ n))
    (hσ : ∀ n, SigmaFinite (ν.restrict (Θ n))) : SigmaFinite (ν.restrict (⋃ n, Θ n)) := by
  letI (n : ℕ) : SigmaFinite (ν.restrict (Θ n)) := hσ n
  let A : ℕ × ℕ → Set Y := fun p =>
    (spanningSets (ν.restrict (Θ p.1)) p.2 ∩ Θ p.1) ∪ (⋃ n, Θ n)ᶜ
  have hA (p : ℕ × ℕ) : MeasurableSet (A p) :=
    ((measurableSet_spanningSets _ _).inter (hΘ p.1)).union (MeasurableSet.iUnion hΘ).compl
  apply Measure.sigmaFinite_of_countable (countable_range A)
  · rintro s ⟨p, rfl⟩
    rw [Measure.restrict_apply (hA p)]
    have hp := measure_spanningSets_lt_top (ν.restrict (Θ p.1)) p.2
    rw [Measure.restrict_apply (measurableSet_spanningSets _ _)] at hp
    apply (measure_mono ?_).trans_lt hp
    intro y hy
    exact hy.1.elim id (fun hn => False.elim (hn hy.2))
  · rw [sUnion_range]
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    by_cases hy : y ∈ ⋃ n, Θ n
    · obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
      have hycover : y ∈ ⋃ j, spanningSets (ν.restrict (Θ n)) j := by
        rw [iUnion_spanningSets]
        trivial
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hycover
      exact ⟨(n, j), Or.inl ⟨hyj, hyn⟩⟩
    · exact ⟨(0, 0), Or.inr hy⟩

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_sigmaFinite_supportedWeakEssentialNorm_eq
    (T : E →L[𝕜] Lp 𝕜 1 ν)
    (hsupport : ∀ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W →
      ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧ L1OperatorSupportedOn Θ W) :
    ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧
      supportedWeakEssentialNorm Θ T = weakEssentialNorm T := by
  let D : Set ℝ := {r | ∃ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W ∧ r = ‖T - W‖}
  have hD : D.Nonempty := ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
  have hDb : BddBelow D := ⟨0, by rintro r ⟨W, _, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨u, _, hu, hmem⟩ := exists_seq_tendsto_sInf hD hDb
  choose W hW heq using hmem
  choose Θ hΘ hσ hs using fun n => hsupport (W n) (hW n)
  refine ⟨⋃ n, Θ n, MeasurableSet.iUnion hΘ,
    sigmaFinite_restrict_countable_iUnion Θ hΘ hσ, le_antisymm ?_
      (weakEssentialNorm_le_supported _ T)⟩
  have hle (n : ℕ) : supportedWeakEssentialNorm (⋃ n, Θ n) T ≤ u n := by
    rw [heq n]
    exact supportedWeakEssentialNorm_le _ T (hW n) ((hs n).mono (subset_iUnion Θ n))
  exact ge_of_tendsto hu (Eventually.of_forall hle)

theorem exists_weaklyCompact_bestApproximation_of_supported
    (T : E →L[𝕜] Lp 𝕜 1 ν)
    (hsupport : ∀ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W →
      ∃ Θ : Set Y, MeasurableSet Θ ∧ SigmaFinite (ν.restrict Θ) ∧ L1OperatorSupportedOn Θ W)
    (hbest : ∀ Θ : Set Y, MeasurableSet Θ → SigmaFinite (ν.restrict Θ) →
      ∃ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
        ‖T - W‖ = supportedWeakEssentialNorm Θ T) :
    ∃ W : E →L[𝕜] Lp 𝕜 1 ν, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T := by
  obtain ⟨Θ, hΘ, hσ, heq⟩ := exists_sigmaFinite_supportedWeakEssentialNorm_eq T hsupport
  obtain ⟨W, hW, _, hnorm⟩ := hbest Θ hΘ hσ
  exact ⟨W, hW, hnorm.trans heq⟩

theorem exists_real_weaklyCompact_bestApproximation_of_supported
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] Lp ℝ 1 ν)
    (hbest : ∀ Θ : Set Y, MeasurableSet Θ → SigmaFinite (ν.restrict Θ) →
      ∃ W : E →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
        ‖T - W‖ = supportedWeakEssentialNorm Θ T) :
    ∃ W : E →L[ℝ] Lp ℝ 1 ν, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T :=
  exists_weaklyCompact_bestApproximation_of_supported T
    (fun _ hW => hW.exists_sigmaFinite_range_part) hbest

theorem exists_complex_weaklyCompact_bestApproximation_of_supported
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (T : E →L[ℂ] Lp ℂ 1 ν)
    (hbest : ∀ Θ : Set Y, MeasurableSet Θ → SigmaFinite (ν.restrict Θ) →
      ∃ W : E →L[ℂ] Lp ℂ 1 ν, IsWeaklyCompactOperator W ∧ L1OperatorSupportedOn Θ W ∧
        ‖T - W‖ = supportedWeakEssentialNorm Θ T) :
    ∃ W : E →L[ℂ] Lp ℂ 1 ν, IsWeaklyCompactOperator W ∧ ‖T - W‖ = weakEssentialNorm T :=
  exists_weaklyCompact_bestApproximation_of_supported T
    (fun _ hW => hW.exists_sigmaFinite_range_part_complex) hbest

end ThesisCommon
