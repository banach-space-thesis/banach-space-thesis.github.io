import ThesisCommon.Analysis.L1Subsigma
import ThesisCommon.Analysis.CountablyGeneratedSup

/-! Separable sets in an actual L1 space lie in a countably generated
sub-sigma-algebra. An existing countably generated sub-sigma-algebra can be retained. -/
noncomputable section
open MeasureTheory Set MeasurableSpace TopologicalSpace
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)

theorem exists_countablyGenerated_lOneSubsigma_enlargement
    (m : MeasurableSpace X) (hm : m ≤ m₀) (hmc : @CountablyGenerated X m)
    (M : Set (Lp ℝ 1 μ)) (hM : TopologicalSpace.IsSeparable M) :
    ∃ m' : MeasurableSpace X, m' ≤ m₀ ∧ m ≤ m' ∧
      @CountablyGenerated X m' ∧ M ⊆ lOneSubsigma μ m' := by
  classical
  obtain ⟨D, hDc, hMD⟩ := hM
  letI : Countable D := hDc.to_subtype
  let s (f : D) : MeasurableSpace X := MeasurableSpace.comap (f.val : X → ℝ) (borel ℝ)
  have hsc (f : D) : @CountablyGenerated X (s f) := CountablyGenerated.comap _
  have hs (f : D) : s f ≤ m₀ := (Lp.stronglyMeasurable f.val).measurable.comap_le
  let m' : MeasurableSpace X := m ⊔ ⨆ f, s f
  have hm' : m' ≤ m₀ := sup_le hm (iSup_le hs)
  have hm'm : m ≤ m' := le_sup_left
  have hm'c : @CountablyGenerated X m' := hmc.sup (countablyGenerated_iSup s hsc)
  refine ⟨m', hm', hm'm, hm'c, hMD.trans ?_⟩
  apply closure_minimal ?_ (isClosed_lOneSubsigma μ hm')
  intro f hf
  have hmeas : @Measurable X ℝ m' (borel ℝ) f :=
    Measurable.of_comap_le ((le_iSup s ⟨f, hf⟩).trans le_sup_right)
  exact ⟨f, hmeas.stronglyMeasurable, Filter.EventuallyEq.rfl⟩

theorem exists_countablyGenerated_lOneSubsigma
    (M : Set (Lp ℝ 1 μ)) (hM : TopologicalSpace.IsSeparable M) :
    ∃ m : MeasurableSpace X, m ≤ m₀ ∧ @CountablyGenerated X m ∧
      M ⊆ lOneSubsigma μ m := by
  obtain ⟨m, hm, _, hmc, hMm⟩ :=
    exists_countablyGenerated_lOneSubsigma_enlargement μ ⊥ bot_le
      (countablyGenerated_bot X) M hM
  exact ⟨m, hm, hmc, hMm⟩

/-- The finite-measure separable envelope is an actual closed separable
L1 subspace, isometrically identified with L1 for the trimmed measure. -/
theorem exists_closed_separable_lOneSubsigma [IsFiniteMeasure μ]
    (M : Set (Lp ℝ 1 μ)) (hM : TopologicalSpace.IsSeparable M) :
    ∃ (m : MeasurableSpace X) (hm : m ≤ m₀), @CountablyGenerated X m ∧
      M ⊆ lOneSubsigma μ m ∧ IsClosed (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) ∧
      TopologicalSpace.IsSeparable (lOneSubsigma μ m : Set (Lp ℝ 1 μ)) := by
  obtain ⟨m, hm, hmc, hMm⟩ := exists_countablyGenerated_lOneSubsigma μ M hM
  letI := hmc
  exact ⟨m, hm, hmc, hMm, isClosed_lOneSubsigma μ hm, isSeparable_lOneSubsigma μ hm⟩

end ThesisCommon
