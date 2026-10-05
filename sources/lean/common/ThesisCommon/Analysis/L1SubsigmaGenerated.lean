import ThesisCommon.Analysis.L1Subsigma
import Mathlib.MeasureTheory.SetAlgebra

/-! A closed L1 sublattice containing constants and the indicators of a
family contains all L1 functions measurable for the generated sigma algebra. -/
noncomputable section
open MeasureTheory Set MeasurableSpace
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀) [IsFiniteMeasure μ]

theorem lOneSubsigma_le_of_indicators {m : MeasurableSpace X} (hm : m ≤ m₀)
    (P : Submodule ℝ (Lp ℝ 1 μ)) (hP : IsClosed (P : Set (Lp ℝ 1 μ)))
    (hI : ∀ (s : Set X) (hs : MeasurableSet[m] s),
      lOneIndicator (mX := m₀) μ s (hm s hs) ∈ P) : lOneSubsigma μ m ≤ P := by
  intro f hf
  apply Lp.induction_stronglyMeasurable hm (by norm_num : (1 : ENNReal) ≠ ⊤)
    (fun g => g ∈ P) ?_ ?_ ?_ f hf
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst X ℝ m₀,
      @indicatorConstLp_eq_smul_lOneIndicator X m₀ μ _]
    exact P.smul_mem c (hI s hs)
  · intro f g hf hg _ _ _ hPf hPg
    exact P.add_mem hPf hPg
  · exact hP.preimage (lOneSubsigma μ m).subtypeL.continuous

theorem lOneIndicator_mem_generateSetAlgebra
    (P : Submodule ℝ (Lp ℝ 1 μ))
    (hPsup : ∀ f ∈ P, ∀ g ∈ P, f ⊔ g ∈ P)
    (hPone : lOneIndicator μ univ MeasurableSet.univ ∈ P)
    (C : Set (Set X)) (hC : ∀ s ∈ C, MeasurableSet[m₀] s)
    (hPC : ∀ (s : Set X) (hs : s ∈ C), lOneIndicator μ s (hC s hs) ∈ P)
    {s : Set X} (hs : s ∈ generateSetAlgebra C) :
    ∃ hsm : MeasurableSet[m₀] s, lOneIndicator μ s hsm ∈ P := by
  classical
  induction hs with
  | base s hs => exact ⟨hC s hs, hPC s hs⟩
  | empty =>
      refine ⟨MeasurableSet.empty, ?_⟩
      have hz : lOneIndicator μ ∅ MeasurableSet.empty = 0 := by
        apply Lp.ext
        exact (lOneIndicator_coe ∅ MeasurableSet.empty).trans
          (by simpa using (Lp.coeFn_zero ℝ 1 μ).symm)
      rw [hz]
      exact P.zero_mem
  | compl s _ ih =>
      obtain ⟨hs, hPs⟩ := ih
      refine ⟨hs.compl, ?_⟩
      have heq : lOneIndicator μ sᶜ hs.compl =
          lOneIndicator μ univ MeasurableSet.univ - lOneIndicator μ s hs := by
        apply Lp.ext
        filter_upwards [lOneIndicator_coe (μ := μ) sᶜ hs.compl,
          Lp.coeFn_sub (lOneIndicator μ univ MeasurableSet.univ) (lOneIndicator μ s hs),
          lOneIndicator_coe (μ := μ) univ MeasurableSet.univ,
          lOneIndicator_coe (μ := μ) s hs] with x hc hsub hone hsx
        rw [hc, hsub, Pi.sub_apply, hone, hsx]
        by_cases hx : x ∈ s <;> simp [hx]
      rw [heq]
      exact P.sub_mem hPone hPs
  | union s t _ _ ihs iht =>
      obtain ⟨hs, hPs⟩ := ihs
      obtain ⟨ht, hPt⟩ := iht
      refine ⟨hs.union ht, ?_⟩
      have heq : lOneIndicator μ (s ∪ t) (hs.union ht) =
          lOneIndicator μ s hs ⊔ lOneIndicator μ t ht := by
        apply Lp.ext
        filter_upwards [lOneIndicator_coe (μ := μ) (s ∪ t) (hs.union ht),
          Lp.coeFn_sup (lOneIndicator μ s hs) (lOneIndicator μ t ht),
          lOneIndicator_coe (μ := μ) s hs,
          lOneIndicator_coe (μ := μ) t ht] with x hu hsup hsx htx
        by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hu, hsup, hsx, htx, hx, hy]
      rw [heq]
      exact hPsup _ hPs _ hPt

theorem lOneSubsigma_generateFrom_le
    (P : Submodule ℝ (Lp ℝ 1 μ)) (hP : IsClosed (P : Set (Lp ℝ 1 μ)))
    (hPsup : ∀ f ∈ P, ∀ g ∈ P, f ⊔ g ∈ P)
    (hPone : lOneIndicator μ univ MeasurableSet.univ ∈ P)
    (C : Set (Set X)) (hC : ∀ s ∈ C, MeasurableSet[m₀] s)
    (hPC : ∀ (s : Set X) (hs : s ∈ C), lOneIndicator μ s (hC s hs) ∈ P) :
    lOneSubsigma μ (generateFrom C) ≤ P := by
  classical
  let m := generateFrom C
  have hm : m ≤ m₀ := generateFrom_le hC
  let ν := μ.trim hm
  let J := lOneSubsigmaEmbedding μ hm
  let A := generateSetAlgebra C
  have hgen : m = generateFrom A := generateFrom_generateSetAlgebra_eq.symm
  have hA : ν.MeasureDense A :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ν isSetAlgebra_generateSetAlgebra hgen
  have hPpre : IsClosed {f : Lp ℝ 1 ν | J f ∈ P} := hP.preimage J.continuous
  letI : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply lOneSubsigma_le_of_indicators μ hm P hP
  intro s hs
  have hI : indicatorConstLp 1 hs (measure_ne_top ν s) (1 : ℝ) ∈
      closure {indicatorConstLp 1 (hA.measurable t ht) hνt (1 : ℝ) |
        (t : Set X) (ht : t ∈ A) (hνt : ν t ≠ ⊤)} :=
    hA.indicatorConstLp_subset_closure 1 (1 : ℝ) ⟨s, hs, measure_ne_top ν s, rfl⟩
  have hsubset : closure {indicatorConstLp 1 (hA.measurable t ht) hνt (1 : ℝ) |
        (t : Set X) (ht : t ∈ A) (hνt : ν t ≠ ⊤)} ⊆ {f : Lp ℝ 1 ν | J f ∈ P} := by
    apply closure_minimal ?_ hPpre
    rintro _ ⟨t, ht, hνt, rfl⟩
    obtain ⟨htm, htP⟩ := lOneIndicator_mem_generateSetAlgebra μ P hPsup hPone C hC hPC ht
    change J (indicatorConstLp 1 (hA.measurable t ht) hνt (1 : ℝ)) ∈ P
    rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul]
    change lOneSubsigmaEmbedding μ hm (lOneIndicator ν t (hA.measurable t ht)) ∈ P
    rw [lOneSubsigmaEmbedding_indicator]
    exact htP
  have hmem := hsubset hI
  change J (indicatorConstLp 1 hs (measure_ne_top ν s) (1 : ℝ)) ∈ P at hmem
  rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul] at hmem
  exact (lOneSubsigmaEmbedding_indicator μ hm s hs) ▸ hmem

theorem lOneSubsigma_iSup_le {I : Type*} (m : I → MeasurableSpace X)
    (hm : ∀ i, m i ≤ m₀) (P : Submodule ℝ (Lp ℝ 1 μ))
    (hP : IsClosed (P : Set (Lp ℝ 1 μ)))
    (hPsup : ∀ f ∈ P, ∀ g ∈ P, f ⊔ g ∈ P)
    (hPone : lOneIndicator μ univ MeasurableSet.univ ∈ P)
    (hPm : ∀ i, lOneSubsigma μ (m i) ≤ P) : lOneSubsigma μ (⨆ i, m i) ≤ P := by
  let C := ⋃ i, {s | MeasurableSet[m i] s}
  have hC : ∀ s ∈ C, MeasurableSet[m₀] s := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact hm i s hi
  rw [← generateFrom_iUnion_measurableSet]
  apply lOneSubsigma_generateFrom_le μ P hP hPsup hPone C hC
  intro s hs
  obtain ⟨i, hi⟩ := mem_iUnion.mp hs
  apply hPm i
  exact ⟨s.indicator (fun _ => (1 : ℝ)),
    (@stronglyMeasurable_const X ℝ (m i) _ (1 : ℝ)).indicator hi,
    lOneIndicator_coe (μ := μ) s (hC s (mem_iUnion.mpr ⟨i, hi⟩))⟩

end ThesisCommon
