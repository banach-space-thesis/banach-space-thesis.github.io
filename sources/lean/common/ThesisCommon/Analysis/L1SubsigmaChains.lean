import ThesisCommon.Analysis.L1SubsigmaGenerated
import ThesisCommon.Analysis.L1SeparableEnvelope
import ThesisCommon.Analysis.RichFamilies

/-! Increasing chains of actual L1 subspaces associated to sub-sigma-algebras.
Only the L1 subspaces need be increasing; their chosen sigma-algebras need not be. -/
noncomputable section
open MeasureTheory Set MeasurableSpace
namespace ThesisCommon
variable {X : Type*} {m₀ : MeasurableSpace X} (μ : @Measure X m₀) [IsFiniteMeasure μ]

theorem richChainClosure_lOneSubsigma (m : ℕ → MeasurableSpace X)
    (hm : ∀ n, m n ≤ m₀) (hmono : Monotone (fun n => lOneSubsigma μ (m n))) :
    richChainClosure (fun n => lOneSubsigma μ (m n)) = lOneSubsigma μ (⨆ n, m n) := by
  let V := fun n => lOneSubsigma μ (m n)
  let P := richChainClosure V
  have hVP (n : ℕ) : V n ≤ P :=
    (le_iSup V n).trans (Submodule.le_topologicalClosure _)
  have hP : IsClosed (P : Set (Lp ℝ 1 μ)) := Submodule.isClosed_topologicalClosure _
  have hPsup : ∀ f ∈ P, ∀ g ∈ P, f ⊔ g ∈ P := by
    intro f hf g hg
    have hcoe : (P : Set (Lp ℝ 1 μ)) = closure (⋃ n, (V n : Set (Lp ℝ 1 μ))) :=
      richChainClosure_coe V hmono
    change f ∈ (P : Set (Lp ℝ 1 μ)) at hf
    change g ∈ (P : Set (Lp ℝ 1 μ)) at hg
    change f ⊔ g ∈ (P : Set (Lp ℝ 1 μ))
    rw [hcoe] at hf hg ⊢
    apply map_mem_closure₂ continuous_sup hf hg
    intro a ha b hb
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max i j, lOneSubsigma_sup_mem μ
      (hmono (le_max_left i j) hi) (hmono (le_max_right i j) hj)⟩
  have hPone : lOneIndicator μ univ MeasurableSet.univ ∈ P := by
    apply hVP 0
    exact ⟨fun _ => (1 : ℝ), @stronglyMeasurable_const X ℝ (m 0) _ (1 : ℝ),
      by simpa only [indicator_univ] using
        lOneIndicator_coe (μ := μ) univ MeasurableSet.univ⟩
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _
      (iSup_le fun n => lOneSubsigma_mono μ (le_iSup m n))
      (isClosed_lOneSubsigma μ (iSup_le hm))
  · exact lOneSubsigma_iSup_le μ m hm P hP hPsup hPone hVP

def countablyGeneratedL1Family : Set (Submodule ℝ (Lp ℝ 1 μ)) :=
  {P | ∃ m : MeasurableSpace X, m ≤ m₀ ∧ @CountablyGenerated X m ∧ P = lOneSubsigma μ m}

theorem isRichFamily_countablyGeneratedL1 : IsRichFamily (countablyGeneratedL1Family μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro P ⟨m, hm, _, rfl⟩
    exact isClosed_lOneSubsigma μ hm
  · rintro P ⟨m, hm, hmc, rfl⟩
    letI := hmc
    exact isSeparable_lOneSubsigma μ hm
  · intro M hM
    obtain ⟨m, hm, hmc, hMm⟩ := exists_countablyGenerated_lOneSubsigma μ M hM
    exact ⟨lOneSubsigma μ m, ⟨m, hm, hmc, rfl⟩, hMm⟩
  · intro V hV hmono
    choose m hm hmc heq using hV
    have hmono' : Monotone (fun n => lOneSubsigma μ (m n)) := by
      simpa only [← heq] using hmono
    refine ⟨⨆ n, m n, iSup_le hm, countablyGenerated_iSup m hmc, ?_⟩
    rw [show V = (fun n => lOneSubsigma μ (m n)) from funext heq]
    exact richChainClosure_lOneSubsigma μ m hm hmono'

end ThesisCommon
