import ThesisCommon.Analysis.L1SeparableReduction
import ThesisCommon.Analysis.L1SubsigmaChains
import PEMS.RichFamilies

/-! Lemma 4.8, for real L1 spaces: the exact modulus-preserving family of
actual countably generated L1 subspaces is rich. The inclusion is expressed
by the proved isometry from the trimmed measure space, with its genuine
operator modulus. The proof uses constant-one witnesses and upward
inheritance, including zero measure spaces. -/
noncomputable section
open MeasureTheory MeasurableSpace Set ThesisCommon
open scoped ThesisCommon.PositiveOperatorOrder
namespace PEMS
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable {μ : @Measure X m₀} {ν : @Measure Y n₀} [IsFiniteMeasure μ]

def modulusPreservingL1Family (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    Set (Submodule ℝ (Lp ℝ 1 μ)) :=
  {P | ∃ (m : MeasurableSpace X) (hm : m ≤ m₀),
    @CountablyGenerated X m ∧ P = lOneSubsigma μ m ∧ L1SubsigmaPreservesModulus T hm}

theorem lemma_4_8_modulus_rich (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    IsRichFamily (modulusPreservingL1Family T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro P ⟨m, hm, _, rfl, _⟩
    exact isClosed_lOneSubsigma μ hm
  · rintro P ⟨m, hm, hmc, rfl, _⟩
    letI := hmc
    exact isSeparable_lOneSubsigma μ hm
  · intro M hM
    obtain ⟨m, hm, _, hmc, hMP, hmod⟩ :=
      exists_countablyGenerated_modulusPreserving_lOneSubsigma T ⊥ bot_le
        (countablyGenerated_bot X) M hM
    exact ⟨lOneSubsigma μ m, ⟨m, hm, hmc, rfl, hmod⟩, hMP⟩
  · intro V hV hmono
    choose m hm hmc heq hmod using hV
    have hmono' : Monotone (fun n => lOneSubsigma μ (m n)) := by
      simpa only [← heq] using hmono
    refine ⟨⨆ n, m n, iSup_le hm, countablyGenerated_iSup m hmc, ?_, ?_⟩
    · rw [show V = (fun n => lOneSubsigma μ (m n)) from funext heq]
      exact richChainClosure_lOneSubsigma μ m hm hmono'
    · exact (hmod 0).mono (lOneSubsigma_mono μ (le_iSup m 0))

theorem lemma_4_8_simultaneous_modulus_rich
    (T : ℕ → (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)) :
    IsRichFamily (⋂ n, modulusPreservingL1Family (T n)) :=
  rich_family_countable_intersection _ (fun n => lemma_4_8_modulus_rich (T n))

end PEMS
