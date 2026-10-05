import ThesisCommon.Analysis.KernelSmallSetTests
import ThesisCommon.Analysis.KernelProductRestriction

/-! A fibre-dependent small set can be approximated by one fixed measurable
output set on a positive-measure set of inputs. Countable generation is
used only on the output. The nonzero input measure is necessary for the
positive-measure witness conclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [mY : MeasurableSpace Y]
variable [MeasurableSpace.CountablyGenerated Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]

theorem exists_smallSet_kernel_witness (hμ : μ ≠ 0)
    (κ : Kernel X Y) [IsFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A) {δ ε : ℝ} (hε : 0 < ε)
    (hsize : ∀ᵐ x ∂μ, ν.real (Prod.mk x ⁻¹' A) < δ) :
    ∃ (B : Set Y) (M : Set X), MeasurableSet B ∧ ν.real B < δ ∧
      MeasurableSet M ∧ 0 < μ M ∧
      ∀ x ∈ M, (κ x).real (Prod.mk x ⁻¹' A) ≤ (κ x).real B + ε := by
  classical
  let 𝒜 := generateSetAlgebra (MeasurableSpace.countableGeneratingSet Y)
  have hgen : mY = MeasurableSpace.generateFrom 𝒜 := by
    rw [generateFrom_generateSetAlgebra_eq, MeasurableSpace.generateFrom_countableGeneratingSet]
  have hcount : 𝒜.Countable :=
    countable_generateSetAlgebra MeasurableSpace.countable_countableGeneratingSet
  letI : Countable 𝒜 := hcount.to_subtype
  letI : NeZero μ := ⟨hμ⟩
  let q : X → ℝ := fun x => (productSetKernel κ A x).real univ
  have hq : Measurable q := (Kernel.measurable_coe _ MeasurableSet.univ).ennreal_toReal
  have hqeq (x : X) : q x = (κ x).real (Prod.mk x ⁻¹' A) := by
    dsimp [q, measureReal_def]
    rw [productSetKernel_apply κ A hA, Measure.restrict_apply_univ]
  let M : 𝒜 → Set X := fun B => {x | q x ≤ (κ x).real B + ε}
  have hMmeas (B : 𝒜) : MeasurableSet (M B) :=
    measurableSet_le hq (((Kernel.measurable_coe κ
      (hgen ▸ MeasurableSpace.measurableSet_generateFrom B.2)).ennreal_toReal).add_const ε)
  have hcover : ∀ᵐ x ∂μ, ∃ B : 𝒜, ν.real B < δ ∧ x ∈ M B := by
    filter_upwards [hsize] with x hx
    obtain ⟨B, hB, hBδ, happrox⟩ := exists_small_algebra_measure_approximation
      isSetAlgebra_generateSetAlgebra hgen (measurable_prodMk_left hA) hx hε (σ := κ x)
    refine ⟨⟨B, hB⟩, hBδ, ?_⟩
    change q x ≤ (κ x).real B + ε
    rwa [hqeq]
  have hex : ∃ B : 𝒜, ν.real B < δ ∧ 0 < μ (M B) := by
    by_contra hn
    push_neg at hn
    have hz : ∀ B : 𝒜, ∀ᵐ x ∂μ, ν.real B < δ → x ∉ M B := by
      intro B
      by_cases hB : ν.real B < δ
      · have hzero : μ (M B) = 0 := le_antisymm (hn B hB) (zero_le _)
        have hnot : ∀ᵐ x ∂μ, x ∉ M B := by
          rw [ae_iff]
          simpa using hzero
        exact hnot.mono fun _ hx _ => hx
      · exact Eventually.of_forall fun _ hx => (hB hx).elim
    have hall : ∀ᵐ x ∂μ, ∀ B : 𝒜, ν.real B < δ → x ∉ M B := ae_all_iff.mpr hz
    obtain ⟨x, ⟨B, hB, hx⟩, hallx⟩ := (hcover.and hall).exists
    exact hallx B hB hx
  obtain ⟨B, hBδ, hpos⟩ := hex
  refine ⟨B, M B, hgen ▸ MeasurableSpace.measurableSet_generateFrom B.2,
    hBδ, hMmeas B, hpos, ?_⟩
  intro x hx
  change q x ≤ (κ x).real B + ε at hx
  rwa [hqeq] at hx

end ThesisCommon
