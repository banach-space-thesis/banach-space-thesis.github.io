import Mathlib.Probability.ProductMeasure
import Mathlib.Algebra.BigOperators.Option
import ThesisCommon.Analysis.LebesgueLpTransport

/-! Splitting one coordinate from a genuinely arbitrary-index probability
product. Measure preservation is proved on finite cylinders, so no
countability condition or assumed product identification is introduced. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThesisCommon
variable {ι A : Type*} [MeasurableSpace A]

def optionPiMeasurableEquiv : (Option ι → A) ≃ᵐ (ι → A) × A where
  toEquiv := Equiv.piOptionEquivProd.trans (Equiv.prodComm _ _)
  measurable_toFun := (measurable_pi_iff.mpr fun i => measurable_pi_apply (some i)).prodMk
    (measurable_pi_apply none)
  measurable_invFun := measurable_pi_iff.mpr fun i => by
    cases i with
    | none => exact measurable_snd
    | some i => exact (measurable_pi_apply i).comp measurable_fst

theorem infinitePi_option_split (μ : Option ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (optionPiMeasurableEquiv (ι := ι) (A := A)) (Measure.infinitePi μ)
      ((Measure.infinitePi fun i => μ (some i)).prod (μ none)) := by
  classical
  let e := optionPiMeasurableEquiv (ι := ι) (A := A)
  have hmap : Measure.map e.symm ((Measure.infinitePi fun i => μ (some i)).prod (μ none)) =
      Measure.infinitePi μ := by
    apply Measure.eq_infinitePi
    intro s t ht
    have hpre : e.symm ⁻¹' Set.pi (s : Set (Option ι)) t =
        (Set.pi (s.eraseNone : Set ι) (fun i => t (some i))) ×ˢ
          (if none ∈ s then t none else univ) := by
      ext z
      change (∀ i ∈ s, (e.symm z) i ∈ t i) ↔ _
      constructor
      · intro h
        constructor
        · intro i hi
          exact h (some i) (Finset.mem_eraseNone.mp hi)
        · by_cases hn : none ∈ s
          · simpa only [if_pos hn] using h none hn
          · simp only [if_neg hn, mem_univ]
      · rintro ⟨h₁, h₂⟩ i hi
        cases i with
        | none => simpa only [if_pos hi] using h₂
        | some i => exact h₁ i (Finset.mem_eraseNone.mpr hi)
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi s.countable_toSet ht), hpre,
      Measure.prod_prod, Measure.infinitePi_pi]
    · have hprod : (∏ i ∈ s.eraseNone, μ (some i) (t (some i))) =
          ∏ i ∈ s.erase none, μ i (t i) := by
        rw [← Finset.map_some_eraseNone s, Finset.prod_map]
        rfl
      rw [hprod]
      by_cases hn : none ∈ s
      · rw [if_pos hn, mul_comm]
        exact Finset.mul_prod_erase s (fun i => μ i (t i)) hn
      · rw [if_neg hn, measure_univ, mul_one, Finset.erase_eq_of_notMem hn]
    · intro i hi
      exact ht (some i) (Finset.mem_eraseNone.mp hi)
  exact (MeasurePreserving.symm e.symm ⟨e.symm.measurable, hmap⟩)

def infinitePiOptionLpEquiv {𝕜 : Type*} [RCLike 𝕜]
    (μ : Option ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (Measure.infinitePi μ) ≃ₗᵢ[𝕜]
      Lp 𝕜 p ((Measure.infinitePi fun i => μ (some i)).prod (μ none)) :=
  (lebesgueLpTransport (optionPiMeasurableEquiv (ι := ι) (A := A))
    (infinitePi_option_split μ)).symm

end ThesisCommon
