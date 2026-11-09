import PEMS.Section44Decomposition
import ThesisCommon.Analysis.L1OperatorRangeFactor

/-! Existence of the decomposition and supported kernels constructed in §4.4. -/
noncomputable section
open MeasureTheory Set ThesisCommon
open scoped ENNReal Function

namespace PEMS

universe u
variable {X : Type u} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem exists_section44_decomposition (hμ : StrictlyLocalizable μ)
    (_hν : StrictlyLocalizable ν) (T : LOne ℝ μ →L[ℝ] LOne ℝ ν) :
    ∃ I : Type u, Nonempty (Section44Decomposition I T) := by
  classical
  let I := strictlyLocalizableParts hμ
  let D : Section44Partition I μ :=
    { piece := Subtype.val
      measurable := strictlyLocalizablePart_measurable hμ
      finite := strictlyLocalizablePart_finite hμ
      disjoint := strictlyLocalizableParts_disjoint hμ
      covers := by simpa only [iUnion_subtype] using hμ.choose_spec.2.2.1
      measurable_of_pieces := fun A hA =>
        (hμ.choose_spec.2.2.2.1 A).mpr fun B hB => hA ⟨B, hB⟩
      sum_restrict := strictlyLocalizable_sum_restrict hμ }
  have piece (i : I) :
      ∃ (A : Set Y) (hA : MeasurableSet A), SigmaFinite (ν.restrict A) ∧
        ∃ (S K : LOne ℝ (μ.restrict (D.piece i)) →L[ℝ] LOne ℝ (ν.restrict A))
          (k : X × Y → ℝ), IsSingularOperator S ∧ IsIntegralKernel k K ∧
            (∀ x y, y ∉ A → k (x, y) = 0) ∧
            T.comp (D.includePiece i) =
              (lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp (S + K) := by
    letI := D.finitePiece i
    obtain ⟨A, hA, hσ, R, hR, _⟩ :=
      exists_sigmaFinite_lOneOperator_range_factor (T.comp (D.includePiece i))
    letI := hσ
    obtain ⟨⟨K, S⟩, ⟨⟨k, hk⟩, hS, hsum⟩, _⟩ :=
      exists_unique_integral_singular_decomposition R
    have hrestore : (lebesgueLpRestrict (𝕜 := ℝ) A).comp
        ((lebesgueLpExtend (𝕜 := ℝ) A hA).toContinuousLinearMap.comp K) = K := by
      ext f : 1
      exact lebesgueLpRestrict_extend (𝕜 := ℝ) A hA (K f)
    have hk' := section44_kernel_restrict (section44_kernel_extend A hA hk) A
    rw [hrestore] at hk'
    refine ⟨A, hA, hσ, S, K, (univ ×ˢ A).indicator k, hS, hk', ?_, ?_⟩
    · intro x y hy
      simp [hy]
    · change R = K + S at hsum
      rw [add_comm S K, ← hsum]
      exact hR.symm
  choose support hmeas hσ S K k hS hk hzero hsum using piece
  exact ⟨I, ⟨{
    partition := D
    support := support
    measurable_support := hmeas
    sigmaFinite_support := hσ
    singularPart := S
    integralPart := K
    kernel := k
    singular := hS
    represents := hk
    kernel_zero_off := hzero
    decompose := hsum }⟩⟩

end PEMS
