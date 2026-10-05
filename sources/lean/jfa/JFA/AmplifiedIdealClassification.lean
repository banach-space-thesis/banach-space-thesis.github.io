import JFA.AmplifiedIdeals
import JFA.CZeroIdeals

/-! The three closed ideals above the separable-range ideal, on the actual
amplified space. The middle ideal is expressed as the preimage of K(c₀).
Identifying it with the closure of factorisations through C₀(K_A), and
classifying the ideals below the separable-range ideal, are separate tasks. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

def amplifiedCompactPreimage (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜) :=
  amplifiedScalarQuotient h𝒜 hc hfew ⁻¹' compactOperators 𝕜 (cZero 𝕜)

theorem amplified_closedIdeal_classification_above_separable
    (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (I : Set (AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜)) :
    (IsClosedOperatorIdeal 𝕜 (AmplifiedMrowka 𝕜 𝒜) I ∧
      separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊆ I) ↔
    I = separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ∨
      I = amplifiedCompactPreimage h𝒜 hc hfew ∨ I = Set.univ := by
  let Φ := amplifiedScalarQuotient (𝕜 := 𝕜) h𝒜 hc hfew
  have hcomp : ∀ A T : AmplifiedMrowka 𝕜 𝒜 →L[𝕜] AmplifiedMrowka 𝕜 𝒜,
      Φ (A.comp T) = (Φ A).comp (Φ T) :=
    fun A T => amplifiedScalarOperator_comp h𝒜 hc hfew T A
  have hk : {T | Φ T = 0} = separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) :=
    amplifiedScalarQuotient_kernel h𝒜 hc hfew
  constructor
  · rintro ⟨hI, hsep⟩
    have hker : {T | Φ T = 0} ⊆ I := by rw [hk]; exact hsep
    let J := Φ '' I
    have hJ : IsClosedOperatorIdeal 𝕜 (cZero 𝕜) J :=
      closedOperatorIdeal_image Φ hcomp (amplifiedScalarQuotient_surjective h𝒜 hc hfew) hI hker
    have hrec : Φ ⁻¹' J = I := closedOperatorIdeal_preimage_image Φ hI hker
    rcases (cZero_closedIdeal_classification J).mp hJ with hJ0 | hJK | hJU
    · left
      rw [← hrec, hJ0]
      exact hk
    · exact Or.inr (Or.inl (hrec.symm.trans (congrArg (fun J => Φ ⁻¹' J) hJK)))
    · right; right
      rw [← hrec, hJU, preimage_univ]
  · rintro (rfl | rfl | rfl)
    · exact ⟨separableOperators_closedIdeal, Subset.rfl⟩
    · refine ⟨closedOperatorIdeal_preimage Φ hcomp compactOperators_closedIdeal, ?_⟩
      rw [← hk]
      exact closedOperatorIdeal_kernel_subset_preimage Φ compactOperators_closedIdeal
    · exact ⟨allOperators_closedIdeal, subset_univ _⟩

theorem amplified_upper_ideals_strict
    (h𝒜 : IsAlmostDisjoint 𝒜) (hc : HasContinuumSize 𝒜)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜)) :
    separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) ⊂ amplifiedCompactPreimage h𝒜 hc hfew ∧
      amplifiedCompactPreimage h𝒜 hc hfew ⊂ Set.univ := by
  let Φ := amplifiedScalarQuotient (𝕜 := 𝕜) h𝒜 hc hfew
  have hsurj := amplifiedScalarQuotient_surjective h𝒜 hc hfew
  have hpre (s t : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) (h : s ⊂ t) : Φ ⁻¹' s ⊂ Φ ⁻¹' t := by
    refine ssubset_iff_subset_ne.mpr ⟨preimage_mono h.subset, ?_⟩
    intro heq
    exact h.ne ((Set.preimage_injective.mpr hsurj) heq)
  have hk : Φ ⁻¹' ({0} : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) =
      separableOperators 𝕜 (AmplifiedMrowka 𝕜 𝒜) :=
    amplifiedScalarQuotient_kernel h𝒜 hc hfew
  obtain ⟨h0K, hKU⟩ := cZero_compact_ideal_strict (𝕜 := 𝕜)
  constructor
  · rw [← hk]
    exact hpre _ _ h0K
  · simpa only [preimage_univ] using hpre _ _ hKU

end JFA
