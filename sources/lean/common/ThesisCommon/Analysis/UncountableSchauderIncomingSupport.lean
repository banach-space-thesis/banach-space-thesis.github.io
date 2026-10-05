import ThesisCommon.Analysis.UncountableSchauderFunctionalSupport
import ThesisCommon.Analysis.CountableTotalDual

/-! A countable total dual set turns scalar incoming support bounds into
an operator support bound, by the countable-union argument of Lemma 4.18. -/
noncomputable section
namespace ThesisCommon
namespace UncountableSchauderSum
variable {𝕜 Γ E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {b : NormalizedSchauderFamily 𝕜 Γ E}

theorem operator_countable_incoming_support (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne) (htotal : HasCountableTotalDual 𝕜 X)
    (T : UncountableSchauderSum b hs.1 X →L[𝕜] X) :
    ∃ Δ : Set Γ, Δ.Countable ∧ ∀ γ ∉ Δ,
      T.comp (coordinateProjection {γ}) = 0 := by
  classical
  obtain ⟨M, hM, hsep⟩ := htotal
  letI : Countable M := hM.to_subtype
  choose Δ hΔc hΔzero using fun φ : M =>
    functional_countable_coordinate_support hs hnot (φ.val.comp T)
  refine ⟨⋃ φ : M, Δ φ, Set.countable_iUnion hΔc, ?_⟩
  intro γ hγ
  apply ContinuousLinearMap.ext
  intro x
  apply hsep
  intro φ hφ
  have hγφ : γ ∉ Δ ⟨φ, hφ⟩ := fun h => hγ (Set.mem_iUnion.mpr ⟨⟨φ, hφ⟩, h⟩)
  exact DFunLike.congr_fun (hΔzero ⟨φ, hφ⟩ γ hγφ) x

end UncountableSchauderSum
end ThesisCommon
