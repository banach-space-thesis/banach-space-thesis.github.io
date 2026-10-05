import ThesisCommon.Analysis.JamesSequenceLpCopy
import ThesisCommon.Analysis.SequenceSumEquivs
import ThesisCommon.Analysis.ScalarExtensionDual

/-! Actual James spaces and their continuous duals absorb a scalar dimension
and are isomorphic to each closed hyperplane. Quasi-reflexivity is not assumed
or proved here; the only ingredients are the concrete complemented lp copy
and the explicit scalar absorption construction. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem jamesSequence_scalarExtension (p : BanachExponent) (hp : p.val ≠ ⊤) :
    IsIsomorphicToScalarExtension 𝕜 (JamesSequenceSpace 𝕜 p) := by
  let e := jamesLpRangeEquiv (𝕜 := 𝕜) p hp
  let a : SequenceSum p 𝕜 ≃L[𝕜] (SequenceSum p 𝕜 × 𝕜) :=
    (lpHeadTailEquiv (𝕜 := 𝕜) (X := 𝕜) p.val).trans
      (ContinuousLinearEquiv.prodComm 𝕜 𝕜 (SequenceSum p 𝕜))
  apply scalarExtension_of_complemented_subspace (jamesLpRange (𝕜 := 𝕜) p hp)
    (jamesLpRange_closedComplemented p hp)
  exact ⟨e.symm.trans (a.trans (e.prodCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)))⟩

theorem jamesSequence_everyHyperplane (p : BanachExponent) (hp : p.val ≠ ⊤) :
    IsIsomorphicToEveryHyperplane 𝕜 (JamesSequenceSpace 𝕜 p) :=
  (jamesSequence_scalarExtension (𝕜 := 𝕜) p hp).everyHyperplane

theorem jamesSequence_dual_everyHyperplane (p : BanachExponent) (hp : p.val ≠ ⊤) :
    IsIsomorphicToEveryHyperplane 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p)) :=
  (jamesSequence_scalarExtension (𝕜 := 𝕜) p hp).dual.everyHyperplane

end ThesisCommon
