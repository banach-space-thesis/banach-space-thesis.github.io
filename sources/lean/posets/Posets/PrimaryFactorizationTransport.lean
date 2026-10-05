import ThesisCommon.Analysis.PrimaryIsomorphism

/-! Isomorphic transport of primary factorisation without a uniform bound. -/
noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem hasPFP_of_equiv (h : HasPFP 𝕜 X) (e : X ≃L[𝕜] Y) : HasPFP 𝕜 Y := by
  intro T
  let A := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  have hAB : A.comp B = ContinuousLinearMap.id 𝕜 X := by
    ext x
    exact e.symm_apply_apply x
  have liftFactor (S : Y →L[𝕜] Y)
      (hS : FactorsIdentity ((A.comp S).comp B) X) : FactorsIdentity S Y := by
    obtain ⟨C, _, hC⟩ := (factorsIdentity_iff_exists_bound _).mp hS
    exact ((hC.of_compression A B).target_equiv e).forget_bound
  rcases h ((A.comp T).comp B) with hT | hT
  · exact Or.inl (liftFactor T hT)
  · apply Or.inr
    apply liftFactor (ContinuousLinearMap.id 𝕜 Y - T)
    rwa [compression_complement T A B hAB]

end Posets
