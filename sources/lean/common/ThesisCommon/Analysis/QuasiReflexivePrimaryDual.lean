import ThesisCommon.Analysis.QuasiReflexiveTransport
import ThesisCommon.Analysis.HyperplaneTransport
import ThesisCommon.Analysis.DualDirectSums
import ThesisCommon.Analysis.PrimaryDirectSum

/-! Primariness of the actual continuous dual under the hypotheses of
Appendix B.3. The chosen projection summands carry their inherited norms.
Their finite defect follows from the genuine residuum product isomorphism.
-/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
namespace ThesisCommon
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- A product summand of a space of finite quasi-reflexive order has finite
defect, by the actual quotient product decomposition. -/
theorem finiteDimensional_residuum_summands {n : ℕ}
    (h : IsQuasiReflexiveOfOrder 𝕜 X n) (e : X ≃L[𝕜] Y × Z) :
    FiniteDimensional 𝕜 (ResiduumSpace 𝕜 Y) ∧
      FiniteDimensional 𝕜 (ResiduumSpace 𝕜 Z) := by
  letI := h.finiteDimensional
  let a := (residuumEquiv e).trans (residuumProductEquiv (𝕜 := 𝕜) (E := Y) (F := Z))
  letI : FiniteDimensional 𝕜 (ResiduumSpace 𝕜 Y × ResiduumSpace 𝕜 Z) :=
    a.toLinearEquiv.finiteDimensional
  constructor
  · exact FiniteDimensional.of_injective
      (LinearMap.inl 𝕜 (ResiduumSpace 𝕜 Y) (ResiduumSpace 𝕜 Z))
      (by intro x y hxy; exact congrArg Prod.fst hxy)
  · exact FiniteDimensional.of_injective
      (LinearMap.inr 𝕜 (ResiduumSpace 𝕜 Y) (ResiduumSpace 𝕜 Z))
      (by intro x y hxy; exact congrArg Prod.snd hxy)

/-- The source's summand argument for an arbitrary actual product
decomposition of the continuous dual. -/
theorem primary_dual_summands_of_quasi_reflexive_orderOne
    (hq : IsQuasiReflexiveOfOrderOne 𝕜 X) (hp : IsPrimary 𝕜 X)
    (hh : IsIsomorphicToEveryHyperplane 𝕜 X)
    (hdual : IsIsomorphicToEveryHyperplane 𝕜 (StrongDual 𝕜 X))
    (d : StrongDual 𝕜 X ≃L[𝕜] Y × Z) :
    Nonempty (StrongDual 𝕜 X ≃L[𝕜] Y) ∨ Nonempty (StrongDual 𝕜 X ≃L[𝕜] Z) := by
  let a : StrongDual 𝕜 (StrongDual 𝕜 X) ≃L[𝕜] StrongDual 𝕜 (Y × Z) :=
    banachDualEquiv (𝕜 := 𝕜) (E := StrongDual 𝕜 X) (F := Y × Z) d
  let b : X ≃L[𝕜] (StrongDual 𝕜 Y × StrongDual 𝕜 Z) :=
    (hq.bidualSelfEquiv hh).symm.trans
      (a.trans (banachDualProductEquiv (𝕜 := 𝕜) (E := Y) (F := Z)))
  have hfinite := finiteDimensional_residuum_summands hq.dual d
  letI : FiniteDimensional 𝕜 (ResiduumSpace 𝕜 Y) := hfinite.1
  letI : FiniteDimensional 𝕜 (ResiduumSpace 𝕜 Z) := hfinite.2
  rcases primary_product_summand hp b with hY | hZ
  · obtain ⟨e⟩ := hY
    have hY : IsQuasiReflexiveOfOrderOne 𝕜 Y := (hq.of_equiv e).of_dual
    obtain ⟨a⟩ := nonempty_equiv_of_bidual_equiv hY hdual
      (banachDualEquiv (𝕜 := 𝕜) (E := X) (F := StrongDual 𝕜 Y) e).symm
    exact Or.inl ⟨a.symm⟩
  · obtain ⟨e⟩ := hZ
    have hZ : IsQuasiReflexiveOfOrderOne 𝕜 Z := (hq.of_equiv e).of_dual
    obtain ⟨a⟩ := nonempty_equiv_of_bidual_equiv hZ hdual
      (banachDualEquiv (𝕜 := 𝕜) (E := X) (F := StrongDual 𝕜 Z) e).symm
    exact Or.inr ⟨a.symm⟩

/-- Proposition B.3 on actual Banach spaces and canonical duals. -/
theorem primary_dual_of_quasi_reflexive_orderOne
    (hq : IsQuasiReflexiveOfOrderOne 𝕜 X) (hp : IsPrimary 𝕜 X)
    (hh : IsIsomorphicToEveryHyperplane 𝕜 X)
    (hdual : IsIsomorphicToEveryHyperplane 𝕜 (StrongDual 𝕜 X)) :
    IsPrimary 𝕜 (StrongDual 𝕜 X) := by
  intro P hP
  let Y := LinearMap.range P.toLinearMap
  let Z := LinearMap.range (ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 X) - P).toLinearMap
  letI : CompleteSpace Y := (projectionRange_isClosed P hP).completeSpace_coe
  letI : CompleteSpace Z := (projectionComplementRange_isClosed P hP).completeSpace_coe
  exact primary_dual_summands_of_quasi_reflexive_orderOne hq hp hh hdual
    (projectionRangeComplementEquiv P hP)

end ThesisCommon
