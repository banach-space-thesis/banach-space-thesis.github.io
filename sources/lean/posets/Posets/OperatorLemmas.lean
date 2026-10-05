import Posets.Definitions

noncomputable section
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem factorsThroughCZero_zero : FactorsThroughCZero 𝕜 (0 : E →L[𝕜] F) :=
  ⟨0, 0, by ext; rfl⟩

theorem FactorsThroughCZero.comp_left {T : E →L[𝕜] F} (h : FactorsThroughCZero 𝕜 T)
    (U : F →L[𝕜] G) : FactorsThroughCZero 𝕜 (U.comp T) := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A, U.comp B, rfl⟩

theorem FactorsThroughCZero.comp_right {T : F →L[𝕜] G} (h : FactorsThroughCZero 𝕜 T)
    (U : E →L[𝕜] F) : FactorsThroughCZero 𝕜 (T.comp U) := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A.comp U, B, rfl⟩

/-- Definition 6.1's coherence and isometry already force ι_tt=id; no extra
diagonal condition is necessary in the definition. -/
theorem fewOperators_self {P : Type*} [PartialOrder P] {X : P → Type*}
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]
    {ι : ∀ s t, X s →L[𝕜] X t} (h : FewOperators 𝕜 X ι) (t : P) :
    ι t t = ContinuousLinearMap.id 𝕜 (X t) := by
  ext x
  apply (h.2.1 t t le_rfl).injective
  exact congrArg (fun T : X t →L[𝕜] X t => T x) (h.2.2.1 t t t le_rfl le_rfl)

end Posets
