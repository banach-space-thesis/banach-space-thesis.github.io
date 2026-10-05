import JFA.Definitions
import ThesisCommon.Analysis.CZeroOperators

/-! The product of two discrete C₀ spaces with countable index sets embeds
complementably in scalar c₀. An injective numbering of the disjoint union
gives disjoint coordinate images and explicit zero-extension/read maps. -/

noncomputable section
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]

theorem cZeroRestrict_extend_zero {ι κ ν : Type*}
    [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace κ] [DiscreteTopology κ]
    [TopologicalSpace ν] [DiscreteTopology ν]
    (eI : ι ↪ ν) (eK : κ ↪ ν) (hne : ∀ i k, eI i ≠ eK k) :
    (ThesisCommon.cZeroRestrict (𝕜 := 𝕜) (X := 𝕜) eI).comp (ThesisCommon.cZeroExtend eK) = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply ZeroAtInftyContinuousMap.ext
  intro i
  change Function.extend eK f 0 (eI i) = 0
  have hn : ¬ ∃ k, eK k = eI i := by
    rintro ⟨k, hk⟩
    exact hne i k hk.symm
  simp only [Function.extend_apply' _ _ _ hn, Pi.zero_apply]

theorem exists_countable_czero_product_retract {ι κ : Type*} [Countable ι] [Countable κ]
    [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace κ] [DiscreteTopology κ] :
    ∃ A : (C₀(ι, 𝕜) × C₀(κ, 𝕜)) →L[𝕜] cZero 𝕜,
    ∃ B : cZero 𝕜 →L[𝕜] (C₀(ι, 𝕜) × C₀(κ, 𝕜)),
      B.comp A = ContinuousLinearMap.id 𝕜 (C₀(ι, 𝕜) × C₀(κ, 𝕜)) := by
  obtain ⟨code, hcode⟩ := exists_injective_nat (ι ⊕ κ)
  let eI : ι ↪ ℕ := ⟨fun i => code (Sum.inl i), hcode.comp Sum.inl_injective⟩
  let eK : κ ↪ ℕ := ⟨fun k => code (Sum.inr k), hcode.comp Sum.inr_injective⟩
  have hne (i : ι) (k : κ) : eI i ≠ eK k := fun h => Sum.noConfusion (hcode h)
  let AI := ThesisCommon.cZeroExtend (𝕜 := 𝕜) (X := 𝕜) eI
  let AK := ThesisCommon.cZeroExtend (𝕜 := 𝕜) (X := 𝕜) eK
  let BI := ThesisCommon.cZeroRestrict (𝕜 := 𝕜) (X := 𝕜) eI
  let BK := ThesisCommon.cZeroRestrict (𝕜 := 𝕜) (X := 𝕜) eK
  have hII := ThesisCommon.cZeroRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜) eI
  have hKK := ThesisCommon.cZeroRestrict_comp_extend (𝕜 := 𝕜) (X := 𝕜) eK
  have hIK := cZeroRestrict_extend_zero (𝕜 := 𝕜) eI eK hne
  have hKI := cZeroRestrict_extend_zero (𝕜 := 𝕜) eK eI (fun k i => (hne i k).symm)
  refine ⟨AI.coprod AK, BI.prod BK, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · change BI (AI x.1 + AK x.2) = x.1
    rw [map_add]
    have h1 : BI (AI x.1) = x.1 := congrArg (fun L => L x.1) hII
    have h2 : BI (AK x.2) = 0 := congrArg (fun L => L x.2) hIK
    rw [h1, h2, add_zero]
  · change BK (AI x.1 + AK x.2) = x.2
    rw [map_add]
    have h1 : BK (AI x.1) = 0 := congrArg (fun L => L x.1) hKI
    have h2 : BK (AK x.2) = x.2 := congrArg (fun L => L x.2) hKK
    rw [h1, h2, zero_add]

end JFA
