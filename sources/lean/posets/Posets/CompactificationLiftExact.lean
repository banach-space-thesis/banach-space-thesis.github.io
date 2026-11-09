import Posets.CompactificationLiftCorner

/-! The printed form of Lemma 8.3 allows a Banach algebra without a unit. -/

noncomputable section
open scoped ZeroAtInfty OnePoint

namespace Posets

variable (𝕜 : Type) [RCLike 𝕜]

/-- Lemma 8.3 with no unit assumption on the target Banach algebra. -/
def Lemma_8_3_exact (K₀ : Type) [TopologicalSpace K₀] [LocallyCompactSpace K₀] [T2Space K₀]
    (C : Type) [NonUnitalNormedRing C] [NormedSpace 𝕜 C]
    [IsScalarTower 𝕜 C C] [SMulCommClass 𝕜 C C] [CompleteSpace C]
    (Ψ : (C₀(K₀, 𝕜) →L[𝕜] C₀(K₀, 𝕜)) →ₗ[𝕜] C) : Prop :=
  IsMultiplicative 𝕜 Ψ →
  (∀ T, FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) → Ψ T = 0) →
  ∃ Φ : (C(OnePoint K₀, 𝕜) →L[𝕜] C(OnePoint K₀, 𝕜)) →ₗ[𝕜] C,
    IsMultiplicative 𝕜 Φ ∧ Set.range Φ = Set.range Ψ ∧
    (Continuous Φ ↔ Continuous Ψ) ∧ (IsCompactOperator Φ ↔ IsCompactOperator Ψ) ∧
    (Function.Surjective Ψ → Function.Surjective Φ) ∧ (¬ Continuous Ψ → ¬ Continuous Φ)

variable (K₀ : Type) [TopologicalSpace K₀] [LocallyCompactSpace K₀] [T2Space K₀]
variable (C : Type) [NonUnitalNormedRing C] [NormedSpace 𝕜 C]
  [IsScalarTower 𝕜 C C] [SMulCommClass 𝕜 C C] [CompleteSpace C]

/-- The compression and its bounded section prove all printed clauses. The
rank-one product defect is killed by the finite-rank kernel assumption. -/
theorem lemma_8_3_exact_proof (Ψ : (C₀(K₀, 𝕜) →L[𝕜] C₀(K₀, 𝕜)) →ₗ[𝕜] C) :
    Lemma_8_3_exact 𝕜 K₀ C Ψ := by
  intro hmul hfin
  let j := compactificationInclusion (𝕜 := 𝕜) K₀
  let π := compactificationProjection (𝕜 := 𝕜) K₀
  let ε : C(OnePoint K₀, 𝕜) →L[𝕜] 𝕜 := ContinuousMap.evalCLM 𝕜 ∞
  let q := cornerCompression j π
  let s := cornerCompression π j
  let Φ := Ψ.comp q.toLinearMap
  have hs (A : C₀(K₀, 𝕜) →L[𝕜] C₀(K₀, 𝕜)) : Φ (s A) = Ψ A := by
    change Ψ (cornerCompression j π (cornerCompression π j A)) = Ψ A
    rw [cornerCompression_section j π (compactificationProjection_inclusion K₀)]
  have hsFun : (fun A => Φ (s A)) = Ψ.toFun := funext hs
  have hcont : Continuous Φ ↔ Continuous Ψ := by
    constructor
    · intro h
      change Continuous Ψ.toFun
      rw [← hsFun]
      exact h.comp s.continuous
    · intro h
      exact h.comp q.continuous
  refine ⟨Φ, ?_, ?_, hcont, ?_, ?_, fun h hn => h (hcont.mp hn)⟩
  · intro T S
    change Ψ (cornerCompression j π (T * S)) = _
    rw [cornerCompression_mul j π ε 1 (compactification_decomposition K₀), map_add,
      hfin _ (finiteDimensional_range_rankOne _ _), add_zero, hmul]
    rfl
  · apply Set.Subset.antisymm
    · rintro _ ⟨T, rfl⟩
      exact ⟨q T, rfl⟩
    · rintro _ ⟨A, rfl⟩
      exact ⟨s A, hs A⟩
  · constructor
    · intro h
      change IsCompactOperator Ψ.toFun
      rw [← hsFun]
      exact h.comp_clm s
    · intro h
      exact h.comp_clm q
  · intro h c
    obtain ⟨A, hA⟩ := h c
    exact ⟨s A, (hs A).trans hA⟩

end Posets
