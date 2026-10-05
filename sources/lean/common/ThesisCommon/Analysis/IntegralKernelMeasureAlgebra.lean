import ThesisCommon.Analysis.MeasureAlgebraCoding
import ThesisCommon.Analysis.IntegralKernelMeasurePreserving
import ThesisCommon.Analysis.IntegralKernelModulus

/-! Explicit transport of jointly measurable real kernels and their large-value
truncations under arbitrary finite measure-algebra isomorphisms. Countable
generation is required only on the original spaces. Replacement spaces are
handled by the Cantor maps constructed from the measure-algebra isomorphisms. -/
noncomputable section
open Set MeasureTheory MeasurableSpace Filter

namespace ThesisCommon
variable {X Y X' Y' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [MeasurableSpace X'] [MeasurableSpace Y']
variable {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
variable [CountablyGenerated X] [CountablyGenerated Y]

/-- The transported kernel represents the conjugated operator on every L1
input, and all signed large-value truncations are exactly conjugated too. -/
theorem IsIntegralKernel.exists_measureAlgebra_transport
    (Φ : MeasureAlgebraIso μ μ') (Ψ : MeasureAlgebraIso ν ν')
    {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hk : IsIntegralKernel k K) :
    ∃ (h : X' × Y' → ℝ)
      (hh : IsIntegralKernel h (operatorTransport Φ.lOneEquiv Ψ.lOneEquiv K)),
      ∀ r : ℝ, hh.truncatedOperator r =
        operatorTransport Φ.lOneEquiv Ψ.lOneEquiv (hk.truncatedOperator r) := by
  let eX : Lp ℝ 1 (μ.map (mapNatBool X)) ≃ₗᵢ[ℝ] Lp ℝ 1 μ :=
    lpComapEquiv μ (mapNatBool X) (measurable_mapNatBool X) (comap_mapNatBool X) 1
  let eY : Lp ℝ 1 (ν.map (mapNatBool Y)) ≃ₗᵢ[ℝ] Lp ℝ 1 ν :=
    lpComapEquiv ν (mapNatBool Y) (measurable_mapNatBool Y) (comap_mapNatBool Y) 1
  let eX' := eX.trans Φ.lOneEquiv
  let eY' := eY.trans Ψ.lOneEquiv
  have hX : ∀ f, eX f =ᵐ[μ] f ∘ mapNatBool X :=
    lpComapEquiv_coe μ (mapNatBool X) (measurable_mapNatBool X) (comap_mapNatBool X) 1
  have hY : ∀ g, eY g =ᵐ[ν] g ∘ mapNatBool Y :=
    lpComapEquiv_coe ν (mapNatBool Y) (measurable_mapNatBool Y) (comap_mapNatBool Y) 1
  have hX' : ∀ f, eX' f =ᵐ[μ'] f ∘ Φ.cantorCoding := Φ.lOneEquiv_cantor_pullback_coe
  have hY' : ∀ g, eY' g =ᵐ[ν'] g ∘ Ψ.cantorCoding := Ψ.lOneEquiv_cantor_pullback_coe
  have hcomp (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
      operatorTransport eX' eY' (operatorTransport eX.symm eY.symm T) =
        operatorTransport Φ.lOneEquiv Ψ.lOneEquiv T := by
    ext f
    simp [operatorTransport_apply, eX', eY']
  have hdescend (q : (ℕ → Bool) × (ℕ → Bool) → ℝ) (hq : Measurable q)
      (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
      (hT : IsIntegralKernel (pullbackKernel (mapNatBool X) (mapNatBool Y) q) T) :
      IsIntegralKernel q (operatorTransport eX.symm eY.symm T) := by
    apply (isIntegralKernel_measurePreserving_transport_iff (mapNatBool X) (mapNatBool Y)
      ⟨measurable_mapNatBool X, rfl⟩ ⟨measurable_mapNatBool Y, rfl⟩
      eX eY hX hY hq (operatorTransport eX.symm eY.symm T)).mp
    have hback : operatorTransport eX eY (operatorTransport eX.symm eY.symm T) = T := by
      ext f
      simp [operatorTransport_apply]
    rw [hback]
    exact hT
  obtain ⟨q, hq, hkq⟩ := exists_pullbackKernel (mapNatBool X) (mapNatBool Y)
    (comap_mapNatBool X) (comap_mapNatBool Y) k hk.measurable
  have hbase : IsIntegralKernel q (operatorTransport eX.symm eY.symm K) := by
    apply hdescend q hq K
    rw [← hkq]
    exact hk
  have hnew : IsIntegralKernel (pullbackKernel Φ.cantorCoding Ψ.cantorCoding q)
      (operatorTransport Φ.lOneEquiv Ψ.lOneEquiv K) := by
    have h := hbase.measurePreserving_transport Φ.cantorCoding Ψ.cantorCoding
      Φ.cantorCoding_measurePreserving Ψ.cantorCoding_measurePreserving eX' eY' hX' hY'
    rwa [hcomp] at h
  refine ⟨pullbackKernel Φ.cantorCoding Ψ.cantorCoding q, hnew, ?_⟩
  intro r
  have htrbase : IsIntegralKernel (truncatedKernel r q)
      (operatorTransport eX.symm eY.symm (hk.truncatedOperator r)) := by
    apply hdescend (truncatedKernel r q) (measurable_truncatedKernel hq r)
    rw [pullbackKernel_truncatedKernel, ← hkq]
    exact hk.truncatedOperator_represents r
  have htrnew := htrbase.measurePreserving_transport Φ.cantorCoding Ψ.cantorCoding
    Φ.cantorCoding_measurePreserving Ψ.cantorCoding_measurePreserving eX' eY' hX' hY'
  rw [pullbackKernel_truncatedKernel, hcomp] at htrnew
  exact (hnew.truncatedOperator_represents r).unique htrnew

theorem IsIntegralOperator.measureAlgebra_transport
    (Φ : MeasureAlgebraIso μ μ') (Ψ : MeasureAlgebraIso ν ν')
    {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν} (hK : IsIntegralOperator K) :
    IsIntegralOperator (operatorTransport Φ.lOneEquiv Ψ.lOneEquiv K) := by
  obtain ⟨k, hk⟩ := hK
  obtain ⟨h, hh, _⟩ := hk.exists_measureAlgebra_transport Φ Ψ
  exact ⟨h, hh⟩

end ThesisCommon
