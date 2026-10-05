import ThesisCommon.Analysis.ContinuousMapComplexPrincipalBand

/-! A complex principal band is L1 of the actual finite Riesz measure of
its positive real generator. The isometry is the density-integral map. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]
variable (e : C(K, ℝ) →L[ℝ] ℝ) (he : 0 ≤ e)

theorem continuousMapL1Density_principal_le_iff
    (f g : Lp ℝ 1 (positiveContinuousMapRiesz e he)) :
    continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f ≤
      continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) g ↔ f ≤ g := by
  have h := continuousMapPrincipalL1Equiv_nonneg_iff e he (g - f)
  change 0 ≤ continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) (g-f) ↔ _ at h
  simpa only [map_sub, sub_nonneg] using h

theorem continuousMapComplexL1Density_mem_principalBand
    (f : Lp ℂ 1 (positiveContinuousMapRiesz e he)) :
    continuousMapL1Density (𝕜 := ℂ) (positiveContinuousMapRiesz e he) f ∈
      continuousMapComplexPrincipalBand e := by
  constructor
  · rw [continuousMapDualRe_L1Density]
    exact continuousMapL1Density_mem_principalBand e he _
  · rw [continuousMapDualIm_L1Density]
    exact continuousMapL1Density_mem_principalBand e he _

theorem continuousMapComplexModulus_L1Density
    (f : Lp ℂ 1 (positiveContinuousMapRiesz e he)) :
    continuousMapComplexModulus (continuousMapL1Density (𝕜 := ℂ)
      (positiveContinuousMapRiesz e he) f) =
      continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) (complexL1Modulus f) := by
  let μ := positiveContinuousMapRiesz e he
  let φ := continuousMapL1Density (𝕜 := ℂ) μ f
  have hphase (c : ℂ) : continuousMapDualRe (c • φ) =
      continuousMapL1Density (𝕜 := ℝ) μ (complexL1Re μ (c • f)) := by
    rw [← map_smul, continuousMapDualRe_L1Density]
  apply le_antisymm
  · apply (continuousMapComplexModulus_isLUB φ).2
    rintro _ ⟨c, hc, rfl⟩
    rw [hphase]
    exact (continuousMapL1Density_principal_le_iff e he _ _).mpr
      (complexL1Re_phase_le f c hc.le)
  · have hm : continuousMapComplexModulus φ ∈ principalBand e :=
      (continuousMapComplexPrincipalBand_mem_iff_modulus e φ).mp
        (continuousMapComplexL1Density_mem_principalBand e he f)
    obtain ⟨g, hg, _⟩ := continuousMap_principalBand_density
      (continuousMapComplexModulus φ) e he hm
    rw [← hg]
    apply (continuousMapL1Density_principal_le_iff e he _ _).mpr
    apply (complexL1Modulus_isLUB f).2
    rintro _ ⟨c, hc, rfl⟩
    apply (continuousMapL1Density_principal_le_iff e he _ _).mp
    rw [hg, ← hphase]
    exact continuousMapDualRe_phase_le φ c hc.le

theorem continuousMapComplexL1Density_principal_norm
    (f : Lp ℂ 1 (positiveContinuousMapRiesz e he)) :
    ‖continuousMapL1Density (𝕜 := ℂ) (positiveContinuousMapRiesz e he) f‖ = ‖f‖ := by
  rw [← norm_continuousMapComplexModulus, continuousMapComplexModulus_L1Density e he,
    continuousMapL1Density_principal_norm e he, norm_complexL1Modulus]

def continuousMapComplexPrincipalL1Isometry :
    Lp ℂ 1 (positiveContinuousMapRiesz e he) →ₗᵢ[ℂ] continuousMapComplexPrincipalBand e where
  toFun f := ⟨continuousMapL1Density (𝕜 := ℂ) (positiveContinuousMapRiesz e he) f,
    continuousMapComplexL1Density_mem_principalBand e he f⟩
  map_add' f g := Subtype.ext (map_add _ f g)
  map_smul' c f := Subtype.ext (map_smul _ c f)
  norm_map' := continuousMapComplexL1Density_principal_norm e he

theorem continuousMapComplexPrincipalL1Isometry_surjective :
    Function.Surjective (continuousMapComplexPrincipalL1Isometry e he) := by
  intro φ
  obtain ⟨f, hf, _⟩ := continuousMap_principalBand_density
    (continuousMapDualRe φ.val) e he φ.property.1
  obtain ⟨g, hg, _⟩ := continuousMap_principalBand_density
    (continuousMapDualIm φ.val) e he φ.property.2
  refine ⟨complexL1OfReal _ f + Complex.I • complexL1OfReal _ g, ?_⟩
  apply Subtype.ext
  change continuousMapL1Density (𝕜 := ℂ) (positiveContinuousMapRiesz e he) _ = φ.val
  rw [map_add, map_smul, continuousMapL1Density_ofReal, continuousMapL1Density_ofReal, hf, hg]
  exact continuousMapDual_decomposition φ.val

def continuousMapComplexPrincipalL1Equiv :
    Lp ℂ 1 (positiveContinuousMapRiesz e he) ≃ₗᵢ[ℂ] continuousMapComplexPrincipalBand e :=
  LinearIsometryEquiv.ofSurjective (continuousMapComplexPrincipalL1Isometry e he)
    (continuousMapComplexPrincipalL1Isometry_surjective e he)

theorem continuousMapComplexPrincipalL1Equiv_apply
    (f : Lp ℂ 1 (positiveContinuousMapRiesz e he)) (g : C(K, ℂ)) :
    ((continuousMapComplexPrincipalL1Equiv e he f : continuousMapComplexPrincipalBand e) :
      C(K, ℂ) →L[ℂ] ℂ) g = ∫ x, f x * g x ∂positiveContinuousMapRiesz e he :=
  continuousMapL1Density_apply _ f g

end ThesisCommon
