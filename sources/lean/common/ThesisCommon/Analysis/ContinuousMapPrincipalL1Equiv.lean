import ThesisCommon.Analysis.ContinuousMapL1DensityInjective

/-! A real principal band in the actual dual of C(K) is linearly isometric
to L1 of the generator's actual finite Riesz measure. The maps are integration
against densities and its proved inverse, rather than a representation input. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]
variable (e : C(K, ℝ) →L[ℝ] ℝ) (he : 0 ≤ e)

theorem continuousMapL1Density_mem_principalBand
    (f : Lp ℝ 1 (positiveContinuousMapRiesz e he)) :
    continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f ∈ principalBand e := by
  have hpos (g : Lp ℝ 1 (positiveContinuousMapRiesz e he)) (hg : 0 ≤ g) :
      continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) g ∈ principalBand e := by
    apply (positiveContinuousMap_mem_principalBand_iff _ e
      (continuousMapL1Density_nonneg _ g hg) he).mpr
    rw [positiveContinuousMapRiesz_L1Density _ g hg]
    exact withDensity_absolutelyContinuous _ _
  rw [← posPart_sub_negPart f, map_sub]
  exact (principalBand e).sub_mem (hpos _ (posPart_nonneg f)) (hpos _ (negPart_nonneg f))

theorem range_continuousMapL1Density_principal :
    LinearMap.range (continuousMapL1Density (𝕜 := ℝ)
      (positiveContinuousMapRiesz e he)).toLinearMap = principalBand e := by
  apply le_antisymm
  · rintro φ ⟨f, rfl⟩
    exact continuousMapL1Density_mem_principalBand e he f
  · intro φ hφ
    obtain ⟨f, hf, _⟩ := continuousMap_principalBand_density φ e he hφ
    exact ⟨f, hf⟩

theorem continuousMapL1Density_principal_norm
    (f : Lp ℝ 1 (positiveContinuousMapRiesz e he)) :
    ‖continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f‖ = ‖f‖ := by
  obtain ⟨g, hg, hn⟩ := continuousMap_principalBand_density
    (continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f) e he
    (continuousMapL1Density_mem_principalBand e he f)
  have hgf : g = f := continuousMapL1Density_injective _ hg
  exact (hgf ▸ hn).symm

def continuousMapPrincipalL1Isometry :
    Lp ℝ 1 (positiveContinuousMapRiesz e he) →ₗᵢ[ℝ] principalBand e where
  toFun f := ⟨continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f,
    continuousMapL1Density_mem_principalBand e he f⟩
  map_add' f g := Subtype.ext (map_add _ f g)
  map_smul' c f := Subtype.ext (map_smul _ c f)
  norm_map' := continuousMapL1Density_principal_norm e he

theorem continuousMapPrincipalL1Isometry_surjective :
    Function.Surjective (continuousMapPrincipalL1Isometry e he) := by
  intro φ
  obtain ⟨f, hf, _⟩ := continuousMap_principalBand_density
    (φ.val : C(K, ℝ) →L[ℝ] ℝ) e he φ.property
  exact ⟨f, Subtype.ext hf⟩

def continuousMapPrincipalL1Equiv :
    Lp ℝ 1 (positiveContinuousMapRiesz e he) ≃ₗᵢ[ℝ] principalBand e :=
  LinearIsometryEquiv.ofSurjective (continuousMapPrincipalL1Isometry e he)
    (continuousMapPrincipalL1Isometry_surjective e he)

theorem continuousMapPrincipalL1Equiv_apply
    (f : Lp ℝ 1 (positiveContinuousMapRiesz e he)) (g : C(K, ℝ)) :
    ((continuousMapPrincipalL1Equiv e he f : principalBand e) : C(K, ℝ) →L[ℝ] ℝ) g =
      ∫ x, f x * g x ∂positiveContinuousMapRiesz e he :=
  continuousMapL1Density_apply _ f g

theorem continuousMapPrincipalL1Equiv_nonneg_iff
    (f : Lp ℝ 1 (positiveContinuousMapRiesz e he)) :
    0 ≤ continuousMapPrincipalL1Equiv e he f ↔ 0 ≤ f := by
  constructor
  · intro hf
    obtain ⟨g, hg, hmap, _⟩ := positiveContinuousMap_principalBand_density
      (continuousMapL1Density (𝕜 := ℝ) (positiveContinuousMapRiesz e he) f) e hf he
      (continuousMapL1Density_mem_principalBand e he f)
    have hgf : g = f := continuousMapL1Density_injective _ hmap
    exact hgf ▸ hg
  · intro hf
    exact continuousMapL1Density_nonneg _ f hf

end ThesisCommon
