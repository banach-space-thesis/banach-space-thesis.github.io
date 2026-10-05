import ThesisCommon.Analysis.ALHomogeneousBooleanIsometry
import ThesisCommon.Analysis.ALPrincipalBandIsoTransport
import ThesisCommon.Analysis.ALFragmentNormalization

/-! Homogeneous principal AL bands of equal infinite density are actually
ordered linearly isometric. Normalizing their positive generators removes
the irrelevant difference in their total fragment masses. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  [HasSolidNorm E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F]
  [HasSolidNorm F] [CompleteSpace F]
variable (hE : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (hF : ∀ x y : F, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
  (e : E) (f : F) [Fact (0 ≤ e)] [Fact (0 ≤ f)]

include hE hF in
theorem exists_ordered_principalBand_isometry_of_homogeneous
    (he : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra e))
    (hf : IsDensityHomogeneous (⊤ : PositiveFragmentAlgebra f))
    (hden : topologicalDensity (PositiveFragmentAlgebra e) =
      topologicalDensity (PositiveFragmentAlgebra f))
    (hinfinite : ℵ₀ ≤ topologicalDensity (PositiveFragmentAlgebra e)) :
    ∃ d : principalBand e ≃ₗᵢ[ℝ] principalBand f, ∀ x, 0 ≤ d x ↔ 0 ≤ x := by
  have he0 : e ≠ 0 := by
    intro hz
    apply he.1
    apply positiveFragmentValue_injective e
    simpa only [positiveFragmentValue_top, positiveFragmentValue_bot] using hz
  have hf0 : f ≠ 0 := by
    intro hz
    apply hf.1
    apply positiveFragmentValue_injective f
    simpa only [positiveFragmentValue_top, positiveFragmentValue_bot] using hz
  have heh := (isDensityHomogeneous_top_normalized_iff e he0).mpr he
  have hfh := (isDensityHomogeneous_top_normalized_iff f hf0).mpr hf
  obtain ⟨q, hq⟩ := exists_isometric_booleanOrderIso_of_homogeneous hE hF
    (normalizedPositiveVector e) (normalizedPositiveVector f) heh hfh
    (by rw [norm_normalizedPositiveVector e he0, norm_normalizedPositiveVector f hf0])
    (by simpa only [topologicalDensity_positiveFragment_normalized e he0,
      topologicalDensity_positiveFragment_normalized f hf0] using hden)
    (by simpa only [topologicalDensity_positiveFragment_normalized e he0] using hinfinite)
  let de := LinearIsometryEquiv.ofEq (principalBand (normalizedPositiveVector e))
    (principalBand e) (principalBand_normalizedPositiveVector e he0)
  let df := LinearIsometryEquiv.ofEq (principalBand (normalizedPositiveVector f))
    (principalBand f) (principalBand_normalizedPositiveVector f hf0)
  let dn := alPrincipalBandEquivOfIsometricFragmentIso hE hF
    (normalizedPositiveVector e) (normalizedPositiveVector f) q hq
  refine ⟨de.symm.trans (dn.trans df), ?_⟩
  intro x
  change 0 ≤ dn (de.symm x) ↔ 0 ≤ x
  rw [alPrincipalBandEquivOfIsometricFragmentIso_nonneg]
  rfl

end ThesisCommon
