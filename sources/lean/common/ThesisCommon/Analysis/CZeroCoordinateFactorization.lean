import ThesisCommon.Analysis.CZeroArbitrarySingles
import ThesisCommon.Analysis.CZeroOperators
import ThesisCommon.Analysis.FactorNormalization
import ThesisCommon.Analysis.CardinalFactorSelection

/-! Actual arbitrary-index c₀ coordinate compression and normalized factor
assembly. Coordinate formulas on all vectors follow from the finite-subset
singleton expansion. -/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty BigOperators
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def cZeroCoordinateEntry (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (β α : Γ) : X →L[𝕜] X :=
  ((cZeroCoordinate β).comp T).comp (cZeroSingleAtL α)

@[simp] theorem cZeroCoordinateEntry_apply
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (β α : Γ) (x : X) :
    cZeroCoordinateEntry T β α x = T (cZeroSingleAt α x) β := rfl

theorem cZeroCoordinateProjection_singleton (α : Γ) (x : C₀(Γ, X)) :
    cZeroCoordinateProjection (𝕜 := 𝕜) {α} x = cZeroSingleAt α (x α) := by
  ext γ
  by_cases h : γ = α
  · subst γ; simp
  · simp [cZeroCoordinateProjection_apply, cZeroSingleAt_apply, h]

theorem cZero_coordinate_diagonal_on_support
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp T).comp
        (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0)
    (x : C₀(Γ, X)) (hx : ∀ γ ∉ Λ, x γ = 0) {α : Γ} (hα : α ∈ Λ) :
    T x α = cZeroCoordinateEntry T α α (x α) := by
  let L := (cZeroCoordinate (𝕜 := 𝕜) α).comp T
  let R := (cZeroCoordinateEntry T α α).comp (cZeroCoordinate α)
  have hsingle (γ : Γ) : L (cZeroSingleAt γ (x γ)) = R (cZeroSingleAt γ (x γ)) := by
    change T (cZeroSingleAt γ (x γ)) α =
      cZeroCoordinateEntry T α α ((cZeroSingleAt γ (x γ)) α)
    by_cases hγα : γ = α
    · subst γ; simp
    · by_cases hγ : γ ∈ Λ
      · have hz := congrArg (fun S : C₀(Γ, X) →L[𝕜] C₀(Γ, X) =>
          S (cZeroSingleAt γ (x γ)) α) (hdiag γ hγ α hα hγα)
        have hz' : T (cZeroSingleAt γ (x γ)) α = 0 := by
          simpa [cZeroCoordinateProjection_singleton, cZeroSingleAt_apply] using hz
        simp only [hz', cZeroSingleAt_apply, if_neg (Ne.symm hγα), map_zero]
      · have hs0 : cZeroSingleAt γ (0 : X) = 0 := by ext δ; simp
        simp only [hx γ hγ, hs0, map_zero]
        change (0 : X) = cZeroCoordinateEntry T α α 0
        exact (map_zero _).symm
  have hleft := (L.continuous.tendsto x).comp (cZero_hasSum_singleAt (𝕜 := 𝕜) x)
  have hright := (R.continuous.tendsto x).comp (cZero_hasSum_singleAt (𝕜 := 𝕜) x)
  change Tendsto (fun F : Finset Γ => L (∑ γ ∈ F, cZeroSingleAt γ (x γ))) atTop (𝓝 (L x)) at hleft
  have heq : (fun F : Finset Γ => L (∑ γ ∈ F, cZeroSingleAt γ (x γ))) =
      (fun F : Finset Γ => R (∑ γ ∈ F, cZeroSingleAt γ (x γ))) := by
    funext F; simp only [map_sum, hsingle]
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem cZeroExtend_apply_of_not_mem_range (e : Γ ↪ Γ) (x : C₀(Γ, X))
    {γ : Γ} (hγ : γ ∉ Set.range e) : cZeroExtend (𝕜 := 𝕜) e x γ = 0 := by
  simp [cZeroExtend, cZeroInsert, Function.extend_apply' _ _ _ hγ]

theorem cZero_coordinate_compression
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp T).comp
        (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0)
    (e : Γ ↪ Γ) (he : ∀ γ, e γ ∈ Λ) (x : C₀(Γ, X)) (γ : Γ) :
    T (cZeroExtend (𝕜 := 𝕜) e x) (e γ) = cZeroCoordinateEntry T (e γ) (e γ) (x γ) := by
  rw [cZero_coordinate_diagonal_on_support T Λ hdiag (cZeroExtend e x) ?_ (he γ),
    cZeroExtend_apply_image]
  intro δ hδ
  apply cZeroExtend_apply_of_not_mem_range
  rintro ⟨η, rfl⟩
  exact hδ (he η)

theorem cZero_factors_of_coordinate_compression
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (F : Γ → X →L[𝕜] X) (e : Γ ↪ Γ)
    (hcomp : ∀ x γ, T (cZeroExtend (𝕜 := 𝕜) e x) (e γ) = F (e γ) (x γ))
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ γ, FactorsIdentityWith (F (e γ)) X C) :
    FactorsIdentityWith T C₀(Γ, X) C := by
  choose U V heq hU hV using fun γ => (hF γ).normalized
  let A := cZeroDiagonal U C hC hU
  let B := cZeroDiagonal V 1 zero_le_one hV
  let R := cZeroRestrict (𝕜 := 𝕜) (X := X) e
  let J := cZeroExtend (𝕜 := 𝕜) (X := X) e
  have hnA : ‖A‖ ≤ C := norm_cZeroDiagonal_le _ _ _ _
  have hnB : ‖B‖ ≤ 1 := norm_cZeroDiagonal_le _ _ _ _
  have hnR : ‖R‖ ≤ 1 := norm_cZeroRestrict_le e
  have hnJ : ‖J‖ ≤ 1 := norm_cZeroExtend_le e
  refine ⟨A.comp R, J.comp B, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    ext γ
    change U γ (T (cZeroExtend (𝕜 := 𝕜) e (B x)) (e γ)) = x γ
    rw [hcomp]
    exact congrArg (fun f : X →L[𝕜] X => f (x γ)) (heq γ)
  · have hAR : ‖A.comp R‖ ≤ C := calc
      _ ≤ ‖A‖ * ‖R‖ := A.opNorm_comp_le R
      _ ≤ C * 1 := mul_le_mul hnA hnR (norm_nonneg R) hC
      _ = C := mul_one _
    have hJB : ‖J.comp B‖ ≤ 1 := calc
      _ ≤ ‖J‖ * ‖B‖ := J.opNorm_comp_le B
      _ ≤ 1 * 1 := mul_le_mul hnJ hnB (norm_nonneg B) zero_le_one
      _ = 1 := one_mul _
    simpa only [mul_one] using mul_le_mul hAR hJB (norm_nonneg (J.comp B)) hC

theorem cZero_factor_dichotomy_of_selected_coordinates
    (T : C₀(Γ, X) →L[𝕜] C₀(Γ, X)) (Λ : Set Γ)
    (hdiag : ∀ α ∈ Λ, ∀ β ∈ Λ, α ≠ β →
      ((cZeroCoordinateProjection (𝕜 := 𝕜) {β}).comp T).comp
        (cZeroCoordinateProjection (𝕜 := 𝕜) {α}) = 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hchoose :
      (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith (cZeroCoordinateEntry T γ γ) X C) ∨
      (∃ H : Set Γ, H ⊆ Λ ∧ Cardinal.mk H = Cardinal.mk Γ ∧
        ∀ γ ∈ H, FactorsIdentityWith
          (ContinuousLinearMap.id 𝕜 X - cZeroCoordinateEntry T γ γ) X C)) :
    FactorsIdentityWith T C₀(Γ, X) C ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 C₀(Γ, X) - T) C₀(Γ, X) C := by
  classical
  rcases hchoose with ⟨H, hHΛ, hHcard, hH⟩ | ⟨H, hHΛ, hHcard, hH⟩
  · obtain ⟨a⟩ := Cardinal.eq.mp hHcard.symm
    let e : Γ ↪ Γ := a.toEmbedding.trans (Function.Embedding.subtype H)
    have he (γ : Γ) : e γ ∈ Λ := hHΛ (a γ).property
    left
    exact cZero_factors_of_coordinate_compression T (fun γ => cZeroCoordinateEntry T γ γ) e
      (cZero_coordinate_compression T Λ hdiag e he) hC
      (fun γ => hH (e γ) (a γ).property)
  · obtain ⟨a⟩ := Cardinal.eq.mp hHcard.symm
    let e : Γ ↪ Γ := a.toEmbedding.trans (Function.Embedding.subtype H)
    have he (γ : Γ) : e γ ∈ Λ := hHΛ (a γ).property
    right
    refine cZero_factors_of_coordinate_compression _
      (fun γ => ContinuousLinearMap.id 𝕜 X - cZeroCoordinateEntry T γ γ) e ?_ hC
      (fun γ => hH (e γ) (a γ).property)
    intro x γ
    change cZeroExtend (𝕜 := 𝕜) e x (e γ) - T (cZeroExtend e x) (e γ) =
      x γ - cZeroCoordinateEntry T (e γ) (e γ) (x γ)
    rw [cZeroExtend_apply_image, cZero_coordinate_compression T Λ hdiag e he]

end ThesisCommon
