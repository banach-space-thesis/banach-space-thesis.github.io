import Posets.TopologyStatements

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty OnePoint
namespace Posets

variable {K : Type*} [TopologicalSpace K] [T2Space K] {L : Set K}

omit [TopologicalSpace K] [T2Space K] in
theorem collapse_surjective (L : Set K) : Function.Surjective (collapse L) := by
  intro y
  cases y with
  | infty => exact ⟨none, rfl⟩
  | coe y => exact ⟨some y.val, by simp [collapse, y.property]; rfl⟩

theorem collapse_continuous (hL : IsOpen L) : Continuous (collapse L) := by
  apply continuous_def.mpr
  intro U hU
  by_cases hinf : (∞ : OnePoint L) ∈ U
  · have hcompact := ((OnePoint.isOpen_iff_of_mem' hinf).mp hU).1
    have heq : ((↑) ⁻¹' ((collapse L) ⁻¹' U) : Set K)ᶜ =
        Subtype.val '' (((↑) ⁻¹' U : Set L)ᶜ) := by
      ext x
      by_cases hx : x ∈ L
      · simp [collapse, hx, Set.mem_image, Subtype.exists]; rfl
      · simp [collapse, hx, Set.mem_image]; exact hinf
    apply (OnePoint.isOpen_iff_of_mem' (show (∞ : OnePoint K) ∈ collapse L ⁻¹' U from hinf)).mpr
    have hc : IsCompact (((↑) ⁻¹' ((collapse L) ⁻¹' U) : Set K)ᶜ) := by
      rw [heq]
      exact hcompact.image continuous_subtype_val
    exact ⟨hc, isClosed_compl_iff.mp hc.isClosed⟩
  · have heq : ((↑) ⁻¹' ((collapse L) ⁻¹' U) : Set K) =
        Subtype.val '' ((↑) ⁻¹' U : Set L) := by
      ext x
      by_cases hx : x ∈ L
      · simp [collapse, hx, Set.mem_image, Subtype.exists]; rfl
      · simp [collapse, hx, Set.mem_image]; exact hinf
    apply (OnePoint.isOpen_iff_of_notMem (show (∞ : OnePoint K) ∉ collapse L ⁻¹' U from hinf)).mpr
    rw [heq]
    exact hL.isOpenEmbedding_subtypeVal.isOpenMap _
      ((OnePoint.isOpen_iff_of_notMem hinf).mp hU)

variable {𝕜 : Type} [RCLike 𝕜]

/-- The continuous extension of a C₀ function to the point at infinity. -/
def atInfinity (f : C₀(L, 𝕜)) : C(OnePoint L, 𝕜) :=
  OnePoint.continuousMapMk f.toContinuousMap 0
    (by simpa only [coclosedCompact_eq_cocompact] using zero_at_infty f)

def openExtensionValue (f : C₀(L, 𝕜)) (x : K) : 𝕜 :=
  if hx : x ∈ L then f ⟨x, hx⟩ else 0

theorem openExtensionValue_continuous (hL : IsOpen L) (f : C₀(L, 𝕜)) :
    Continuous (openExtensionValue f) := by
  have hc := (atInfinity f).continuous.comp
    ((collapse_continuous hL).comp OnePoint.continuous_coe)
  convert hc using 1
  funext x
  by_cases hx : x ∈ L <;> simp [openExtensionValue, atInfinity,
    Function.comp_def, collapse, OnePoint.continuousMapMk, hx] <;> rfl

omit [T2Space K] in
theorem openExtensionValue_zeroAtInfty (f : C₀(L, 𝕜)) :
    Tendsto (openExtensionValue f) (cocompact K) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hsmall⟩ := hasBasis_cocompact.mem_iff.mp
    ((Metric.tendsto_nhds.mp (zero_at_infty f)) ε hε)
  filter_upwards [(hC.image continuous_subtype_val).compl_mem_cocompact] with x hx
  by_cases hxL : x ∈ L
  · simp only [openExtensionValue, dif_pos hxL]
    apply hsmall
    intro hxC
    exact hx ⟨⟨x, hxL⟩, hxC, rfl⟩
  · simpa [openExtensionValue, hxL] using hε

def openExtension (hL : IsOpen L) (f : C₀(L, 𝕜)) : C₀(K, 𝕜) where
  toFun := openExtensionValue f
  continuous_toFun := openExtensionValue_continuous hL f
  zero_at_infty' := openExtensionValue_zeroAtInfty f

theorem norm_openExtension_le (hL : IsOpen L) (f : C₀(L, 𝕜)) :
    ‖openExtension hL f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖openExtensionValue f x‖ ≤ ‖f‖
  by_cases hx : x ∈ L
  · simpa only [openExtensionValue, dif_pos hx] using f.toBCF.norm_coe_le_norm ⟨x, hx⟩
  · simp [openExtensionValue, hx]

/-- Pullback through the collapse map, restricted to functions zero at infinity. -/
def openExtensionHom (hL : IsOpen L) : BoundedHom 𝕜 C₀(L, 𝕜) C₀(K, 𝕜) where
  toContinuousLinearMap :=
    ({toFun := openExtension hL
      map_add' := by
        intro f g
        ext x
        by_cases hx : x ∈ L <;> simp [openExtension, openExtensionValue, hx]
      map_smul' := by
        intro a f
        ext x
        by_cases hx : x ∈ L <;> simp [openExtension, openExtensionValue, hx]} :
      C₀(L, 𝕜) →ₗ[𝕜] C₀(K, 𝕜)).mkContinuous 1
        (fun f => by simpa using norm_openExtension_le hL f)
  map_mul' := by
    intro f g
    ext x
    by_cases hx : x ∈ L <;> simp [openExtension, openExtensionValue, hx]

theorem openExtensionHom_isometry (hL : IsOpen L) :
    Isometry (openExtensionHom (𝕜 := 𝕜) hL) := by
  apply AddMonoidHomClass.isometry_of_norm (openExtensionHom hL).toContinuousLinearMap
  intro f
  apply le_antisymm (norm_openExtension_le hL f)
  apply (BoundedContinuousFunction.norm_le (norm_nonneg (openExtension hL f))).mpr
  intro x
  have hx := (openExtension hL f).toBCF.norm_coe_le_norm x.val
  simpa [openExtension, openExtensionValue, x.property] using hx

theorem lemma_4_6_proof (𝕜 : Type) [RCLike 𝕜] (K : Type*)
    [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K] (L : Set K) :
    Lemma_4_6 𝕜 K L := by
  intro hL
  exact ⟨collapse_continuous hL, collapse_surjective L,
    openExtensionHom hL, openExtensionHom_isometry hL, fun _ _ => rfl⟩

end Posets
