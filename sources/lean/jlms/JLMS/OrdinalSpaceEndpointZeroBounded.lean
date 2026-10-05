import JLMS.OrdinalSpaceEndpointZero

/-!
# Uniform bounds in Kislyakov's endpoint-zero identification

The forward and inverse maps both have norm at most two, uniformly in the
infinite ordinal. Their distortion is therefore at most four, as asserted
in Kislyakov (1.1). These bounds allow the identification to be applied
coordinatewise inside Banach c₀ sums.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

local instance endpointBoundedFunctionGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (OrdinalC 𝕜 α) := inferInstance
local instance endpointBoundedFunctionSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (OrdinalC 𝕜 α) := inferInstance

theorem norm_ordinalZeroEvaluation (f : OrdinalC 𝕜 (0 : Ordinal.{u})) :
    ‖ordinalZeroEvaluation f‖ = ‖f‖ := by
  apply le_antisymm (f.norm_coe_le_norm _)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  have hx : x = (⟨0, le_rfl, le_rfl⟩ : OrdinalInterval (0 : Ordinal.{u})) :=
    Subtype.ext (le_antisymm x.property.2 x.property.1)
  subst x
  exact le_rfl

def ordinalZeroProductIsometry {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    OrdinalC 𝕜 (0 : Ordinal.{u}) × E ≃ₗᵢ[𝕜] 𝕜 × E where
  toLinearEquiv := (ordinalZeroEvaluation.prodCongr (ContinuousLinearEquiv.refl 𝕜 E)).toLinearEquiv
  norm_map' f := by
    change max ‖ordinalZeroEvaluation f.1‖ ‖f.2‖ = max ‖f.1‖ ‖f.2‖
    rw [norm_ordinalZeroEvaluation]

def ordinalIsolatedSplitIsometry (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    OrdinalC 𝕜 α ≃ₗᵢ[𝕜] 𝕜 × OrdinalC 𝕜 α :=
  (ordinalSpaceCongrIsometry (zero_add α).symm).trans
    ((ordinalSpaceAddIsometry 0 α hα).trans ordinalZeroProductIsometry)

theorem ordinalIsolatedSplitIsometry_endpoint (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α)
    (f : OrdinalC 𝕜 α) :
    (ordinalIsolatedSplitIsometry (𝕜 := 𝕜) α hα f).2 ⟨α, Ordinal.zero_le _, le_rfl⟩ =
      f ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
  change f ((ordinalIntervalCongr (zero_add α))
    (ordinalSplitRight 0 α hα ⟨α, Ordinal.zero_le _, le_rfl⟩)) = _
  congr 1
  apply Subtype.ext
  change (0 + 1) + α = α
  simp only [zero_add, Ordinal.one_add_of_omega0_le hα]

section StableKernelBounds
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (χ : E →L[𝕜] 𝕜) (v : E) (hv : χ v = 1)
  (e : E ≃ₗᵢ[𝕜] 𝕜 × E) (he : ∀ x, χ (e x).2 = χ x)

theorem norm_kernelEquivOfStableSplit_le (hχ : ∀ x, ‖χ x‖ ≤ ‖x‖) (hnv : ‖v‖ ≤ 1) (x : E) :
    ‖kernelEquivOfStableSplit χ v hv e.toContinuousLinearEquiv he x‖ ≤ 2 * ‖x‖ := by
  change ‖e.symm (χ x, x - χ x • v)‖ ≤ _
  rw [e.symm.norm_map, Prod.norm_def]
  apply max_le
  · exact (hχ x).trans (by nlinarith [norm_nonneg x])
  · calc
      ‖x - χ x • v‖ ≤ ‖x‖ + ‖χ x • v‖ := norm_sub_le _ _
      _ = ‖x‖ + ‖χ x‖ * ‖v‖ := by rw [norm_smul]
      _ ≤ ‖x‖ + ‖χ x‖ :=
        add_le_add_left (mul_le_of_le_one_right (norm_nonneg (χ x)) hnv) _
      _ ≤ 2 * ‖x‖ := by linarith [hχ x]

theorem norm_kernelEquivOfStableSplit_symm_le (hnv : ‖v‖ ≤ 1)
    (x : LinearMap.ker χ) :
    ‖(kernelEquivOfStableSplit χ v hv e.toContinuousLinearEquiv he).symm x‖ ≤ 2 * ‖x‖ := by
  change ‖(e x.val).2 + (e x.val).1 • v‖ ≤ _
  have hfst : ‖(e x.val).1‖ ≤ ‖x‖ := by
    exact (le_max_left ‖(e x.val).1‖ ‖(e x.val).2‖).trans_eq (e.norm_map x.val)
  have hsnd : ‖(e x.val).2‖ ≤ ‖x‖ := by
    exact (le_max_right ‖(e x.val).1‖ ‖(e x.val).2‖).trans_eq (e.norm_map x.val)
  calc
    ‖(e x.val).2 + (e x.val).1 • v‖ ≤ ‖(e x.val).2‖ + ‖(e x.val).1 • v‖ := norm_add_le _ _
    _ = ‖(e x.val).2‖ + ‖(e x.val).1‖ * ‖v‖ := by rw [norm_smul]
    _ ≤ ‖(e x.val).2‖ + ‖(e x.val).1‖ :=
      add_le_add_left (mul_le_of_le_one_right (norm_nonneg (e x.val).1) hnv) _
    _ ≤ 2 * ‖x‖ := by linarith
end StableKernelBounds

def ordinalSpaceEndpointZeroBoundedEquiv (α : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) :
    OrdinalC 𝕜 α ≃L[𝕜] ordinalEndpointZero 𝕜 α :=
  kernelEquivOfStableSplit
    (ContinuousMap.evalCLM (R := 𝕜) (M := 𝕜)
      (⟨α, Ordinal.zero_le _, le_rfl⟩ : OrdinalInterval α))
    (ContinuousMap.const _ 1) rfl (ordinalIsolatedSplitIsometry (𝕜 := 𝕜) α hα).toContinuousLinearEquiv
    (ordinalIsolatedSplitIsometry_endpoint (𝕜 := 𝕜) α hα)

theorem norm_ordinalSpaceEndpointZeroBoundedEquiv_le (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) (f : OrdinalC 𝕜 α) :
    ‖ordinalSpaceEndpointZeroBoundedEquiv α hα f‖ ≤ 2 * ‖f‖ := by
  unfold ordinalSpaceEndpointZeroBoundedEquiv
  apply norm_kernelEquivOfStableSplit_le
  · exact fun g => g.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    simp

theorem norm_ordinalSpaceEndpointZeroBoundedEquiv_symm_le (α : Ordinal.{u})
    (hα : Ordinal.omega0 ≤ α) (f : ordinalEndpointZero 𝕜 α) :
    ‖(ordinalSpaceEndpointZeroBoundedEquiv α hα).symm f‖ ≤ 2 * ‖f‖ := by
  unfold ordinalSpaceEndpointZeroBoundedEquiv
  apply norm_kernelEquivOfStableSplit_symm_le
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro x
  simp

end JLMS
