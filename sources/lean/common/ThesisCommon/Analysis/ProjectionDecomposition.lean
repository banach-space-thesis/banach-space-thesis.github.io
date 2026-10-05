import ThesisCommon.Analysis.Factorization

/-! Complemented copies supplied by primary factorisation.
This is the first step of the Pełczyński decomposition argument cited in both
primariness papers. The splitting is mathlib's actual bounded map
`y ↦ (U y, y - V (U y))`, not an assumed existence of a complement.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A bounded projection splits the space into its actual range and kernel. -/
def projectionRangeKerEquiv (P : X →L[𝕜] X) (hP : P.comp P = P) :
    X ≃L[𝕜] LinearMap.range P.toLinearMap × LinearMap.ker P.toLinearMap := by
  have hPP (x : X) : P (P x) = P x := DFunLike.congr_fun hP x
  let Q := (ContinuousLinearMap.id 𝕜 X - P).codRestrict
    (LinearMap.ker P.toLinearMap) (by
      intro x
      change P (x - P x) = 0
      rw [map_sub, hPP, sub_self])
  refine ContinuousLinearEquiv.equivOfInverse (P.rangeRestrict.prod Q)
    ((LinearMap.range P.toLinearMap).subtypeL.coprod
      (LinearMap.ker P.toLinearMap).subtypeL) ?_ ?_
  · intro x
    change P x + (x - P x) = x
    rw [add_comm, sub_add_cancel]
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    have hPy : P y = y := by
      obtain ⟨t, rfl⟩ := hy
      exact hPP t
    change P z = 0 at hz
    apply Prod.ext <;> apply Subtype.ext
    · change P (y + z) = y
      rw [map_add, hPy, hz, add_zero]
    · change y + z - P (y + z) = z
      rw [map_add, hPy, hz, add_zero, add_sub_cancel_left]

/-- Factorisation through a projection splits its range as the whole space
times a concrete closed kernel. -/
theorem FactorsIdentity.projection_range_decomposition
    {P : X →L[𝕜] X} (h : FactorsIdentity P X) :
    ∃ U : LinearMap.range P.toLinearMap →L[𝕜] X,
      Nonempty (LinearMap.range P.toLinearMap ≃L[𝕜] X × LinearMap.ker U.toLinearMap) := by
  obtain ⟨U, V, hUV⟩ := h
  let U' := U.comp (LinearMap.range P.toLinearMap).subtypeL
  let V' := P.rangeRestrict.comp V
  refine ⟨U', ⟨ContinuousLinearEquiv.equivOfRightInverse U' V' ?_⟩⟩
  intro x
  exact DFunLike.congr_fun hUV x

/-- The complementary operator of a bounded projection is also a projection. -/
theorem complementary_projection {P : X →L[𝕜] X} (hP : P.comp P = P) :
    (ContinuousLinearMap.id 𝕜 X - P).comp (ContinuousLinearMap.id 𝕜 X - P) =
      ContinuousLinearMap.id 𝕜 X - P := by
  ext x
  have h := DFunLike.congr_fun hP x
  change P (P x) = P x at h
  change x - P x - P (x - P x) = x - P x
  rw [map_sub, h, sub_self, sub_zero]

end ThesisCommon
