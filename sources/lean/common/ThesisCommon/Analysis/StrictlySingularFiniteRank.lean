import ThesisCommon.Analysis.GowersMaureyOperatorTargets

/-! Elementary consequences of the genuine subspace/bounded-below definition
of strictly singular operators, without assuming an operator ideal theorem. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem isStrictlySingularOperator_of_finiteDimensional_range
    (T : X →L[𝕜] X) [FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)] :
    IsStrictlySingularOperator T := by
  intro E hE
  obtain ⟨c, hc, hb⟩ := hE
  let f : E →ₗ[𝕜] LinearMap.range T.toLinearMap := T.toLinearMap.rangeRestrict.comp E.subtype
  apply FiniteDimensional.of_injective f
  intro x y hxy
  have hxy' : T x.val = T y.val := congrArg Subtype.val hxy
  have hzero : T ((x - y : E).val) = 0 := by
    change T (x.val - y.val) = 0
    rw [map_sub, hxy', sub_self]
  have hnorm : ‖x - y‖ ≤ 0 := by
    have h := hb (x - y)
    rw [hzero, norm_zero] at h
    nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)

theorem isStrictlySingularOperator_projection_iff_finiteDimensional_range
    (P : X →L[𝕜] X) (hP : P.comp P = P) :
    IsStrictlySingularOperator P ↔ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) := by
  constructor
  · intro h
    apply h (LinearMap.range P.toLinearMap)
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    obtain ⟨y, hy⟩ := x.property
    have hx : P x.val = x.val := by
      rw [← hy]
      exact DFunLike.congr_fun hP y
    simp only [hx, one_mul, Submodule.norm_coe]
    exact le_rfl
  · intro h
    letI := h
    exact isStrictlySingularOperator_of_finiteDimensional_range P

end ThesisCommon
