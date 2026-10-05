import ThesisCommon.Analysis.GowersMaureyOperatorTargets
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Small unit vectors for a genuinely strictly singular operator can be
chosen in the common kernel of any finite family of scalar coordinates.
The original subspace need not be closed. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem IsStrictlySingularOperator.exists_unit_small
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T)
    (E : Submodule 𝕜 X) (hE : ¬ FiniteDimensional 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, x ∈ E ∧ ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  by_contra h
  push_neg at h
  apply hE
  apply hT E
  refine ⟨ε, hε, ?_⟩
  intro x
  by_cases hx : x.val = 0
  · simp [hx]
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr hx
  let y : X := ((‖x.val‖⁻¹ : ℝ) : 𝕜) • x.val
  have hy : y ∈ E := E.smul_mem _ x.property
  have hyn : ‖y‖ = 1 := by
    simp only [y, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hh := h y hy hyn
  simp only [y, map_smul, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at hh
  have hm := mul_le_mul_of_nonneg_right hh hn.le
  simpa only [mul_assoc, mul_left_comm ‖x.val‖⁻¹, inv_mul_cancel₀ hn.ne', mul_one] using hm

theorem not_finiteDimensional_map_kernel_of_finite_codomain
    (E : Submodule 𝕜 X) (hE : ¬ FiniteDimensional 𝕜 E)
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [FiniteDimensional 𝕜 Y]
    (f : E →ₗ[𝕜] Y) :
    ¬ FiniteDimensional 𝕜 ((LinearMap.ker f).map E.subtype) := by
  intro h
  letI := h
  let e := Submodule.equivMapOfInjective E.subtype
    (Submodule.injective_subtype E) (LinearMap.ker f)
  letI : FiniteDimensional 𝕜 (LinearMap.ker f) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : FiniteDimensional 𝕜 (E ⧸ LinearMap.ker f) :=
    FiniteDimensional.of_injective f.quotKerEquivRange.toLinearMap
      f.quotKerEquivRange.injective
  exact hE (Module.Finite.of_submodule_quotient (LinearMap.ker f))

theorem IsStrictlySingularOperator.exists_unit_small_annihilating
    {T : X →L[𝕜] X} (hT : IsStrictlySingularOperator T)
    (E : Submodule 𝕜 X) (hE : ¬ FiniteDimensional 𝕜 E) {N : ℕ}
    (φ : Fin N → X →L[𝕜] 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, x ∈ E ∧ ‖x‖ = 1 ∧ ‖T x‖ < ε ∧ ∀ i, φ i x = 0 := by
  let f : E →ₗ[𝕜] (Fin N → 𝕜) := {
    toFun := fun x i => φ i x.val
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro c x; ext i; simp }
  obtain ⟨x, hx, hxn, hxT⟩ := hT.exists_unit_small
    ((LinearMap.ker f).map E.subtype)
    (not_finiteDimensional_map_kernel_of_finite_codomain E hE f) hε
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y.val, y.property, hxn, hxT, ?_⟩
  intro i
  exact congrFun (show f y = 0 from hy) i

end ThesisCommon
