import ThesisCommon.Analysis.ScalarIsometryTransport
import ThesisCommon.Analysis.Factorization

/-! Isometric semilinear changes of scalar field preserve the actual
factorisation dichotomy and its exact bound. Operators are conjugated by
the given semilinear isometry, so the transported factors are linear over
the target field. -/
noncomputable section
namespace ThesisCommon
attribute [local instance] RingHomInvPair.of_ringEquiv
variable {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜' Y]
variable (r : 𝕜 ≃+* 𝕜')
  [RingHomIsometric (RingHomClass.toRingHom r)]
  [RingHomIsometric (RingHomClass.toRingHom r.symm)]
  (e : X ≃ₛₗᵢ[RingHomClass.toRingHom r] Y)

def operatorScalarConjugate : (X →L[𝕜] X) ≃SL[RingHomClass.toRingHom r] (Y →L[𝕜'] Y) :=
  e.toContinuousLinearEquiv.arrowCongrSL e.toContinuousLinearEquiv

@[simp] theorem operatorScalarConjugate_apply (T : X →L[𝕜] X) (y : Y) :
    operatorScalarConjugate r e T y = e (T (e.symm y)) := rfl

theorem operatorScalarConjugate_norm (T : X →L[𝕜] X) :
    ‖operatorScalarConjugate r e T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro y
    rw [operatorScalarConjugate_apply, e.norm_map]
    exact (T.le_opNorm _).trans_eq (by rw [e.symm.norm_map])
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := (operatorScalarConjugate r e T).le_opNorm (e x)
    simpa only [operatorScalarConjugate_apply, e.symm_apply_apply, e.norm_map] using h

@[simp] theorem operatorScalarConjugate_id :
    operatorScalarConjugate r e (ContinuousLinearMap.id 𝕜 X) =
      ContinuousLinearMap.id 𝕜' Y := by
  apply ContinuousLinearMap.ext
  intro y
  exact e.apply_symm_apply y

theorem operatorScalarConjugate_comp (S T : X →L[𝕜] X) :
    operatorScalarConjugate r e (S.comp T) =
      (operatorScalarConjugate r e S).comp (operatorScalarConjugate r e T) := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [operatorScalarConjugate_apply, ContinuousLinearMap.comp_apply, e.symm_apply_apply]

theorem FactorsIdentityWith.scalar_conjugate {T : X →L[𝕜] X} {C : ℝ}
    (h : FactorsIdentityWith T X C) :
    FactorsIdentityWith (operatorScalarConjugate r e T) Y C := by
  obtain ⟨U, V, heq, hn⟩ := h
  refine ⟨operatorScalarConjugate r e U, operatorScalarConjugate r e V, ?_, ?_⟩
  · rw [← operatorScalarConjugate_comp, ← operatorScalarConjugate_comp, heq,
      operatorScalarConjugate_id]
  · simpa only [operatorScalarConjugate_norm] using hn

include r e in
theorem HasCPFP.of_semilinearIsometry {C : ℝ} (h : HasCPFP 𝕜 X C) :
    HasCPFP 𝕜' Y C := by
  intro T
  let S := (operatorScalarConjugate r e).symm T
  have hS : operatorScalarConjugate r e S = T :=
    (operatorScalarConjugate r e).apply_symm_apply T
  rcases h S with hf | hf
  · exact Or.inl (hS ▸ hf.scalar_conjugate r e)
  · right
    have hh := hf.scalar_conjugate r e
    simpa only [map_sub, operatorScalarConjugate_id, hS] using hh

include r e in
theorem HasUPFP.of_semilinearIsometry (h : HasUPFP 𝕜 X) : HasUPFP 𝕜' Y := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, h.of_semilinearIsometry r e⟩

theorem FactorsIdentity.scalar_conjugate {T : X →L[𝕜] X}
    (h : FactorsIdentity T X) : FactorsIdentity (operatorScalarConjugate r e T) Y := by
  obtain ⟨U, V, heq⟩ := h
  refine ⟨operatorScalarConjugate r e U, operatorScalarConjugate r e V, ?_⟩
  rw [← operatorScalarConjugate_comp, ← operatorScalarConjugate_comp, heq,
    operatorScalarConjugate_id]

include r e in
theorem HasPFP.of_semilinearIsometry (h : HasPFP 𝕜 X) : HasPFP 𝕜' Y := by
  intro T
  let S := (operatorScalarConjugate r e).symm T
  have hS : operatorScalarConjugate r e S = T :=
    (operatorScalarConjugate r e).apply_symm_apply T
  rcases h S with hf | hf
  · exact Or.inl (hS ▸ hf.scalar_conjugate r e)
  · right
    have hh := hf.scalar_conjugate r e
    simpa only [map_sub, operatorScalarConjugate_id, hS] using hh

end ThesisCommon
