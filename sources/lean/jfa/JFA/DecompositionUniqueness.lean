import JFA.SeparableRange
import JFA.TensorSlices

/-! The uniqueness clause of Theorem 1.1, proved from its original
nonseparability hypothesis. No existence or few-operator conclusion is assumed. -/

noncomputable section
open TopologicalSpace
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F X A : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]

theorem tensor_decomposition_unique (hX : ¬ SeparableSpace X)
    (p : ReasonableCrossnorm 𝕜 E X) (ι : E ⊗[𝕜] X →ₗ[𝕜] A)
    (hι : IsTensorCompletion 𝕜 E X A p ι)
    (T : A →L[𝕜] InjectiveTensor 𝕜 F X)
    {U V : E →L[𝕜] F} {S R : A →L[𝕜] InjectiveTensor 𝕜 F X}
    (hS : HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) S)
    (hR : HasSeparableRange 𝕜 A (InjectiveTensor 𝕜 F X) R)
    (hU : ∀ e x, T (ι (e ⊗ₜ[𝕜] x)) =
      injectivePure 𝕜 F X (U e) x + S (ι (e ⊗ₜ[𝕜] x)))
    (hV : ∀ e x, T (ι (e ⊗ₜ[𝕜] x)) =
      injectivePure 𝕜 F X (V e) x + R (ι (e ⊗ₜ[𝕜] x))) : U = V ∧ S = R := by
  have hUV : U = V := by
    ext e
    apply (NormedSpace.eq_iff_forall_dual_eq (𝕜 := 𝕜)).mpr
    intro φ
    let M := (leftSlice φ).comp ((R - S).comp (completionPureMap p ι hι e))
    have hMsep : HasSeparableRange 𝕜 X X M :=
      ((hR.sub hS).comp_right (completionPureMap p ι hι e)).comp_left (leftSlice φ)
    have hM : M = (φ (U e) - φ (V e)) • ContinuousLinearMap.id 𝕜 X := by
      ext x
      change leftSlice φ (R (ι (e ⊗ₜ[𝕜] x)) - S (ι (e ⊗ₜ[𝕜] x))) =
        (φ (U e) - φ (V e)) • x
      rw [map_sub, sub_smul]
      have h := congrArg (leftSlice φ) ((hU e x).symm.trans (hV e x))
      simp only [map_add, leftSlice_pure] at h
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using h.symm)
    have hz := (scalar_id_separable_iff hX (φ (U e) - φ (V e))).mp (hM ▸ hMsep)
    exact sub_eq_zero.mp hz
  refine ⟨hUV, ?_⟩
  apply completion_ext ι hι.2.1
  intro e x
  have h := (hU e x).symm.trans (hV e x)
  rw [hUV] at h
  exact add_left_cancel h

end JFA
