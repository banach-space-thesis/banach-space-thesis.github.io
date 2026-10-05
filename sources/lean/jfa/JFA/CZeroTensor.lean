import JFA.CZeroProduct
import JFA.ContinuousTensorDensity
import JFA.TensorCancellation

/-! The actual C₀ product identification and the unique decomposition in
Corollary 1.3. Both the tensor identification and the nonseparability consequence
of nonmetrizability have been proved, so neither is an extra hypothesis. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {L : Type*} [TopologicalSpace L] [LocallyCompactSpace L] [T2Space L]

def czeroTensorEquiv {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M] :
    InjectiveTensor 𝕜 C(M, 𝕜) C₀(L, 𝕜) ≃ₗᵢ[𝕜] C₀(M × L, 𝕜) :=
  (tensorContinuousEquiv (𝕜 := 𝕜) (M := M) (X := C₀(L, 𝕜))).trans
    (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := L)).symm

omit [LocallyCompactSpace L] in
@[simp] theorem czeroTensorEquiv_pure {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (f : C(M, 𝕜)) (g : C₀(L, 𝕜)) (p : M × L) :
    (czeroTensorEquiv (𝕜 := 𝕜) (M := M) (L := L)) (injectivePure 𝕜 C(M, 𝕜) C₀(L, 𝕜) f g) p = f p.1 * g p.2 := by
  rcases p with ⟨m, l⟩
  change (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := L)).symm ((tensorContinuousEquiv (𝕜 := 𝕜) (M := M) (X := C₀(L, 𝕜)))
    (injectivePure 𝕜 C(M, 𝕜) C₀(L, 𝕜) f g)) (m, l) = _
  rw [czeroProductEquiv_symm_apply]
  change tensorContinuousFunction (injectivePure 𝕜 C(M, 𝕜) C₀(L, 𝕜) f g) m l = _
  rw [tensorContinuousFunction_pure]
  rfl

theorem corollary_1_3 (M₁ M₂ : Type*) [MetricSpace M₁] [CompactSpace M₁]
    [MetricSpace M₂] [CompactSpace M₂] : Corollary_1_3 𝕜 L M₁ M₂ := by
  intro hL hfew T
  let E := C(M₁, 𝕜)
  let F := C(M₂, 𝕜)
  let X := C₀(L, 𝕜)
  let c₁ := czeroTensorEquiv (𝕜 := 𝕜) (L := L) (M := M₁)
  let c₂ := czeroTensorEquiv (𝕜 := 𝕜) (L := L) (M := M₂)
  let T' : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X :=
    c₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp c₁.toContinuousLinearEquiv.toContinuousLinearMap)
  have hX : ¬ SeparableSpace X := czero_nonseparable_of_nonmetrizable (𝕜 := 𝕜) hL
  obtain ⟨d, ⟨hsep, hEq⟩, hunique⟩ := epsilonDecomposition hX hfew T'
  let S : C₀(M₁ × L, 𝕜) →L[𝕜] C₀(M₂ × L, 𝕜) :=
    c₂.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (d.2.comp c₁.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hS : HasSeparableRange 𝕜 C₀(M₁ × L, 𝕜) C₀(M₂ × L, 𝕜) S :=
    (hsep.comp_right c₁.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp_left
      c₂.toContinuousLinearEquiv.toContinuousLinearMap
  have hproduct (f : E) (g : X) :
      T (c₁ (injectivePure 𝕜 E X f g)) =
        c₂ (injectivePure 𝕜 F X (d.1 f) g) + S (c₁ (injectivePure 𝕜 E X f g)) := by
    have h := congrArg c₂ (hEq f g)
    change c₂ (c₂.symm (T (c₁ (injectivePure 𝕜 E X f g)))) =
      c₂ (injectivePure 𝕜 F X (d.1 f) g + d.2 (injectivePure 𝕜 E X f g)) at h
    change T (c₁ (injectivePure 𝕜 E X f g)) =
      c₂ (injectivePure 𝕜 F X (d.1 f) g) +
        c₂ (d.2 (c₁.symm (c₁ (injectivePure 𝕜 E X f g))))
    simpa only [c₂.apply_symm_apply, c₁.symm_apply_apply, map_add] using h
  refine ⟨(d.1, S), ⟨hS, ?_⟩, ?_⟩
  · intro f g h hh p
    have hrep : h = c₁ (injectivePure 𝕜 E X f g) := by
      ext q
      exact (hh q).trans (czeroTensorEquiv_pure f g q).symm
    rw [hrep]
    have h := congrArg (fun k : C₀(M₂ × L, 𝕜) => k p) (hproduct f g)
    simp only [ZeroAtInftyContinuousMap.add_apply] at h
    have hc₂ : c₂ (injectivePure 𝕜 F X (d.1 f) g) p = (d.1 f) p.1 * g p.2 :=
      czeroTensorEquiv_pure (d.1 f) g p
    rw [hc₂] at h
    exact h
  · rintro ⟨V, R⟩ ⟨hR, hVR⟩
    let R' : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X :=
      c₂.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (R.comp c₁.toContinuousLinearEquiv.toContinuousLinearMap)
    have hR' : HasSeparableRange 𝕜 (InjectiveTensor 𝕜 E X) (InjectiveTensor 𝕜 F X) R' :=
      (hR.comp_right c₁.toContinuousLinearEquiv.toContinuousLinearMap).comp_left
        c₂.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hVR' : ∀ f g, T' (injectivePure 𝕜 E X f g) =
        injectivePure 𝕜 F X (V f) g + R' (injectivePure 𝕜 E X f g) := by
      intro f g
      have heq : T (c₁ (injectivePure 𝕜 E X f g)) =
          c₂ (injectivePure 𝕜 F X (V f) g) + R (c₁ (injectivePure 𝕜 E X f g)) := by
        ext p
        have hp := hVR f g (c₁ (injectivePure 𝕜 E X f g))
          (fun q => czeroTensorEquiv_pure f g q) p
        change T (c₁ (injectivePure 𝕜 E X f g)) p =
          c₂ (injectivePure 𝕜 F X (V f) g) p + R (c₁ (injectivePure 𝕜 E X f g)) p
        have hc₂ : c₂ (injectivePure 𝕜 F X (V f) g) p = (V f) p.1 * g p.2 :=
          czeroTensorEquiv_pure (V f) g p
        rw [hc₂]
        exact hp
      have h := congrArg c₂.symm heq
      change c₂.symm (T (c₁ (injectivePure 𝕜 E X f g))) =
        injectivePure 𝕜 F X (V f) g + c₂.symm (R (c₁ (injectivePure 𝕜 E X f g)))
      simpa only [map_add, c₂.symm_apply_apply] using h
    have hd : (V, R') = d := hunique (V, R') ⟨hR', hVR'⟩
    apply Prod.ext
    · exact congrArg (fun A : (E →L[𝕜] F) ×
        (InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X) => A.1) hd
    apply ContinuousLinearMap.ext
    intro h
    have hr := congrArg (fun A : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 F X =>
      c₂ (A (c₁.symm h))) (congrArg Prod.snd hd)
    change c₂ (c₂.symm (R (c₁ (c₁.symm h)))) = c₂ (d.2 (c₁.symm h)) at hr
    change R h = c₂ (d.2 (c₁.symm h))
    simpa only [c₁.apply_symm_apply, c₂.apply_symm_apply] using hr

end JFA
