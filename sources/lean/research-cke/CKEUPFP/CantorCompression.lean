import CKEUPFP.CantorExtension
import CKEUPFP.Compression
import CKEUPFP.Multipliers
import CKEUPFP.Isomorphism
import CKEUPFP.LocalDefect
import CKEUPFP.ContinuousFactorSelection

/-!
# The geometric and operator-algebra assembly on the Cantor host

Supported extension converts the small local defect on the selected Cantor
subset into a compression norm estimate. Strongly continuous factor fields
then give multipliers; the proved perturbation lemma gives the exact bound.
The fields and selected subset remain explicit inputs to this assembly lemma.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- An isometric model of the identity can be replaced by the original
identity without changing either the middle operator or the cost. -/
theorem FactorsThroughWith.id_of_isometric_model
    (e : X ≃ₗᵢ[𝕜] Y) {T : X →L[𝕜] X} {C : ℝ}
    (h : FactorsThroughWith (ContinuousLinearMap.id 𝕜 Y) T C) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 X) T C := by
  obtain ⟨U, V, hUV, hnorm⟩ := h
  refine ⟨e.symm.toLinearIsometry.toContinuousLinearMap.comp U,
    V.comp e.toLinearIsometry.toContinuousLinearMap, ?_, ?_⟩
  · ext x
    have hx := congrArg (fun F : Y →L[𝕜] Y => F (e x)) hUV
    change U (T (V (e x))) = e x at hx
    change e.symm (U (T (V (e x)))) = x
    rw [hx, e.symm_apply_apply]
  · simpa only [LinearIsometry.norm_toContinuousLinearMap_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] using hnorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {D O : Set (ℕ → Fin 2)} [CompactSpace D]

/-- Supported extension and the paper's local-defect supremum control the
norm of the difference between the compressed operator and its multiplier. -/
theorem cantor_compression_error_le
    (T : C((ℕ → Fin 2), E) →L[𝕜] C((ℕ → Fin 2), E))
    (A : (ℕ → Fin 2) → E →L[𝕜] E)
    (J : C(D, E) →L[𝕜] C((ℕ → Fin 2), E))
    (M : C(D, E) →L[𝕜] C(D, E)) {η : ℝ}
    (hη : 0 ≤ η) (hJ : ‖J‖ ≤ 1)
    (hJvalue : ∀ f d, J f (d : D) = f d)
    (hJsupport : ∀ f, VanishesOff O (J f))
    (hMvalue : ∀ f d, M f d = A (d : D) (f d))
    (hsmall : ∀ d : D, localDefect T A O d ≤ η) :
    ‖((cantorRestriction (𝕜 := 𝕜)).comp T).comp J - M‖ ≤ η := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hη
  intro f hf
  have hJf : ‖J f‖ ≤ 1 := by
    calc
      ‖J f‖ ≤ ‖J‖ * ‖f‖ := J.le_opNorm f
      _ ≤ 1 := by simpa only [hf, mul_one] using hJ
  apply (ContinuousMap.norm_le _ hη).mpr
  intro d
  change ‖T (J f) d - M f d‖ ≤ η
  rw [hMvalue, ← hJvalue f d]
  exact (norm_sub_le_localDefect T A O d (J f) hJf (hJsupport f)).trans (hsmall d)

variable [CompleteSpace E]

/-- The last part of the paper's Cantor proof, starting from the constructed
small-defect subset and its continuous balanced factors. -/
theorem cantor_factorisation_of_selected_fields
    (T : C((ℕ → Fin 2), E) →L[𝕜] C((ℕ → Fin 2), E))
    (A : (ℕ → Fin 2) → E →L[𝕜] E)
    (hD : IsClosed D) (hne : D.Nonempty) (hO : IsOpen O) (hDO : D ⊆ O)
    (hmodel : (ℕ → Fin 2) ≃ₜ D) (σ : Bool)
    (L R : D → E →L[𝕜] E) {C η : ℝ}
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hquarter : C * η ≤ (1 / 4 : ℝ))
    (hA : IsStronglyContinuous (fun d : D => A d))
    (hAbound : ∀ d : D, ‖A d‖ ≤ ‖T‖)
    (hL : IsStronglyContinuous L) (hR : IsStronglyContinuous R)
    (hLbound : ∀ d, ‖L d‖ ≤ Real.sqrt C) (hRbound : ∀ d, ‖R d‖ ≤ Real.sqrt C)
    (hfactor : ∀ d, ((L d).comp (factorSelectionSide σ (A d))).comp (R d) =
      ContinuousLinearMap.id 𝕜 E)
    (hsmall : ∀ d : D, localDefect T A O d ≤ η) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 C((ℕ → Fin 2), E))
      (factorSelectionSide σ T) ((4 / 3 : ℝ) * C) := by
  let Q := cantorRestriction (𝕜 := 𝕜) (D := D) (E := E)
  let J := cantorSupportedExtend (𝕜 := 𝕜) (E := E) hD hne hO hDO
  let MA := multiplier (fun d : D => A d) hA ‖T‖ (norm_nonneg T) hAbound
  let ML := multiplier L hL (Real.sqrt C) (Real.sqrt_nonneg C) hLbound
  let MR := multiplier R hR (Real.sqrt C) (Real.sqrt_nonneg C) hRbound
  let Mσ : C(D, E) →L[𝕜] C(D, E) := factorSelectionSide σ MA
  have hQJ : Q.comp J = ContinuousLinearMap.id 𝕜 C(D, E) :=
    cantorSupportedExtend_right_inverse hD hne hO hDO
  have herr : ‖(Q.comp T).comp J - MA‖ ≤ η :=
    cantor_compression_error_le T A J MA hη
      (norm_cantorSupportedExtend_le hD hne hO hDO)
      (cantorSupportedExtend_on_subset hD hne hO hDO)
      (cantorSupportedExtend_vanishesOff hD hne hO hDO) (fun _ _ => rfl) hsmall
  have herrσ : ‖(Q.comp (factorSelectionSide σ T)).comp J - Mσ‖ ≤ η := by
    cases σ
    · exact herr
    · change ‖(Q.comp (ContinuousLinearMap.id 𝕜 _ - T)).comp J -
          (ContinuousLinearMap.id 𝕜 _ - MA)‖ ≤ η
      rwa [compression_complement_error T Q J MA hQJ]
  have hidentity : (ML.comp Mσ).comp MR = ContinuousLinearMap.id 𝕜 C(D, E) := by
    ext f d
    have hd := congrArg (fun F : E →L[𝕜] E => F (f d)) (hfactor d)
    cases σ <;> simpa [ML, MR, Mσ, MA, factorSelectionSide, multiplier_apply] using hd
  have hcost : ‖ML‖ * ‖MR‖ ≤ C := by
    calc
      ‖ML‖ * ‖MR‖ ≤ Real.sqrt C * Real.sqrt C :=
        mul_le_mul (multiplier_norm_le _ _ _ _ _) (multiplier_norm_le _ _ _ _ _)
          (norm_nonneg MR) (Real.sqrt_nonneg C)
      _ = C := Real.mul_self_sqrt (zero_le_one.trans hC)
  have hfact := factorsThroughWith_of_compression (factorSelectionSide σ T) Q J
    ML Mσ MR norm_cantorRestriction_le (norm_cantorSupportedExtend_le hD hne hO hDO)
    hidentity hcost hη herrσ hquarter
  exact hfact.id_of_isometric_model (continuousMapCongrIsometry hmodel)

end CKEUPFP
