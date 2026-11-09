import CKEUPFP.Definitions
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Ring

/-!
# Isomorphic invariance of the primary factorisation properties

Conjugating both factor maps accounts for two copies of the distortion
`‖e‖ * ‖e.symm‖`. Isometries preserve the factorisation constant exactly.
Reparametrising a compact domain by a homeomorphism is a linear isometry of
the corresponding spaces of continuous vector-valued functions.
-/

noncomputable section

namespace CKEUPFP

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Pull back an endomorphism along a bounded linear equivalence. -/
def conjugateOperator (e : X ≃L[𝕜] Y) (T : Y →L[𝕜] Y) : X →L[𝕜] X :=
  (e.symm.toContinuousLinearMap.comp T).comp e.toContinuousLinearMap

@[simp]
theorem conjugateOperator_apply (e : X ≃L[𝕜] Y) (T : Y →L[𝕜] Y) (x : X) :
    conjugateOperator e T x = e.symm (T (e x)) := rfl

theorem conjugateOperator_complement (e : X ≃L[𝕜] Y) (T : Y →L[𝕜] Y) :
    conjugateOperator e (ContinuousLinearMap.id 𝕜 Y - T) =
      ContinuousLinearMap.id 𝕜 X - conjugateOperator e T := by
  ext x
  simp [conjugateOperator]

/-- Conjugate a factorisation, tracking both factor maps' distortion. -/
theorem FactorsThroughWith.of_conjugate {T : Y →L[𝕜] Y} {C : ℝ}
    (e : X ≃L[𝕜] Y)
    (h : FactorsThroughWith (ContinuousLinearMap.id 𝕜 X) (conjugateOperator e T) C) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 Y) T
      (C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) ^ 2) := by
  obtain ⟨U, V, heq, hnorm⟩ := h
  let A := e.symm.toContinuousLinearMap
  let B := e.toContinuousLinearMap
  refine ⟨(B.comp U).comp A, (B.comp V).comp A, ?_, ?_⟩
  · ext y
    have hy := congrArg (fun f : X →L[𝕜] X => f (e.symm y)) heq
    change U (e.symm (T (e (V (e.symm y))))) = e.symm y at hy
    change e (U (e.symm (T (e (V (e.symm y)))))) = y
    rw [hy, e.apply_symm_apply]
  · have hbnd (L : X →L[𝕜] X) :
        ‖(B.comp L).comp A‖ ≤ (‖B‖ * ‖L‖) * ‖A‖ := by
      calc
        ‖(B.comp L).comp A‖ ≤ ‖B.comp L‖ * ‖A‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖B‖ * ‖L‖) * ‖A‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    calc
      ‖(B.comp U).comp A‖ * ‖(B.comp V).comp A‖ ≤
          ((‖B‖ * ‖U‖) * ‖A‖) * ((‖B‖ * ‖V‖) * ‖A‖) := by
        exact mul_le_mul (hbnd U) (hbnd V) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      _ = (‖U‖ * ‖V‖) * (‖B‖ * ‖A‖) ^ 2 := by ring
      _ ≤ C * (‖B‖ * ‖A‖) ^ 2 :=
        mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

/-- The `max` also covers the zero space, where the distortion is zero. -/
theorem HasCPFP.of_equiv {C : ℝ} (h : HasCPFP 𝕜 X C) (e : X ≃L[𝕜] Y) :
    HasCPFP 𝕜 Y
      (max 1 (C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) ^ 2)) := by
  refine ⟨le_max_left _ _, ?_⟩
  intro T
  have liftFactor (S : Y →L[𝕜] Y)
      (hS : FactorsThroughWith (ContinuousLinearMap.id 𝕜 X) (conjugateOperator e S) C) :
      FactorsThroughWith (ContinuousLinearMap.id 𝕜 Y) S
        (max 1 (C * (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) ^ 2)) := by
    obtain ⟨U, V, heq, hbnd⟩ := hS.of_conjugate e
    exact ⟨U, V, heq, hbnd.trans (le_max_right _ _)⟩
  rcases h.2 (conjugateOperator e T) with hT | hT
  · exact Or.inl (liftFactor T hT)
  · apply Or.inr
    apply liftFactor (ContinuousLinearMap.id 𝕜 Y - T)
    rwa [conjugateOperator_complement]

theorem HasUPFP.of_equiv (h : HasUPFP 𝕜 X) (e : X ≃L[𝕜] Y) : HasUPFP 𝕜 Y := by
  obtain ⟨C, hC⟩ := h
  exact ⟨_, hC.of_equiv e⟩

theorem hasUPFP_iff_of_equiv (e : X ≃L[𝕜] Y) : HasUPFP 𝕜 X ↔ HasUPFP 𝕜 Y :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

/-- Linear isometries allow the same constant, including for zero spaces. -/
theorem FactorsThroughWith.of_isometric_conjugate {T : Y →L[𝕜] Y} {C : ℝ}
    (e : X ≃ₗᵢ[𝕜] Y)
    (h : FactorsThroughWith (ContinuousLinearMap.id 𝕜 X)
      (conjugateOperator e.toContinuousLinearEquiv T) C) :
    FactorsThroughWith (ContinuousLinearMap.id 𝕜 Y) T C := by
  obtain ⟨U, V, heq, hnorm⟩ := h
  let A := e.symm.toLinearIsometry.toContinuousLinearMap
  let B := e.toLinearIsometry.toContinuousLinearMap
  refine ⟨(B.comp U).comp A, (B.comp V).comp A, ?_, ?_⟩
  · ext y
    have hy := congrArg (fun f : X →L[𝕜] X => f (e.symm y)) heq
    change U (e.symm (T (e (V (e.symm y))))) = e.symm y at hy
    change e (U (e.symm (T (e (V (e.symm y)))))) = y
    rw [hy, e.apply_symm_apply]
  · have hn (L : X →L[𝕜] X) : ‖(B.comp L).comp A‖ = ‖L‖ := by
      change ‖(e.toLinearIsometry.toContinuousLinearMap.comp L).comp
        e.symm.toLinearIsometry.toContinuousLinearMap‖ = ‖L‖
      rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
        LinearIsometry.norm_toContinuousLinearMap_comp]
    simpa only [hn] using hnorm

theorem HasCPFP.of_isometry {C : ℝ} (h : HasCPFP 𝕜 X C) (e : X ≃ₗᵢ[𝕜] Y) :
    HasCPFP 𝕜 Y C := by
  refine ⟨h.1, ?_⟩
  intro T
  rcases h.2 (conjugateOperator e.toContinuousLinearEquiv T) with hT | hT
  · exact Or.inl (hT.of_isometric_conjugate e)
  · apply Or.inr
    apply FactorsThroughWith.of_isometric_conjugate e
    rwa [conjugateOperator_complement]

theorem hasCPFP_iff_of_isometry (e : X ≃ₗᵢ[𝕜] Y) (C : ℝ) :
    HasCPFP 𝕜 X C ↔ HasCPFP 𝕜 Y C :=
  ⟨fun h => h.of_isometry e, fun h => h.of_isometry e.symm⟩

section ContinuousMaps

variable {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]

/-- A homeomorphism of compact domains induces a linear isometry on `C(K,X)`.
The map sends `f` to `f ∘ h.symm`. -/
def continuousMapCongrIsometry (h : K ≃ₜ L) : C(K, X) ≃ₗᵢ[𝕜] C(L, X) where
  toFun f := f.comp (h.symm : C(L, K))
  invFun f := f.comp (h : C(K, L))
  left_inv f := by ext k; simp
  right_inv f := by ext l; simp
  map_add' f g := by ext l; rfl
  map_smul' c f := by ext l; rfl
  norm_map' f := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro l
      exact ContinuousMap.norm_coe_le_norm f (h.symm l)
    · apply (ContinuousMap.norm_le f (norm_nonneg (f.comp (h.symm : C(L, K))))).2
      intro k
      simpa using ContinuousMap.norm_coe_le_norm (f.comp (h.symm : C(L, K))) (h k)

@[simp]
theorem continuousMapCongrIsometry_apply (h : K ≃ₜ L) (f : C(K, X)) (l : L) :
    continuousMapCongrIsometry (𝕜 := 𝕜) (X := X) h f l = f (h.symm l) := rfl

theorem hasCPFP_continuousMap_iff_of_homeomorph (h : K ≃ₜ L) (C : ℝ) :
    HasCPFP 𝕜 C(K, X) C ↔ HasCPFP 𝕜 C(L, X) C :=
  hasCPFP_iff_of_isometry (continuousMapCongrIsometry h) C

theorem hasUPFP_continuousMap_iff_of_homeomorph (h : K ≃ₜ L) :
    HasUPFP 𝕜 C(K, X) ↔ HasUPFP 𝕜 C(L, X) :=
  hasUPFP_iff_of_equiv (continuousMapCongrIsometry h).toContinuousLinearEquiv

end ContinuousMaps

end CKEUPFP
