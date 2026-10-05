import ThesisCommon.Analysis.JamesBidualDecomposition
import ThesisCommon.Analysis.BanachAdjointAlgebra
import ThesisCommon.Analysis.Gantmacher

/-! The scalar action of a James-space operator on the actual bidual quotient.
Its kernel is exactly the weakly compact operators. In particular, every
projection has one weakly compact complementary projection. These facts do
not assert primarity or identify either projection range with James space. -/
noncomputable section
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (hpl : 1 < p.val.toReal)

local instance jamesCharacterBidualGroup :
    NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)
local instance jamesCharacterBidualSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := 𝕜) (E := StrongDual 𝕜 (JamesSequenceSpace 𝕜 p))
    (F := 𝕜) (σ₁₂ := RingHom.id 𝕜)

def jamesOperatorScalar (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) : 𝕜 :=
  jamesBidualLimit p hp (bidualMap T (jamesBidualConstant (𝕜 := 𝕜) p hp hpl))

theorem jamesOperatorScalar_norm_le (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    ‖jamesOperatorScalar p hp hpl T‖ ≤ ‖T‖ := by
  apply (jamesBidualLimit_norm_le p hp _).trans
  apply ((bidualMap T).le_opNorm (jamesBidualConstant (𝕜 := 𝕜) p hp hpl)).trans
  rw [norm_bidualMap]
  exact (mul_le_mul_of_nonneg_left (jamesBidualConstant_norm_le p hp hpl)
    (norm_nonneg T)).trans_eq (mul_one _)

theorem jamesBidualLimit_map (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p)
    (ξ : (JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜) →L[𝕜] 𝕜) :
    jamesBidualLimit p hp (bidualMap T ξ) =
      jamesOperatorScalar p hp hpl T * jamesBidualLimit p hp ξ := by
  have hc (x : JamesSequenceSpace 𝕜 p) :
      bidualMap T (NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p) x) =
        NormedSpace.inclusionInDoubleDual 𝕜 (JamesSequenceSpace 𝕜 p) (T x) := by
    ext φ
    rfl
  have hξ := congrArg (fun ζ => jamesBidualLimitContinuous (𝕜 := 𝕜) p hp (bidualMap T ζ))
    (jamesBidual_decomposition p hp hpl ξ)
  simp only [map_add, map_smul, hc, jamesBidualLimitContinuous_apply,
    jamesBidualLimit_canonical, zero_add, smul_eq_mul] at hξ
  exact hξ.trans (mul_comm _ _)

@[simp] theorem jamesOperatorScalar_id :
    jamesOperatorScalar (𝕜 := 𝕜) p hp hpl
      (ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p)) = 1 := by
  exact jamesBidualLimit_constant p hp hpl

theorem jamesOperatorScalar_add (S T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    jamesOperatorScalar p hp hpl (S + T) =
      jamesOperatorScalar p hp hpl S + jamesOperatorScalar p hp hpl T := by
  change jamesBidualLimitLinear p hp (bidualMap (S + T) _) = _
  rw [bidualMap_add, ContinuousLinearMap.add_apply, map_add]
  rfl

theorem jamesOperatorScalar_sub (S T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    jamesOperatorScalar p hp hpl (S - T) =
      jamesOperatorScalar p hp hpl S - jamesOperatorScalar p hp hpl T := by
  change jamesBidualLimitLinear p hp (bidualMap (S - T) _) = _
  rw [bidualMap_sub, ContinuousLinearMap.sub_apply, map_sub]
  rfl

theorem jamesOperatorScalar_smul (a : 𝕜)
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    jamesOperatorScalar p hp hpl (a • T) = a * jamesOperatorScalar p hp hpl T := by
  change jamesBidualLimitLinear p hp (bidualMap (a • T) _) = _
  rw [bidualMap_smul, ContinuousLinearMap.smul_apply, map_smul]
  rfl

theorem jamesOperatorScalar_comp (S T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    jamesOperatorScalar p hp hpl (S.comp T) =
      jamesOperatorScalar p hp hpl S * jamesOperatorScalar p hp hpl T := by
  unfold jamesOperatorScalar
  rw [bidualMap_comp, ContinuousLinearMap.comp_apply]
  exact jamesBidualLimit_map p hp hpl S _

theorem james_weaklyCompact_iff_scalar_eq_zero
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    IsWeaklyCompactOperator T ↔ jamesOperatorScalar p hp hpl T = 0 := by
  rw [gantmacher_iff_bidual_mem_image]
  constructor
  · intro h
    exact (jamesBidual_mem_image_iff_limit_eq_zero p hp hpl _).mp
      (h (jamesBidualConstant (𝕜 := 𝕜) p hp hpl))
  · intro h ξ
    apply (jamesBidual_mem_image_iff_limit_eq_zero p hp hpl _).mpr
    rw [jamesBidualLimit_map p hp hpl, h, zero_mul]

theorem james_operator_scalar_residual_weaklyCompact
    (T : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) :
    IsWeaklyCompactOperator (T - jamesOperatorScalar p hp hpl T •
      ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p)) := by
  rw [james_weaklyCompact_iff_scalar_eq_zero p hp hpl, jamesOperatorScalar_sub,
    jamesOperatorScalar_smul, jamesOperatorScalar_id, mul_one, sub_self]

include hp hpl in
theorem james_projection_weaklyCompact_or_complement
    (P : JamesSequenceSpace 𝕜 p →L[𝕜] JamesSequenceSpace 𝕜 p) (hP : P.comp P = P) :
    IsWeaklyCompactOperator P ∨
      IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 (JamesSequenceSpace 𝕜 p) - P) := by
  have he := congrArg (jamesOperatorScalar p hp hpl) hP
  rw [jamesOperatorScalar_comp] at he
  have hz : jamesOperatorScalar p hp hpl P * (jamesOperatorScalar p hp hpl P - 1) = 0 := by
    rw [mul_sub, mul_one, he, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl ((james_weaklyCompact_iff_scalar_eq_zero p hp hpl P).mpr h)
  · apply Or.inr
    rw [james_weaklyCompact_iff_scalar_eq_zero p hp hpl, jamesOperatorScalar_sub,
      jamesOperatorScalar_id, sub_eq_zero.mp h, sub_self]

end ThesisCommon
