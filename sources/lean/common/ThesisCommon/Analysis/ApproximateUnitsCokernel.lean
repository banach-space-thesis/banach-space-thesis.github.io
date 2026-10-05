import ThesisCommon.Analysis.TransverseOperatorStability
import ThesisCommon.Analysis.FiniteTransverseDimension
import Mathlib.Analysis.Normed.Module.Complemented

/-! Approximation by invertible operators and a genuine finite-codimensional
closed embedding force finite codimension of its image. The argument
uses stable finite transverse blocks, not an assumed Fredholm index. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem transverse_finrank_le_of_mem_closure_units
    (T : X →L[𝕜] X) (hT : T ∈ closure {U : X →L[𝕜] X | IsUnit U})
    (E : Submodule 𝕜 X) (hE : IsClosed (E : Set X))
    [FiniteDimensional 𝕜 (X ⧸ E)]
    (hi : Function.Injective (T.comp E.subtypeL))
    (hr : IsClosed (Set.range (T.comp E.subtypeL)))
    (Z : Submodule 𝕜 X) [FiniteDimensional 𝕜 Z]
    (hZ : Disjoint (LinearMap.range (T.comp E.subtypeL).toLinearMap) Z) :
    Module.finrank 𝕜 Z ≤ Module.finrank 𝕜 (X ⧸ E) := by
  letI : CompleteSpace E := hE.completeSpace_coe
  obtain ⟨δ,hδ,hball⟩ := exists_injective_transverse_ball (T.comp E.subtypeL) hi hr Z hZ
  obtain ⟨U,hU,hUT⟩ := Metric.mem_closure_iff.mp hT δ hδ
  have hnorm : ‖U-T‖ < δ := by simpa only [dist_eq_norm, norm_sub_rev] using hUT
  have hrestrict : ‖U.comp E.subtypeL - T.comp E.subtypeL‖ ≤ ‖U-T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (U-T))
    intro x
    exact (U-T).le_opNorm x.val
  have hcop := hball (U.comp E.subtypeL) (hrestrict.trans_lt hnorm)
  obtain ⟨u,rfl⟩ := hU
  let e : X ≃L[𝕜] X := ContinuousLinearEquiv.ofUnit u
  let L : Z →ₗ[𝕜] (X ⧸ E) := E.mkQ.comp (e.symm.toLinearMap.comp Z.subtype)
  have hLzero : ∀ z, L z = 0 → z = 0 := by
    intro z hz
    have hm : e.symm z.val ∈ E := (Submodule.Quotient.mk_eq_zero E).mp hz
    let x : E := ⟨e.symm z.val,hm⟩
    have heq : ((u.val.comp E.subtypeL).coprod Z.subtypeL) (x,0) =
        ((u.val.comp E.subtypeL).coprod Z.subtypeL) (0,z) := by
      change e (e.symm z.val) + 0 = e 0 + z.val
      rw [e.apply_symm_apply, map_zero, add_zero, zero_add]
    have hh := congrArg Prod.snd (hcop heq)
    exact hh.symm
  have hL : Function.Injective L := by
    intro z w hzw
    exact sub_eq_zero.mp (hLzero (z-w) (by rw [map_sub,hzw,sub_self]))
  exact LinearMap.finrank_le_finrank_of_injective hL

theorem finiteDimensional_restricted_cokernel_of_mem_closure_units
    (T : X →L[𝕜] X) (hT : T ∈ closure {U : X →L[𝕜] X | IsUnit U})
    (E : Submodule 𝕜 X) (hE : IsClosed (E : Set X))
    [FiniteDimensional 𝕜 (X ⧸ E)]
    (hi : Function.Injective (T.comp E.subtypeL))
    (hr : IsClosed (Set.range (T.comp E.subtypeL))) :
    FiniteDimensional 𝕜 (X ⧸ LinearMap.range (T.comp E.subtypeL).toLinearMap) ∧
      Module.finrank 𝕜 (X ⧸ LinearMap.range (T.comp E.subtypeL).toLinearMap) ≤
        Module.finrank 𝕜 (X ⧸ E) := by
  apply finiteDimensional_quotient_of_transverse_finrank_bound _ _
  intro Z hZ hdisj
  letI := hZ
  exact transverse_finrank_le_of_mem_closure_units T hT E hE hi hr Z hdisj

end ThesisCommon
