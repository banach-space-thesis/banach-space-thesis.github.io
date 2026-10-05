import ThesisCommon.Analysis.ApproximateUnitsCokernel
import ThesisCommon.Analysis.TransverseQuotientEquivalence
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! An operator approximable by invertibles, with a closed embedding on
a finite-codimensional subspace, has a genuine finite-rank correction
which is invertible. All dimensions are derived from actual maps. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem transverse_finrank_eq_of_mem_closure_units
    (T : X →L[𝕜] X) (hT : T ∈ closure {U : X →L[𝕜] X | IsUnit U})
    (E : Submodule 𝕜 X) (hE : IsClosed (E : Set X))
    [FiniteDimensional 𝕜 (X ⧸ E)]
    (hi : Function.Injective (T.comp E.subtypeL))
    (Z : Submodule 𝕜 X) [FiniteDimensional 𝕜 Z]
    (hZ : IsCompl (LinearMap.range (T.comp E.subtypeL).toLinearMap) Z) :
    Module.finrank 𝕜 Z = Module.finrank 𝕜 (X ⧸ E) := by
  letI : CompleteSpace E := hE.completeSpace_coe
  letI : CompleteSpace Z := Z.closed_of_finiteDimensional.completeSpace_coe
  let C : (E × Z) ≃L[𝕜] X :=
    (T.comp E.subtypeL).coprodSubtypeLEquivOfIsCompl hZ (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp C.nhds
  obtain ⟨U,hU,hUT⟩ := Metric.mem_closure_iff.mp hT δ hδ
  have hnorm : ‖U-T‖ < δ := by simpa only [dist_eq_norm,norm_sub_rev] using hUT
  let V : E × Z →L[𝕜] X := (U.comp E.subtypeL).coprod Z.subtypeL
  have hVC : ‖V-C.toContinuousLinearMap‖ ≤ ‖U-T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (U-T))
    rintro ⟨x,z⟩
    have he : (V-C.toContinuousLinearMap) (x,z) = (U-T) x.val := by
      change (U x.val+z.val)-(T x.val+z.val) = U x.val-T x.val
      abel
    rw [he]
    exact ((U-T).le_opNorm x.val).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (x,z)) (norm_nonneg (U-T)))
  have hV : V ∈ Set.range (fun e : (E × Z) ≃L[𝕜] X => e.toContinuousLinearMap) :=
    hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hVC.trans_lt hnorm)
  obtain ⟨eV,heV⟩ := hV
  obtain ⟨u,rfl⟩ := hU
  have hbij : Function.Bijective
      (((ContinuousLinearEquiv.ofUnit u).toLinearEquiv.toLinearMap.comp E.subtype).coprod Z.subtype) := by
    change Function.Bijective (V : E × Z → X)
    rw [← heV]
    exact eV.bijective
  exact (transverseQuotientEquiv (ContinuousLinearEquiv.ofUnit u).toLinearEquiv E Z hbij).finrank_eq

theorem exists_finiteRank_invertible_correction_of_mem_closure_units
    (T : X →L[𝕜] X) (hT : T ∈ closure {U : X →L[𝕜] X | IsUnit U})
    (E : Submodule 𝕜 X) (hE : IsClosed (E : Set X))
    [FiniteDimensional 𝕜 (X ⧸ E)]
    (hi : Function.Injective (T.comp E.subtypeL))
    (hr : IsClosed (Set.range (T.comp E.subtypeL))) :
    ∃ K : X →L[𝕜] X, FiniteDimensional 𝕜 (LinearMap.range K.toLinearMap) ∧
      IsUnit (T+K) := by
  letI : CompleteSpace E := hE.completeSpace_coe
  let R := LinearMap.range (T.comp E.subtypeL).toLinearMap
  letI : FiniteDimensional 𝕜 (X ⧸ R) :=
    (finiteDimensional_restricted_cokernel_of_mem_closure_units T hT E hE hi hr).1
  obtain ⟨Z,hZ⟩ := R.exists_isCompl
  letI : FiniteDimensional 𝕜 Z := (R.quotientEquivOfIsCompl Z hZ).finiteDimensional
  letI : CompleteSpace Z := Z.closed_of_finiteDimensional.completeSpace_coe
  obtain ⟨F,hF⟩ := E.exists_isCompl
  letI : FiniteDimensional 𝕜 F := (E.quotientEquivOfIsCompl F hF).finiteDimensional
  have hdim : Module.finrank 𝕜 F = Module.finrank 𝕜 Z :=
    (E.quotientEquivOfIsCompl F hF).finrank_eq.symm.trans
      (transverse_finrank_eq_of_mem_closure_units T hT E hE hi Z hZ).symm
  let d : F ≃L[𝕜] Z := ContinuousLinearEquiv.ofFinrankEq hdim
  let ep : (E × F) ≃L[𝕜] X := E.prodEquivOfClosedCompl F hF hE F.closed_of_finiteDimensional
  let C : (E × Z) ≃L[𝕜] X :=
    (T.comp E.subtypeL).coprodSubtypeLEquivOfIsCompl hZ (LinearMap.ker_eq_bot.mpr hi)
  let G : X ≃L[𝕜] X := ep.symm.trans ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr d) |>.trans C
  let K : X →L[𝕜] X := G.toContinuousLinearMap-T
  have hKE : E ≤ LinearMap.ker K.toLinearMap := by
    intro x hx
    change G x-T x = 0
    have hep : ep.symm x = (⟨x,hx⟩,0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left E F hF ⟨x,hx⟩
    change C (((ContinuousLinearEquiv.refl 𝕜 E).prodCongr d) (ep.symm x))-T x = 0
    rw [hep]
    change (T x+(d 0).val)-T x = 0
    rw [map_zero,ZeroMemClass.coe_zero,add_zero,sub_self]
  have hfinite : FiniteDimensional 𝕜 (LinearMap.range K.toLinearMap) := by
    let L := E.liftQ K.toLinearMap hKE
    haveI : FiniteDimensional 𝕜 (LinearMap.range L) := inferInstance
    have he : LinearMap.range L = LinearMap.range K.toLinearMap := E.range_liftQ K.toLinearMap hKE
    exact he ▸ inferInstance
  refine ⟨K,hfinite,?_⟩
  have he : T+K = G.toContinuousLinearMap := by dsimp only [K]; abel
  rw [he]
  exact ⟨G.toUnit,rfl⟩

end ThesisCommon
