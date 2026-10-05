import PEMS.DeBlasiProperties
import PEMS.ALMainFactorization
import ThesisCommon.Analysis.RCLikeEllOneWeakCompact
import ThesisCommon.Analysis.LpCompactCoordinates

/-! Sharp De Blasi lower bounds from actual ℓ¹ factorizations. Schur
compactness makes the coordinates of the weakly compact approximating set
uniformly small, while the factored unit vectors retain a fixed coordinate. -/
noncomputable section
open Set Filter Topology ThesisCommon
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem ellOne_factorization_constant_le_deBlasiOperator
    (T : E →L[𝕜] F) (U : F →L[𝕜] EllOne 𝕜) (V : EllOne 𝕜 →L[𝕜] E)
    (hfac : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜)) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ deBlasiOperator T := by
  by_cases hU : ‖U‖ = 0
  · simpa [hU] using deBlasiOperator_nonneg T
  by_cases hV : ‖V‖ = 0
  · simpa [hV] using deBlasiOperator_nonneg T
  have hUp : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg U) (Ne.symm hU)
  have hVp : 0 < ‖V‖ := lt_of_le_of_ne (norm_nonneg V) (Ne.symm hV)
  apply le_csInf
  · refine ⟨‖T‖ + 1, by positivity, {0}, by simp, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    refine ⟨0, by simp, ?_⟩
    simpa using ((T.le_opNorm x).trans
      (mul_le_of_le_one_right (norm_nonneg T) hx')).trans (by linarith : ‖T‖ ≤ ‖T‖ + 1)
  · rintro ε ⟨hε, D, hD, happ⟩
    have hcompact := isCompact_norm_of_weakScalarEllOne
      (hD.image (WeakSpace.map U).continuous)
    have hbound : ‖V‖⁻¹ ≤ ‖U‖ * ε := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      obtain ⟨n, hn⟩ := (IsCompact.lp_coordinates_uniformly_small
        (by simp) hcompact hδ).exists
      let e : EllOne 𝕜 := lp.single 1 n 1
      have he : ‖e‖ = 1 := by simp [e, lp.norm_single (by simp : (0 : ENNReal) < 1)]
      let a : 𝕜 := (‖V‖⁻¹ : ℝ)
      have ha : ‖a‖ = ‖V‖⁻¹ := by simp [a, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg V))]
      let x : E := a • V e
      have hx : ‖x‖ ≤ 1 := by
        calc
          ‖x‖ = ‖V‖⁻¹ * ‖V e‖ := by dsimp only [x]; rw [norm_smul, ha]
          _ ≤ ‖V‖⁻¹ * (‖V‖ * ‖e‖) :=
            mul_le_mul_of_nonneg_left (V.le_opNorm e) (inv_nonneg.mpr (norm_nonneg V))
          _ = 1 := by rw [he, mul_one, inv_mul_cancel₀ hV]
      obtain ⟨y, hy, hxy⟩ := happ (T x) ⟨x, by simpa using hx, rfl⟩
      have hymem : U y ∈ (toWeakSpace 𝕜 (EllOne 𝕜)).symm ''
          (WeakSpace.map U '' (toWeakSpace 𝕜 F '' D)) := by
        exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      have hsmall := hn (U y) hymem
      have hUT : U (T x) = a • e := by
        have h := congrArg (fun R : EllOne 𝕜 →L[𝕜] EllOne 𝕜 => R e) hfac
        simpa only [x, map_smul, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply] using congrArg (fun z => a • z) h
      have hcoord : ‖a - U y n‖ ≤ ‖U‖ * ε := by
        calc
          ‖a - U y n‖ = ‖(U (T x - y)) n‖ := by simp [map_sub, hUT, e]
          _ ≤ ‖U (T x - y)‖ := lp.norm_apply_le_norm (by simp) _ n
          _ ≤ ‖U‖ * ‖T x - y‖ := U.le_opNorm _
          _ ≤ ‖U‖ * ε := mul_le_mul_of_nonneg_left hxy (norm_nonneg U)
      have htri := norm_le_norm_sub_add a (U y n)
      rw [ha] at htri
      linarith
    calc
      ‖U‖⁻¹ * ‖V‖⁻¹ ≤ ‖U‖⁻¹ * (‖U‖ * ε) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg U))
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hU, one_mul]

theorem factorizationSup_ellOne_le_deBlasiOperator (T : E →L[𝕜] F) :
    factorizationSup (EllOne 𝕜) T ≤ deBlasiOperator T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hfac, rfl⟩)
  · exact deBlasiOperator_nonneg T
  · exact ellOne_factorization_constant_le_deBlasiOperator T U V hfac

theorem deBlasiOperator_eq_weakEssentialNorm_of_ellOne_factorization
    (T : E →L[𝕜] F)
    (h : weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    deBlasiOperator T = weakEssentialNorm T :=
  le_antisymm (deBlasiOperator_le_weakEssentialNorm T)
    (h.symm ▸ factorizationSup_ellOne_le_deBlasiOperator T)

end PEMS
