import JFA.ProjectionComparison

/-! The kernel in a comparison of projections whose difference factors
through c₀ is complemented in c₀². Reading the factorisation coordinate and
the added c₀ coordinate reconstructs every vector in this kernel. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem projection_range_comparison_kernel_retract (P Q : E →L[𝕜] E)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (A : E →L[𝕜] cZero 𝕜) (B : cZero 𝕜 →L[𝕜] E) (hBA : B.comp A = P - Q) :
    ∃ F : LinearMap.range P.toLinearMap →L[𝕜] (LinearMap.range Q.toLinearMap × cZero 𝕜),
    ∃ G : (LinearMap.range Q.toLinearMap × cZero 𝕜) →L[𝕜] LinearMap.range P.toLinearMap,
      G.comp F = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) ∧
      ∃ U : LinearMap.ker G.toLinearMap →L[𝕜] cZero 𝕜,
      ∃ V : cZero 𝕜 →L[𝕜] LinearMap.ker G.toLinearMap,
        V.comp U = ContinuousLinearMap.id 𝕜 (LinearMap.ker G.toLinearMap) := by
  let F : LinearMap.range P.toLinearMap →L[𝕜] (LinearMap.range Q.toLinearMap × cZero 𝕜) :=
    (Q.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtypeL).prod
    (A.comp (LinearMap.range P.toLinearMap).subtypeL)
  let G : (LinearMap.range Q.toLinearMap × cZero 𝕜) →L[𝕜] LinearMap.range P.toLinearMap :=
    P.rangeRestrict.comp ((LinearMap.range Q.toLinearMap).subtypeL.coprod B)
  have hGF : G.comp F = ContinuousLinearMap.id 𝕜 (LinearMap.range P.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change P (Q z.val + B (A z.val)) = z.val
    have hz : B (A z.val) = P z.val - Q z.val := congrArg (fun L => L z.val) hBA
    have heq : Q z.val + B (A z.val) = P z.val := by rw [hz]; abel
    rw [heq, projection_fix_range P hP z, projection_fix_range P hP z]
  have hgf (z : LinearMap.range P.toLinearMap) : G (F z) = z :=
    congrArg (fun L => L z) hGF
  let H := (ContinuousLinearMap.id 𝕜 (LinearMap.range Q.toLinearMap × cZero 𝕜) - F.comp G).codRestrict
    (LinearMap.ker G.toLinearMap) (fun z => by
      change G (z - F (G z)) = 0
      rw [map_sub, hgf, sub_self])
  let D : (LinearMap.range Q.toLinearMap × cZero 𝕜) →L[𝕜] (cZero 𝕜 × cZero 𝕜) :=
    ((A.comp (LinearMap.range Q.toLinearMap).subtypeL).comp
    (ContinuousLinearMap.fst 𝕜 (LinearMap.range Q.toLinearMap) (cZero 𝕜))).prod
      (ContinuousLinearMap.snd 𝕜 (LinearMap.range Q.toLinearMap) (cZero 𝕜))
  let K : (cZero 𝕜 × cZero 𝕜) →L[𝕜] (LinearMap.range Q.toLinearMap × cZero 𝕜) :=
    (Q.rangeRestrict.comp ((-B).coprod (-(P.comp B)))).prod
    (ContinuousLinearMap.snd 𝕜 (cZero 𝕜) (cZero 𝕜))
  have hKD (z : LinearMap.ker G.toLinearMap) : K (D z.val) = z.val := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [K, D, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply]
      change Q (-B (A z.val.1.val) + -(P (B z.val.2))) = z.val.1.val
      have hg : P (z.val.1.val + B z.val.2) = 0 := congrArg Subtype.val z.property
      have hpy : P z.val.1.val = -P (B z.val.2) := by
        rw [map_add] at hg
        exact eq_neg_of_add_eq_zero_left hg
      have hba : B (A z.val.1.val) = P z.val.1.val - Q z.val.1.val :=
        congrArg (fun L => L z.val.1.val) hBA
      rw [projection_fix_range Q hQ z.val.1] at hba
      have heq : -B (A z.val.1.val) + -(P (B z.val.2)) = z.val.1.val := by
        rw [hba, hpy]
        abel
      rw [heq, projection_fix_range Q hQ z.val.1]
    · rfl
  let U₀ := D.comp (LinearMap.ker G.toLinearMap).subtypeL
  let V₀ := H.comp K
  have hVU : V₀.comp U₀ = ContinuousLinearMap.id 𝕜 (LinearMap.ker G.toLinearMap) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    change K (D z.val) - F (G (K (D z.val))) = z.val
    rw [hKD]
    have hz : G z.val = 0 := z.property
    rw [hz, map_zero, sub_zero]
  let e := (cZeroSquareEquiv (𝕜 := 𝕜)).symm
  refine ⟨F, G, hGF, e.toContinuousLinearMap.comp U₀,
    V₀.comp e.symm.toContinuousLinearMap, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change V₀ (e.symm (e (U₀ z))) = z
  rw [e.symm_apply_apply]
  exact congrArg (fun L => L z) hVU

end JFA
