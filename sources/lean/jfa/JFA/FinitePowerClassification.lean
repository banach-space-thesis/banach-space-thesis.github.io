import JFA.FiniteProjectionModels

/-! Proposition 4.9, with the bound on the power and without a cardinality
assumption on the almost disjoint family. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open Set TopologicalSpace
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

private def conjugateOp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) : F →L[𝕜] F :=
  e.toContinuousLinearMap.comp (P.comp e.symm.toContinuousLinearMap)

private theorem conjugateOp_projection {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (P : E →L[𝕜] E) (hP : P.comp P = P) :
    (conjugateOp e P).comp (conjugateOp e P) = conjugateOp e P := by
  ext x
  change e (P (e.symm (e (P (e.symm x))))) = e (P (e.symm x))
  rw [e.symm_apply_apply]
  exact congrArg e (congrArg (fun T : E →L[𝕜] E => T (e.symm x)) hP)

private abbrev FiniteMrowkaFunctions (𝕜 : Type*) [RCLike 𝕜] (𝒜 : Set (Set ℕ)) (n : ℕ) :=
  C₀(Fin n × Mrowka 𝒜, 𝕜)

private def finiteMrowkaFunctionsEquiv (h𝒜 : IsAlmostDisjoint 𝒜) (n : ℕ) :
    FiniteMrowkaFunctions 𝕜 𝒜 n ≃L[𝕜] (Fin n → MrowkaCZero 𝕜 𝒜) := by
  letI := mrowka_t2Space h𝒜
  exact (czeroDiscreteProductEquiv.trans finiteCZeroEquiv).toContinuousLinearEquiv

private theorem finite_mrowka_projection_range_cZero_retract
    (h𝒜 : IsAlmostDisjoint 𝒜) {n : ℕ}
    (P : FiniteMrowkaFunctions 𝕜 𝒜 n →L[𝕜] FiniteMrowkaFunctions 𝕜 𝒜 n)
    (hP : P.comp P = P) (hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    ∃ U : cZero 𝕜 →L[𝕜] LinearMap.range P.toLinearMap,
    ∃ V : LinearMap.range P.toLinearMap →L[𝕜] cZero 𝕜,
      V.comp U = ContinuousLinearMap.id 𝕜 (cZero 𝕜) := by
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  letI := mrowka_t2Space h𝒜
  have hsc : JLMS.IsScattered (Fin n × Mrowka 𝒜) := discrete_prod_isScattered mrowka_isScattered
  have hPc : ¬ IsCompactOperator P :=
    fun h => hinf ((projection_compact_iff_finiteDimensional P hP).mp h)
  obtain ⟨A, B, hAB, _⟩ := JLMS.theorem_1_6_of_scatteredCZero
    (K := Fin n × Mrowka 𝒜) (L := Fin n × Mrowka 𝒜)
    hsc hsc (JLMS.cZero_admissible hsc) P hPc 1 zero_lt_one
  refine ⟨P.rangeRestrict.comp B, A.comp (LinearMap.range P.toLinearMap).subtypeL, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : cZero 𝕜 →L[𝕜] cZero 𝕜 => T x) hAB

private theorem finite_mrowka_separable_projection_range_iso
    (h𝒜 : IsAlmostDisjoint 𝒜) {n : ℕ}
    (P : FiniteMrowkaFunctions 𝕜 𝒜 n →L[𝕜] FiniteMrowkaFunctions 𝕜 𝒜 n)
    (hP : P.comp P = P) (hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap))
    (hsep : HasSeparableRange 𝕜 _ _ P) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (cZero 𝕜) := by
  obtain ⟨A, B, hAB, _⟩ := separable_mrowka_factors_cZero (D := Fin n) h𝒜 P hsep
  obtain ⟨W, hW, ⟨e⟩⟩ := projection_factorization_complemented P hP A B hAB.symm
  have hWinf : ¬ FiniteDimensional 𝕜 W := by
    intro hf
    letI := hf
    exact hinf (FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.injective)
  obtain ⟨f⟩ := cZero_complemented_infinite_iso W hW hWinf
  exact ⟨e.trans f⟩

private theorem finite_mrowka_projection_range_classification
    (h𝒜 : IsAlmostDisjoint 𝒜) (n : ℕ)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (P : FiniteMrowkaFunctions 𝕜 𝒜 n →L[𝕜] FiniteMrowkaFunctions 𝕜 𝒜 n)
    (hP : P.comp P = P) (hinf : ¬ FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap)) :
    Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (cZero 𝕜) ∨
      ∃ m ≤ n, Isomorphic 𝕜 (LinearMap.range P.toLinearMap) (Fin m → MrowkaCZero 𝕜 𝒜) := by
  let X := MrowkaCZero 𝕜 𝒜
  let E := Fin n → 𝕜
  let Z := FiniteMrowkaFunctions 𝕜 𝒜 n
  let c : InjectiveTensor 𝕜 E X ≃L[𝕜] Z :=
    finitePowerTensorEquiv.trans (finiteMrowkaFunctionsEquiv h𝒜 n).symm
  by_cases hX : SeparableSpace X
  · letI := hX
    letI : SeparableSpace Z := isomorphic_separableSpace
      ⟨(finiteMrowkaFunctionsEquiv (𝕜 := 𝕜) h𝒜 n).symm⟩ inferInstance
    exact Or.inl (finite_mrowka_separable_projection_range_iso h𝒜 P hP hinf
      (isSeparable_range P.continuous))
  let P' := conjugateOp c.symm P
  have hP' : P'.comp P' = P' := conjugateOp_projection c.symm P hP
  let Q : E →L[𝕜] E := epsilonScalarOperator hX hfew P'
  have hQ : Q.comp Q = Q := epsilonScalarOperator_projection hX hfew P' hP'
  let L' : InjectiveTensor 𝕜 E X →L[𝕜] InjectiveTensor 𝕜 E X := injectiveTensorMap Q
  let L : Z →L[𝕜] Z := conjugateOp c L'
  have hR : HasSeparableRange 𝕜 Z Z (P - L) := by
    have hs := ((epsilonRemainder_separable hX hfew P').comp_right
      c.symm.toContinuousLinearMap).comp_left c.toContinuousLinearMap
    have he : conjugateOp c (epsilonRemainder hX hfew P') = P - L := by
      apply ContinuousLinearMap.ext
      intro z
      change c (P' (c.symm z) - L' (c.symm z)) = P z - c (L' (c.symm z))
      have hback : c (P' (c.symm z)) = P z := by
        change c (c.symm (P (c (c.symm z)))) = P z
        rw [c.apply_symm_apply, c.apply_symm_apply]
      rw [map_sub, hback]
    exact he ▸ hs
  by_cases hQ0 : Q = 0
  · have hL0 : L = 0 := by
      have hL'0 : L' = 0 := by
        apply injectiveTensor_ext
        intro e x
        change injectiveTensorMap Q (injectivePure 𝕜 E X e x) = 0
        rw [injectiveTensorMap_pure, hQ0, ContinuousLinearMap.zero_apply]
        simp [injectivePure]
      apply ContinuousLinearMap.ext
      intro z
      change c (L' (c.symm z)) = 0
      rw [hL'0, ContinuousLinearMap.zero_apply, map_zero]
    exact Or.inl (finite_mrowka_separable_projection_range_iso h𝒜 P hP hinf
      (by simpa only [hL0, sub_zero] using hR))
  let r := Module.finrank 𝕜 (LinearMap.range Q.toLinearMap)
  have hr : 0 < r := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    obtain ⟨x, hx⟩ : ∃ x, Q x ≠ 0 := by
      by_contra! h
      exact hQ0 (ContinuousLinearMap.ext h)
    exact ⟨⟨Q x, ⟨x, rfl⟩⟩, fun hz => hx (congrArg Subtype.val hz)⟩
  have hrn : r ≤ n := by
    have hd := LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.range Q.toLinearMap).subtype) Subtype.val_injective
    change r ≤ Module.finrank 𝕜 (Fin n → 𝕜) at hd
    simpa only [Module.finrank_fin_fun] using hd
  let eQ := (Module.finBasisOfFinrankEq 𝕜 (LinearMap.range Q.toLinearMap)
    (rfl : Module.finrank 𝕜 (LinearMap.range Q.toLinearMap) = r)).equivFun.toContinuousLinearEquiv
  let eL : LinearMap.range L.toLinearMap ≃L[𝕜] (Fin r → X) :=
    (conjugateProjectionRangeEquiv c L' L rfl).symm.trans
      ((injectiveTensorProjectionRangeEquiv (X := X) Q hQ).trans
        ((injectiveTensorEquiv (X := X) eQ).trans finitePowerTensorEquiv))
  have hL : L.comp L = L := conjugateOp_projection c L' (injectiveTensorMap_projection Q hQ)
  have hLinf : ¬ FiniteDimensional 𝕜 (LinearMap.range L.toLinearMap) := by
    intro hfin
    letI := hfin
    have hs := isomorphic_separableSpace ⟨eL⟩
      (inferInstance : SeparableSpace (LinearMap.range L.toLinearMap))
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    rw [hj] at hs
    exact finitePower_nonseparable hX j hs
  obtain ⟨UP, VP, hVP⟩ := finite_mrowka_projection_range_cZero_retract h𝒜 P hP hinf
  obtain ⟨UL, VL, hVL⟩ := finite_mrowka_projection_range_cZero_retract h𝒜 L hL hLinf
  obtain ⟨A, B, hAB, _⟩ := separable_mrowka_factors_cZero (D := Fin n) h𝒜 (P - L) hR
  obtain ⟨e⟩ := projection_ranges_isomorphic_of_cZero_difference P L hP hL A B hAB.symm
    UP VP hVP UL VL hVL
  exact Or.inr ⟨r, hrn, ⟨e.trans eL⟩⟩

/-- Proposition 4.9: every infinite-dimensional complemented subspace of
Xⁿ is isomorphic to c₀ or to Xᵐ for some m ≤ n, where X = C₀(K_𝒜). -/
theorem proposition_4_9 (h𝒜 : IsAlmostDisjoint 𝒜) (n : ℕ)
    (hfew : HasFewOperators 𝕜 (MrowkaCZero 𝕜 𝒜))
    (W : Submodule 𝕜 (Fin n → MrowkaCZero 𝕜 𝒜)) (hW : IsComplemented 𝕜 _ W)
    (hinf : ¬ FiniteDimensional 𝕜 W) :
    Isomorphic 𝕜 W (cZero 𝕜) ∨
      ∃ m ≤ n, Isomorphic 𝕜 W (Fin m → MrowkaCZero 𝕜 𝒜) := by
  obtain ⟨P, hP, rfl⟩ := hW
  let c := (finiteMrowkaFunctionsEquiv (𝕜 := 𝕜) h𝒜 n).symm
  let Q := conjugateOp c P
  let e := conjugateProjectionRangeEquiv c P Q rfl
  have hQinf : ¬ FiniteDimensional 𝕜 (LinearMap.range Q.toLinearMap) := by
    intro hf
    letI := hf
    exact hinf (FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.injective)
  rcases finite_mrowka_projection_range_classification h𝒜 n hfew Q
      (conjugateOp_projection c P hP) hQinf with h | ⟨m, hm, ⟨f⟩⟩
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨m, hm, ⟨e.trans f⟩⟩

end JFA
