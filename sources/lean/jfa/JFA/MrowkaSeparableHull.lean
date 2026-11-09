import JFA.CZeroComplementedSubspaces
import JFA.CompactCZeroSelfSimilarity

/-! A closed countably supported containing subspace with the isomorphism
type C₀(M × ℕ). -/

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
open Set TopologicalSpace
open scoped ZeroAtInfty
namespace JFA

variable {𝕜 : Type*} [RCLike 𝕜] {𝒜 : Set (Set ℕ)}

private abbrev Point := PUnit.{1}

private theorem point_mrowka_support_iso_czero (h𝒜 : IsAlmostDisjoint 𝒜)
    (S : Set 𝒜) [Countable S] :
    Isomorphic 𝕜 (mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := Point) S) (cZero 𝕜) := by
  let W := mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := Point) S
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let H := C₀(Point × ℕ, 𝕜) × C₀(Point × S, 𝕜)
  let split : W →L[𝕜] H := mrowkaSupportSplit S h𝒜
  let J : H →L[𝕜] W := (mrowkaSupportJoin S h𝒜).codRestrict W (by
    intro a p B hB
    change mrowkaNaturalLift h𝒜 a.1 (p, Sum.inr B) +
      mrowkaFamilyLift S h𝒜 a.2 (p, Sum.inr B) = 0
    rw [mrowkaNaturalLift_inr, mrowkaFamilyLift_outside S h𝒜 _ _ _ hB, add_zero])
  have hJ (f : W) : J (split f) = f :=
    Subtype.ext (DFunLike.congr_fun (mrowkaSupportJoin_split S h𝒜) f)
  obtain ⟨A, B, hBA⟩ := exists_countable_czero_product_retract (𝕜 := 𝕜)
    (ι := Point × ℕ) (κ := Point × S)
  have hret : (J.comp B).comp (A.comp split) = ContinuousLinearMap.id 𝕜 W := by
    apply ContinuousLinearMap.ext
    intro f
    change J (B (A (split f))) = f
    rw [show B (A (split f)) = split f from DFunLike.congr_fun hBA (split f), hJ]
  have hinf : ¬ FiniteDimensional 𝕜 W := by
    intro hfin
    letI := hfin
    let a := czeroHomeomorphIsometry (𝕜 := 𝕜) (Homeomorph.punitProd ℕ)
    let V : cZero 𝕜 →L[𝕜] W := J.comp
      ((ContinuousLinearMap.inl 𝕜 _ _).comp a.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    have hV : Function.Injective V := by
      intro f g h
      apply a.symm.injective
      ext q
      have hv := congrArg (fun u : W => u.val (q.1, Sum.inl q.2)) h
      change mrowkaNaturalLift h𝒜 (a.symm f) (q.1, Sum.inl q.2) +
          mrowkaFamilyLift S h𝒜 0 (q.1, Sum.inl q.2) =
        mrowkaNaturalLift h𝒜 (a.symm g) (q.1, Sum.inl q.2) +
          mrowkaFamilyLift S h𝒜 0 (q.1, Sum.inl q.2) at hv
      simpa only [mrowkaNaturalLift_inl, map_zero, ZeroAtInftyContinuousMap.zero_apply, add_zero] using hv
    exact JLMS.cZero_not_finiteDimensional 𝕜 (FiniteDimensional.of_injective V.toLinearMap hV)
  obtain ⟨U, hU, ⟨e⟩⟩ := projection_factorization_complemented
    (ContinuousLinearMap.id 𝕜 W) (by simp) (A.comp split) (J.comp B) hret
  let eId := (LinearIsometryEquiv.ofTop W
    (LinearMap.range (ContinuousLinearMap.id 𝕜 W).toLinearMap)
    LinearMap.range_id).toContinuousLinearEquiv.symm
  have hUinf : ¬ FiniteDimensional 𝕜 U := by
    intro hfin
    letI := hfin
    exact hinf (FiniteDimensional.of_injective (eId.trans e).toLinearEquiv.toLinearMap
      (eId.trans e).injective)
  obtain ⟨f⟩ := cZero_complemented_infinite_iso U hU hUinf
  exact ⟨eId.trans (e.trans f)⟩

private def currySupportedEquiv {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (h𝒜 : IsAlmostDisjoint 𝒜) (S : Set 𝒜) :
    mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := M) S ≃L[𝕜]
      C(M, mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := Point) S) := by
  letI := mrowka_t2Space h𝒜
  letI := mrowka_locallyCompactSpace (𝒜 := 𝒜)
  let W := mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := M) S
  let W₀ := mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := Point) S
  let a := (czeroHomeomorphIsometry (𝕜 := 𝕜) (Homeomorph.punitProd (Mrowka 𝒜))).toContinuousLinearEquiv
  let e := (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := Mrowka 𝒜)).toContinuousLinearEquiv
  let F₀ := (ContinuousLinearMap.compLeftContinuous 𝕜 M a.symm.toContinuousLinearMap).comp
    (e.toContinuousLinearMap.comp W.subtypeL)
  let Fval (f : W) : C(M, W₀) :=
    ⟨fun m => ⟨F₀ f m, fun _ A hA => f.property m A hA⟩,
      (F₀ f).continuous.subtype_mk _⟩
  let F : W →L[𝕜] C(M, W₀) := LinearMap.mkContinuous
    { toFun := Fval
      map_add' := by
        intro f g
        apply ContinuousMap.ext
        intro m
        apply Subtype.ext
        exact ContinuousMap.congr_fun (map_add F₀ f g) m
      map_smul' := by
        intro c f
        apply ContinuousMap.ext
        intro m
        apply Subtype.ext
        exact ContinuousMap.congr_fun (map_smul F₀ c f) m }
    ‖F₀‖ (fun f => (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (fun m => ((F₀ f).norm_coe_le_norm m).trans (F₀.le_opNorm f)))
  let G₀ := e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.compLeftContinuous 𝕜 M (a.toContinuousLinearMap.comp W₀.subtypeL))
  let G : C(M, W₀) →L[𝕜] W := G₀.codRestrict W (by
    intro g m A hA
    change (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := Mrowka 𝒜)).symm
      (ContinuousLinearMap.compLeftContinuous 𝕜 M (a.toContinuousLinearMap.comp W₀.subtypeL) g)
      (m, Sum.inr A) = 0
    rw [czeroProductEquiv_symm_apply]
    exact (g m).property PUnit.unit A hA)
  apply ContinuousLinearEquiv.equivOfInverse F G
  · intro f
    apply Subtype.ext
    change e.symm (ContinuousLinearMap.compLeftContinuous 𝕜 M a.toContinuousLinearMap
      (ContinuousLinearMap.compLeftContinuous 𝕜 M a.symm.toContinuousLinearMap (e f.val))) = f.val
    rw [show ContinuousLinearMap.compLeftContinuous 𝕜 M a.toContinuousLinearMap
      (ContinuousLinearMap.compLeftContinuous 𝕜 M a.symm.toContinuousLinearMap (e f.val)) = e f.val from
      ContinuousMap.ext fun m => a.apply_symm_apply (e f.val m), e.symm_apply_apply]
  · intro g
    apply ContinuousMap.ext
    intro m
    apply Subtype.ext
    let v := ContinuousLinearMap.compLeftContinuous 𝕜 M (a.toContinuousLinearMap.comp W₀.subtypeL) g
    change a.symm (e (e.symm v) m) = (g m).val
    rw [e.apply_symm_apply]
    exact a.symm_apply_apply (g m).val

/-- The containment and product-model assertion of Lemma 4.6. -/
theorem mrowka_separable_closed_hull {M : Type*} [MetricSpace M] [CompactSpace M]
    (h𝒜 : IsAlmostDisjoint 𝒜) (F : Set C₀(M × Mrowka 𝒜, 𝕜)) (hF : IsSeparable F) :
    ∃ Y : Submodule 𝕜 C₀(M × Mrowka 𝒜, 𝕜), IsClosed (Y : Set C₀(M × Mrowka 𝒜, 𝕜)) ∧
      F ⊆ Y ∧ Isomorphic 𝕜 Y C₀(M × ℕ, 𝕜) := by
  let S := mrowkaSetSupport F
  letI : Countable S := (mrowka_set_support_countable hF).to_subtype
  let Y := mrowkaSupportedSubmodule (𝕜 := 𝕜) (D := M) S
  obtain ⟨e⟩ := point_mrowka_support_iso_czero (𝕜 := 𝕜) h𝒜 S
  refine ⟨Y, mrowkaSupportedSubmodule_isClosed S, ?_, ⟨(currySupportedEquiv h𝒜 S).trans
    ((continuousMapValueEquiv e).trans
      (czeroProductEquiv (𝕜 := 𝕜) (M := M) (L := ℕ)).symm.toContinuousLinearEquiv)⟩⟩
  intro f hf m A hA
  by_contra hne
  exact hA ⟨f, hf, m, hne⟩

/-- Lemma 4.6 with the convention that the compact metric space is nonempty.
Both specializations apply to the same closed containing subspace. -/
theorem lemma_4_6 {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
    (h𝒜 : IsAlmostDisjoint 𝒜) (F : Set C₀(M × Mrowka 𝒜, 𝕜)) (hF : IsSeparable F) :
    ∃ Y : Submodule 𝕜 C₀(M × Mrowka 𝒜, 𝕜), IsClosed (Y : Set C₀(M × Mrowka 𝒜, 𝕜)) ∧
      F ⊆ Y ∧ Isomorphic 𝕜 Y C₀(M × ℕ, 𝕜) ∧
      (Infinite M → Isomorphic 𝕜 Y C(M, 𝕜)) ∧
      (Finite M → Isomorphic 𝕜 Y (cZero 𝕜)) := by
  obtain ⟨Y, hY, hFY, ⟨e⟩⟩ := mrowka_separable_closed_hull h𝒜 F hF
  refine ⟨Y, hY, hFY, ⟨e⟩, ?_, ?_⟩
  · intro hM
    letI := hM
    obtain ⟨eM⟩ := infiniteCompactCZeroSelfSimilar (𝕜 := 𝕜) M
    exact ⟨e.trans (czeroCompactNatEquiv.trans eM.symm)⟩
  · intro hM
    letI := hM
    exact ⟨e.trans czeroFiniteCompactNatEquiv⟩

end JFA
