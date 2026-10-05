import ThesisCommon.Analysis.UniformPrimariness
import ThesisCommon.Analysis.PrimaryDirectSum

/-! Primariness under actual bounded equivalences, and quantitative primariness
under linear isometries with exactly the same control function. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem IsPrimary.of_equiv (h : IsPrimary 𝕜 X) (e : X ≃L[𝕜] Y) : IsPrimary 𝕜 Y := by
  intro P hP
  rcases primary_product_summand h (e.trans (projectionRangeComplementEquiv P hP)) with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨e.symm.trans f⟩

def isometryConjugate (e : X ≃ₗᵢ[𝕜] Y) (P : Y →L[𝕜] Y) : X →L[𝕜] X :=
  (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp P).comp
    e.toContinuousLinearEquiv.toContinuousLinearMap

theorem norm_isometryConjugate_le (e : X ≃ₗᵢ[𝕜] Y) (P : Y →L[𝕜] Y) :
    ‖isometryConjugate e P‖ ≤ ‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
  intro x
  change ‖e.symm (P (e x))‖ ≤ ‖P‖ * ‖x‖
  simpa only [e.symm.norm_map, e.norm_map] using P.le_opNorm (e x)

theorem isometryConjugate_idempotent (e : X ≃ₗᵢ[𝕜] Y) (P : Y →L[𝕜] Y)
    (hP : P.comp P = P) : (isometryConjugate e P).comp (isometryConjugate e P) =
      isometryConjugate e P := by
  apply ContinuousLinearMap.ext
  intro x
  change e.symm (P (e (e.symm (P (e x))))) = e.symm (P (e x))
  rw [e.apply_symm_apply]
  exact congrArg e.symm (DFunLike.congr_fun hP (e x))

theorem isometryConjugate_complement (e : X ≃ₗᵢ[𝕜] Y) (P : Y →L[𝕜] Y) :
    isometryConjugate e (ContinuousLinearMap.id 𝕜 Y - P) =
      ContinuousLinearMap.id 𝕜 X - isometryConjugate e P := by
  apply ContinuousLinearMap.ext
  intro x
  change e.symm (e x - P (e x)) = x - e.symm (P (e x))
  rw [map_sub, e.symm_apply_apply]

def isometryConjugateRange (e : X ≃ₗᵢ[𝕜] Y) (P : Y →L[𝕜] Y) :
    LinearMap.range (isometryConjugate e P).toLinearMap ≃ₗᵢ[𝕜]
      LinearMap.range P.toLinearMap where
  toFun x := ⟨e x, by
    obtain ⟨z, hz⟩ := x.property
    refine ⟨e z, ?_⟩
    change e.symm (P (e z)) = x.val at hz
    exact (e.apply_symm_apply (P (e z))).symm.trans (congrArg e hz)⟩
  invFun y := ⟨e.symm y, by
    obtain ⟨z, hz⟩ := y.property
    refine ⟨e.symm z, ?_⟩
    change e.symm (P (e (e.symm z))) = e.symm y.val
    rw [e.apply_symm_apply]
    exact congrArg e.symm hz⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' a x := Subtype.ext (map_smul e a x.val)
  norm_map' x := e.norm_map x.val

theorem IsomorphicWithBound.of_isometries
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C)
    (e : X ≃ₗᵢ[𝕜] A) (f : Y ≃ₗᵢ[𝕜] B) : IsomorphicWithBound 𝕜 A B C := by
  obtain ⟨g, hg⟩ := h
  let k := (e.symm.toContinuousLinearEquiv.trans g).trans f.toContinuousLinearEquiv
  have hk : ‖k.toContinuousLinearMap‖ ≤ ‖g.toContinuousLinearMap‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g.toContinuousLinearMap)
    intro a
    change ‖f (g (e.symm a))‖ ≤ ‖g.toContinuousLinearMap‖ * ‖a‖
    simpa only [f.norm_map, e.symm.norm_map] using g.toContinuousLinearMap.le_opNorm (e.symm a)
  have hki : ‖k.symm.toContinuousLinearMap‖ ≤ ‖g.symm.toContinuousLinearMap‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g.symm.toContinuousLinearMap)
    intro b
    change ‖e (g.symm (f.symm b))‖ ≤ ‖g.symm.toContinuousLinearMap‖ * ‖b‖
    simpa only [e.norm_map, f.symm.norm_map] using g.symm.toContinuousLinearMap.le_opNorm (f.symm b)
  exact ⟨k, (mul_le_mul hk hki (norm_nonneg k.symm.toContinuousLinearMap)
    (norm_nonneg g.toContinuousLinearMap)).trans hg⟩

theorem IsUniformlyPrimary.of_isometry (h : IsUniformlyPrimary 𝕜 X)
    (e : X ≃ₗᵢ[𝕜] Y) : IsUniformlyPrimary 𝕜 Y := by
  obtain ⟨C, hmono, hC, h⟩ := h
  refine ⟨C, hmono, hC, ?_⟩
  intro P hP
  have hbound : C (max 1 ‖isometryConjugate e P‖) ≤ C (max 1 ‖P‖) :=
    hmono (show 1 ≤ max 1 ‖isometryConjugate e P‖ from le_max_left _ _)
      (show 1 ≤ max 1 ‖P‖ from le_max_left _ _)
      (max_le_max_left 1 (norm_isometryConjugate_le e P))
  rcases h (isometryConjugate e P) (isometryConjugate_idempotent e P hP) with h | h
  · obtain ⟨g, hg⟩ := h.of_isometries e (isometryConjugateRange e P)
    exact Or.inl ⟨g, hg.trans hbound⟩
  · rw [← isometryConjugate_complement e P] at h
    obtain ⟨g, hg⟩ := h.of_isometries e (isometryConjugateRange e (ContinuousLinearMap.id 𝕜 Y - P))
    exact Or.inr ⟨g, hg.trans hbound⟩

end ThesisCommon
