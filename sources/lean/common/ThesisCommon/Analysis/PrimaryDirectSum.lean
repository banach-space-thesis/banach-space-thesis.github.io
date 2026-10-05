import ThesisCommon.Analysis.Primary
import ThesisCommon.Analysis.ProjectionDecomposition

/-! Primariness for arbitrary bounded product decompositions. Retractions
and insertions identify the actual projection ranges with their summands;
no completeness or isometry of the product decomposition is assumed.
-/
noncomputable section
namespace ThesisCommon
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A bounded insertion with a bounded left inverse identifies its
projection range with the inserted space, using the inherited range norm. -/
def splitProjectionRangeEquiv (J : Y →L[𝕜] X) (R : X →L[𝕜] Y)
    (hRJ : R.comp J = ContinuousLinearMap.id 𝕜 Y) :
    LinearMap.range (J.comp R).toLinearMap ≃L[𝕜] Y := by
  have h (y : Y) : R (J y) = y := DFunLike.congr_fun hRJ y
  let M := LinearMap.range (J.comp R).toLinearMap
  let f : M →L[𝕜] Y := R.comp M.subtypeL
  let g : Y →L[𝕜] M := J.codRestrict M (fun y => by
    refine ⟨J y, ?_⟩
    change J (R (J y)) = J y
    rw [h])
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · intro x
    apply Subtype.ext
    change J (R x.val) = x.val
    obtain ⟨z, hz⟩ := x.property
    change J (R z) = x.val at hz
    rw [← hz, h]
  · intro y
    exact h y

/-- Primariness applies to every actual bounded isomorphism with a product.
The two projections are obtained by conjugating the coordinate projections. -/
theorem primary_product_summand (hX : IsPrimary 𝕜 X) (e : X ≃L[𝕜] Y × Z) :
    Nonempty (X ≃L[𝕜] Y) ∨ Nonempty (X ≃L[𝕜] Z) := by
  let J : Y →L[𝕜] X := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 Y Z)
  let R : X →L[𝕜] Y := (ContinuousLinearMap.fst 𝕜 Y Z).comp e.toContinuousLinearMap
  let K : Z →L[𝕜] X := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 Y Z)
  let S : X →L[𝕜] Z := (ContinuousLinearMap.snd 𝕜 Y Z).comp e.toContinuousLinearMap
  have hRJ : R.comp J = ContinuousLinearMap.id 𝕜 Y := by
    apply ContinuousLinearMap.ext
    intro y
    change (e (e.symm (y, 0))).1 = y
    simp
  have hSK : S.comp K = ContinuousLinearMap.id 𝕜 Z := by
    apply ContinuousLinearMap.ext
    intro z
    change (e (e.symm (0, z))).2 = z
    simp
  let P := J.comp R
  have hP : P.comp P = P := by
    apply ContinuousLinearMap.ext
    intro x
    change J ((R.comp J) (R x)) = J (R x)
    rw [hRJ]
    rfl
  have hQ : ContinuousLinearMap.id 𝕜 X - P = K.comp S := by
    apply ContinuousLinearMap.ext
    intro x
    apply e.injective
    change e (x - e.symm ((e x).1, 0)) = e (e.symm (0, (e x).2))
    rw [map_sub, e.apply_symm_apply, e.apply_symm_apply]
    exact Prod.ext (sub_self _) (sub_zero _)
  rcases hX P hP with hY | hZ
  · obtain ⟨eY⟩ := hY
    exact Or.inl ⟨eY.trans (splitProjectionRangeEquiv J R hRJ)⟩
  · rw [hQ] at hZ
    obtain ⟨eZ⟩ := hZ
    exact Or.inr ⟨eZ.trans (splitProjectionRangeEquiv K S hSK)⟩

/-- The actual range of a bounded projection is closed, including the
zero projection. -/
theorem projectionRange_isClosed (P : X →L[𝕜] X) (hP : P.comp P = P) :
    IsClosed (LinearMap.range P.toLinearMap : Set X) := by
  have hPP (x : X) : P (P x) = P x := DFunLike.congr_fun hP x
  have heq : (LinearMap.range P.toLinearMap : Set X) = {x | P x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hPP y
    · intro hx
      exact ⟨x, hx⟩
  rw [heq]
  exact isClosed_eq P.continuous continuous_id

/-- Closedness of the complementary projection range. -/
theorem projectionComplementRange_isClosed (P : X →L[𝕜] X) (hP : P.comp P = P) :
    IsClosed (LinearMap.range (ContinuousLinearMap.id 𝕜 X - P).toLinearMap : Set X) :=
  projectionRange_isClosed _ (complementary_projection hP)

/-- A bounded projection splits X into its range and the actual range of
its complementary projection, precisely the two summands in IsPrimary. -/
def projectionRangeComplementEquiv (P : X →L[𝕜] X) (hP : P.comp P = P) :
    X ≃L[𝕜] LinearMap.range P.toLinearMap ×
      LinearMap.range (ContinuousLinearMap.id 𝕜 X - P).toLinearMap := by
  have hPP (x : X) : P (P x) = P x := DFunLike.congr_fun hP x
  let Q := ContinuousLinearMap.id 𝕜 X - P
  refine ContinuousLinearEquiv.equivOfInverse (P.rangeRestrict.prod Q.rangeRestrict)
    ((LinearMap.range P.toLinearMap).subtypeL.coprod
      (LinearMap.range Q.toLinearMap).subtypeL) ?_ ?_
  · intro x
    change P x + (x - P x) = x
    rw [add_comm, sub_add_cancel]
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hPx : P x = x := by
      obtain ⟨z, rfl⟩ := hx
      exact hPP z
    have hPy : P y = 0 := by
      obtain ⟨z, hz⟩ := hy
      change z - P z = y at hz
      rw [← hz, map_sub, hPP, sub_self]
    apply Prod.ext <;> apply Subtype.ext
    · change P (x + y) = x
      rw [map_add, hPx, hPy, add_zero]
    · change x + y - P (x + y) = y
      rw [map_add, hPx, hPy, add_zero, add_sub_cancel_left]

end ThesisCommon
