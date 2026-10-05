import ThesisCommon.Analysis.CountablePartitionReindex
import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.LpCoordinateFactorization
import ThesisCommon.Analysis.CoordinateMaskSubspaces
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! An actual isometric coordinate change for a countable partition. Each
block is paired with the natural numbers before it becomes one model fibre.
Coordinate masks and block compressions are transported explicitly. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ ι X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
variable (B : ι → Set Γ) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
  (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ)

def lpPartitionReadIsometry :
    lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p ≃ₗᵢ[𝕜]
      lp (fun _ : ι => lp (fun _ : ℕ => X) p) p :=
  (lpProductFlattenIsometry p hp (Equiv.refl (Γ × ℕ))).trans
    (lpProductFlattenIsometry p hp (partitionPairEquiv B hB hcover φ)).symm

@[simp] theorem lpPartitionReadIsometry_apply
    (x : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (i : ι) (n : ℕ) :
    lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ x i n =
      x ((φ i).symm n).1.val ((φ i).symm n).2 := rfl

theorem lpPartitionReadIsometry_mask
    (x : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (i : ι) :
    lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ
        (lpCoordinateProjection (𝕜 := 𝕜) p (B i) x) =
      lp.single p i (lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ x i) := by
  apply lp.ext
  funext j
  apply lp.ext
  funext n
  have hmem : ((φ j).symm n).1.val ∈ B i ↔ j = i :=
    partitionPairEquiv_fst_mem_iff B hB hcover φ i j n
  by_cases hji : j = i
  · subst j
    simp only [lpPartitionReadIsometry_apply, lpCoordinateProjection_apply,
      if_pos ((φ i).symm n).1.property, lp.single_apply_self]
  · simp only [lpPartitionReadIsometry_apply, lpCoordinateProjection_apply,
      if_neg (fun h => hji (hmem.mp h)),
      lp.single_apply_ne (E := fun _ : ι => lp (fun _ : ℕ => X) p) p i _ hji,
      lp.coeFn_zero, Pi.zero_apply]

theorem lpPartitionReadIsometry_symm_single
    (x : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (i : ι) :
    (lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ).symm
      (lp.single p i (lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ x i)) =
        lpCoordinateProjection (𝕜 := 𝕜) p (B i) x := by
  rw [← lpPartitionReadIsometry_mask, LinearIsometryEquiv.symm_apply_apply]

theorem lpPartitionReadIsometry_single_supported (i : ι) (x : lp (fun _ : ℕ => X) p) :
    (lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ).symm (lp.single p i x) ∈
      lpSupportedSubmodule (𝕜 := 𝕜) p (B i) := by
  let E := lpPartitionReadIsometry (𝕜 := 𝕜) (X := X) p hp B hB hcover φ
  have hm := lpPartitionReadIsometry_symm_single (𝕜 := 𝕜) p hp B hB hcover φ
    (E.symm (lp.single p i x)) i
  change E.symm (lp.single p i (E (E.symm (lp.single p i x)) i)) = _ at hm
  simp only [LinearIsometryEquiv.apply_symm_apply, lp.single_apply_self] at hm
  intro γ hγ
  rw [hm, lpCoordinateProjection_apply, if_neg hγ]

theorem lpPartitionReadIsometry_entry_idempotent
    (P : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p →L[𝕜]
      lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (i : ι)
    (hPi : (lpBlockCompression p P (B i)).comp (lpBlockCompression p P (B i)) =
      lpBlockCompression p P (B i)) :
    let E := lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ
    let Q := operatorTransport E E P
    (lpCoordinateEntry p Q i i).comp (lpCoordinateEntry p Q i i) =
      lpCoordinateEntry p Q i i := by
  dsimp only
  let E := lpPartitionReadIsometry (𝕜 := 𝕜) (X := X) p hp B hB hcover φ
  apply ContinuousLinearMap.ext
  intro x
  let y : lpSupportedSubmodule (𝕜 := 𝕜) p (B i) :=
    ⟨E.symm (lp.single p i x), lpPartitionReadIsometry_single_supported p hp B hB hcover φ i x⟩
  have h := congrArg (fun T => (T y).val) hPi
  change lpCoordinateProjection p (B i) (P (lpCoordinateProjection p (B i) (P y.val))) =
    lpCoordinateProjection p (B i) (P y.val) at h
  have hh := congrArg (fun z => E z i) h
  simp only [E, lpPartitionReadIsometry_mask, lp.single_apply_self] at hh
  change E (P (E.symm (lp.single p i (E (P y.val) i)))) i = E (P y.val) i
  rw [lpPartitionReadIsometry_symm_single]
  exact hh

theorem lpPartitionReadIsometry_entry_zero
    (P : lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p →L[𝕜]
      lp (fun _ : Γ => lp (fun _ : ℕ => X) p) p) (i j : ι)
    (hPij : ((lpCoordinateProjection (𝕜 := 𝕜) p (B j)).comp P).comp
      (lpSupportedSubmodule (𝕜 := 𝕜) p (B i)).subtypeL = 0) :
    let E := lpPartitionReadIsometry (𝕜 := 𝕜) p hp B hB hcover φ
    lpCoordinateEntry p (operatorTransport E E P) j i = 0 := by
  dsimp only
  let E := lpPartitionReadIsometry (𝕜 := 𝕜) (X := X) p hp B hB hcover φ
  apply ContinuousLinearMap.ext
  intro x
  let y : lpSupportedSubmodule (𝕜 := 𝕜) p (B i) :=
    ⟨E.symm (lp.single p i x), lpPartitionReadIsometry_single_supported p hp B hB hcover φ i x⟩
  have h := congrArg (fun T => T y) hPij
  change lpCoordinateProjection p (B j) (P y.val) = 0 at h
  have hh := congrArg (fun z => E z j) h
  simpa only [E, lpPartitionReadIsometry_mask, lp.single_apply_self, map_zero,
    lp.coeFn_zero, Pi.zero_apply] using hh

end ThesisCommon
