import ThesisCommon.Analysis.CountablePartitionReindex
import ThesisCommon.Analysis.CZeroArbitraryProducts
import ThesisCommon.Analysis.CZeroCoordinateFactorization
import ThesisCommon.Analysis.OperatorIsometryTransport

/-! Countable nonempty coordinate blocks of c₀ become countable-model
fibres under an actual isometry. Block masks and compressions are preserved. -/
noncomputable section
open scoped ZeroAtInfty
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ ι X : Type*} [RCLike 𝕜]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  [TopologicalSpace ι] [DiscreteTopology ι]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (B : ι → Set Γ) (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
  (hcover : (⋃ i, B i) = Set.univ) (φ : ∀ i, B i × ℕ ≃ ℕ)

def cZeroPartitionReadIsometry : C₀(Γ, C₀(ℕ, X)) ≃ₗᵢ[𝕜] C₀(ι, C₀(ℕ, X)) :=
  (cZeroProductFlattenIsometry (Equiv.refl (Γ × ℕ))).trans
    (cZeroProductFlattenIsometry (partitionPairEquiv B hB hcover φ)).symm

@[simp] theorem cZeroPartitionReadIsometry_apply
    (x : C₀(Γ, C₀(ℕ, X))) (i : ι) (n : ℕ) :
    cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ x i n =
      x ((φ i).symm n).1.val ((φ i).symm n).2 := rfl

theorem cZeroPartitionReadIsometry_mask
    (x : C₀(Γ, C₀(ℕ, X))) (i : ι) :
    cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
        (cZeroCoordinateProjection (𝕜 := 𝕜) (B i) x) =
      cZeroSingleAt i (cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ x i) := by
  ext j n
  have hmem : ((φ j).symm n).1.val ∈ B i ↔ j = i :=
    partitionPairEquiv_fst_mem_iff B hB hcover φ i j n
  by_cases hji : j = i
  · subst j
    simp only [cZeroPartitionReadIsometry_apply, cZeroCoordinateProjection_apply,
      if_pos ((φ i).symm n).1.property, cZeroSingleAt_apply, if_true]
  · simp only [cZeroPartitionReadIsometry_apply, cZeroCoordinateProjection_apply,
      if_neg (fun h => hji (hmem.mp h)), cZeroSingleAt_apply, if_neg hji]
    rfl

theorem cZeroPartitionReadIsometry_symm_single
    (x : C₀(Γ, C₀(ℕ, X))) (i : ι) :
    (cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ).symm
      (cZeroSingleAt i (cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ x i)) =
        cZeroCoordinateProjection (𝕜 := 𝕜) (B i) x := by
  rw [← cZeroPartitionReadIsometry_mask, LinearIsometryEquiv.symm_apply_apply]

theorem cZeroPartitionReadIsometry_single_supported (i : ι) (x : C₀(ℕ, X)) :
    (cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ).symm (cZeroSingleAt i x) ∈
      cZeroSupportedSubmodule (𝕜 := 𝕜) (B i) := by
  let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
  have hm := cZeroPartitionReadIsometry_symm_single (𝕜 := 𝕜) B hB hcover φ
    (E.symm (cZeroSingleAt i x)) i
  change E.symm (cZeroSingleAt i (E (E.symm (cZeroSingleAt i x)) i)) = _ at hm
  simp only [LinearIsometryEquiv.apply_symm_apply, cZeroSingleAt_apply, if_true] at hm
  intro γ hγ
  rw [hm, cZeroCoordinateProjection_apply, if_neg hγ]

theorem cZeroPartitionReadIsometry_entry_idempotent
    (P : C₀(Γ, C₀(ℕ, X)) →L[𝕜] C₀(Γ, C₀(ℕ, X))) (i : ι)
    (hPi : (cZeroBlockCompression P (B i)).comp (cZeroBlockCompression P (B i)) =
      cZeroBlockCompression P (B i)) :
    let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
    let Q := operatorTransport E E P
    (cZeroCoordinateEntry Q i i).comp (cZeroCoordinateEntry Q i i) =
      cZeroCoordinateEntry Q i i := by
  dsimp only
  let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
  apply ContinuousLinearMap.ext
  intro x
  let y : cZeroSupportedSubmodule (𝕜 := 𝕜) (B i) :=
    ⟨E.symm (cZeroSingleAt i x), cZeroPartitionReadIsometry_single_supported B hB hcover φ i x⟩
  have h := congrArg (fun T => (T y).val) hPi
  change cZeroCoordinateProjection (B i) (P (cZeroCoordinateProjection (B i) (P y.val))) =
    cZeroCoordinateProjection (B i) (P y.val) at h
  have hh := congrArg (fun z => E z i) h
  simp only [E, cZeroPartitionReadIsometry_mask, cZeroSingleAt_apply, if_true] at hh
  change E (P (E.symm (cZeroSingleAt i (E (P y.val) i)))) i = E (P y.val) i
  rw [cZeroPartitionReadIsometry_symm_single]
  exact hh

theorem cZeroPartitionReadIsometry_entry_zero
    (P : C₀(Γ, C₀(ℕ, X)) →L[𝕜] C₀(Γ, C₀(ℕ, X))) (i j : ι)
    (hPij : ((cZeroCoordinateProjection (𝕜 := 𝕜) (B j)).comp P).comp
      (cZeroSupportedSubmodule (𝕜 := 𝕜) (X := C₀(ℕ, X)) (B i)).subtypeL = 0) :
    let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
    cZeroCoordinateEntry (operatorTransport E E P) j i = 0 := by
  dsimp only
  let E := cZeroPartitionReadIsometry (𝕜 := 𝕜) (X := X) B hB hcover φ
  apply ContinuousLinearMap.ext
  intro x
  let y : cZeroSupportedSubmodule (𝕜 := 𝕜) (B i) :=
    ⟨E.symm (cZeroSingleAt i x), cZeroPartitionReadIsometry_single_supported B hB hcover φ i x⟩
  have h := congrArg (fun T => T y) hPij
  change cZeroCoordinateProjection (B j) (P y.val) = 0 at h
  have hh := congrArg (fun z => E z j) h
  simpa only [E, cZeroPartitionReadIsometry_mask, cZeroSingleAt_apply, if_true,
    map_zero, ZeroAtInftyContinuousMap.zero_apply] using hh

end ThesisCommon

