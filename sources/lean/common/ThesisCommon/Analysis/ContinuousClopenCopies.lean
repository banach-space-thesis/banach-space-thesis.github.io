import ThesisCommon.Analysis.FreeNatUltrafilterCopies
import ThesisCommon.Analysis.FreeNatUltrafilterTensorDensity

/-! Contractive insertion and restriction along an actual homeomorphism
onto a clopen subset, on all vector-valued continuous functions. -/
noncomputable section
open Set Topology
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 K L X : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [CompactSpace K] [TopologicalSpace L] [CompactSpace L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def continuousClopenInsert (A : Set K) (hA : IsClopen A) (e : L ≃ₜ A) :
    C(L, X) →L[𝕜] C(K, X) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun U => if h : U ∈ A then f (e.symm ⟨U, h⟩) else 0, by
        apply continuous_iff_continuousAt.mpr
        intro U
        by_cases hU : U ∈ A
        · have h : ContinuousOn (fun V => if h : V ∈ A then f (e.symm ⟨V, h⟩) else 0) A := by
            apply continuousOn_iff_continuous_restrict.mpr
            convert f.continuous.comp e.symm.continuous using 1
            ext V
            simp only [Set.restrict_apply, dif_pos V.property, Function.comp_apply]
          exact h.continuousAt (hA.isOpen.mem_nhds hU)
        · have h : ContinuousOn (fun V => if h : V ∈ A then f (e.symm ⟨V, h⟩) else 0) Aᶜ := by
            apply continuousOn_iff_continuous_restrict.mpr
            convert (continuous_const : Continuous (fun _ : ↥(Aᶜ) => (0 : X))) using 1
            ext V
            simp only [Set.restrict_apply, dif_neg V.property]
          exact h.continuousAt (hA.isClosed.isOpen_compl.mem_nhds hU)⟩
      map_add' := fun f g => by ext U; by_cases hU : U ∈ A <;> simp [hU]
      map_smul' := fun c f => by ext U; by_cases hU : U ∈ A <;> simp [hU] }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro U
      change ‖if h : U ∈ A then f (e.symm ⟨U, h⟩) else 0‖ ≤ ‖f‖
      split_ifs with hU
      · exact f.norm_coe_le_norm _
      · simp)

@[simp] theorem continuousClopenInsert_apply (A : Set K) (hA : IsClopen A) (e : L ≃ₜ A)
    (f : C(L, X)) (U : K) : continuousClopenInsert (𝕜 := 𝕜) A hA e f U =
      if h : U ∈ A then f (e.symm ⟨U, h⟩) else 0 := rfl

theorem norm_continuousClopenInsert_le (A : Set K) (hA : IsClopen A) (e : L ≃ₜ A) :
    ‖continuousClopenInsert (𝕜 := 𝕜) (X := X) A hA e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def continuousClopenRead (A : Set K) (e : L ≃ₜ A) : C(K, X) →L[𝕜] C(L, X) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun U => f (e U).val,
        f.continuous.comp (continuous_subtype_val.comp e.continuous)⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
    1 (fun f => by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      exact fun U => f.norm_coe_le_norm (e U).val)

@[simp] theorem continuousClopenRead_apply (A : Set K) (e : L ≃ₜ A)
    (f : C(K, X)) (U : L) : continuousClopenRead (𝕜 := 𝕜) A e f U = f (e U).val := rfl

theorem norm_continuousClopenRead_le (A : Set K) (e : L ≃ₜ A) :
    ‖continuousClopenRead (𝕜 := 𝕜) (X := X) A e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem continuousClopenRead_comp_insert (A : Set K) (hA : IsClopen A) (e : L ≃ₜ A) :
    (continuousClopenRead (𝕜 := 𝕜) (X := X) A e).comp (continuousClopenInsert A hA e) =
      ContinuousLinearMap.id 𝕜 C(L, X) := by
  apply ContinuousLinearMap.ext
  intro f
  ext U
  change continuousClopenInsert (𝕜 := 𝕜) A hA e f (e U).val = f U
  rw [continuousClopenInsert_apply, dif_pos (e U).property]
  exact congrArg f (e.symm_apply_apply U)

end ThesisCommon
