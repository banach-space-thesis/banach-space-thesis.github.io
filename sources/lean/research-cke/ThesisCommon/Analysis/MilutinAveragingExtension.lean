import ThesisCommon.Analysis.MilutinCylinderDensity
import Mathlib.Analysis.Normed.Operator.Completeness

/-! Extend a coherent contractive family from the cylinder functions of a
sequential compact inverse limit. This is the analytic extension step in
Rosenthal Lemma 2.12. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : ℕ → Type*} [∀ n, TopologicalSpace (K n)]
  [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)]
variable (φ : ∀ n, C(K (n + 1), K n))
variable (hφ : ∀ n, Function.Surjective (φ n))

include hφ in
theorem milutinCylinder_pullback_injective (n : ℕ) :
    Function.Injective (fun f : C(K n, 𝕜) => f.comp (milutinLimitProjection φ n)) := by
  intro f g h
  ext x
  obtain ⟨z, rfl⟩ := milutinLimitProjection_surjective φ hφ n x
  exact congrArg (fun u : C(MilutinInverseLimit φ, 𝕜) => u z) h

include hφ in
theorem norm_milutinCylinder_pullback (n : ℕ) (f : C(K n, 𝕜)) :
    ‖f.comp (milutinLimitProjection φ n)‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
    intro z
    exact f.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    obtain ⟨z, rfl⟩ := milutinLimitProjection_surjective φ hφ n x
    exact (f.comp (milutinLimitProjection φ n)).norm_coe_le_norm z

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (T : ∀ n, C(K n, 𝕜) →L[𝕜] E)
variable (hT : ∀ n (f : C(K n, 𝕜)), T (n + 1) (f.comp (φ n)) = T n f)

include hT in
theorem milutinCylinder_lift_preserving_average {n m : ℕ} (hnm : n ≤ m)
    (f : C(K n, 𝕜)) :
    ∃ g : C(K m, 𝕜), g.comp (milutinLimitProjection φ m) =
      f.comp (milutinLimitProjection φ n) ∧ T m g = T n f := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨f, rfl, rfl⟩
  | succ m hm ih =>
    obtain ⟨g, hg, hTg⟩ := ih
    refine ⟨g.comp (φ m), ?_, (hT m g).trans hTg⟩
    rw [ContinuousMap.comp_assoc, milutinLimitProjection_compatible, hg]

include hφ hT in
theorem milutinCylinder_averages_eq {n m : ℕ} (f : C(K n, 𝕜)) (g : C(K m, 𝕜))
    (hfg : f.comp (milutinLimitProjection φ n) = g.comp (milutinLimitProjection φ m)) :
    T n f = T m g := by
  obtain ⟨f', hf', hTf'⟩ := milutinCylinder_lift_preserving_average φ T hT
    (Nat.le_max_left n m) f
  obtain ⟨g', hg', hTg'⟩ := milutinCylinder_lift_preserving_average φ T hT
    (Nat.le_max_right n m) g
  have heq : f' = g' := milutinCylinder_pullback_injective φ hφ (max n m)
    (hf'.trans (hfg.trans hg'.symm))
  rw [← hTf', ← hTg', heq]

abbrev MilutinCylinderModule := (milutinCylinderAlgebra (𝕜 := 𝕜) φ).toSubalgebra.toSubmodule

def milutinCylinderAverageValue (g : MilutinCylinderModule (𝕜 := 𝕜) φ) : E :=
  T g.property.choose g.property.choose_spec.choose

include hφ hT in
theorem milutinCylinderAverageValue_eq (g : MilutinCylinderModule (𝕜 := 𝕜) φ)
    (n : ℕ) (f : C(K n, 𝕜)) (hf : f.comp (milutinLimitProjection φ n) = g.val) :
    milutinCylinderAverageValue φ T g = T n f :=
  milutinCylinder_averages_eq φ hφ T hT _ _ (g.property.choose_spec.choose_spec.trans hf.symm)

theorem milutinCylinder_common_representatives
    (f g : MilutinCylinderModule (𝕜 := 𝕜) φ) :
    ∃ (n : ℕ) (f' g' : C(K n, 𝕜)),
      f'.comp (milutinLimitProjection φ n) = f.val ∧
      g'.comp (milutinLimitProjection φ n) = g.val := by
  obtain ⟨n, hn⟩ := f.property
  obtain ⟨m, hm⟩ := g.property
  obtain ⟨f', hf'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_left n m) hn
  obtain ⟨g', hg'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_right n m) hm
  exact ⟨max n m, f', g', hf', hg'⟩

def milutinCylinderAverage (hbound : ∀ n, ‖T n‖ ≤ 1) :
    MilutinCylinderModule (𝕜 := 𝕜) φ →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := milutinCylinderAverageValue φ T
      map_add' := by
        intro f g
        obtain ⟨n, f', g', hf', hg'⟩ := milutinCylinder_common_representatives φ f g
        have hfg : (f' + g').comp (milutinLimitProjection φ n) = (f + g).val := by
          change (f' + g').comp (milutinLimitProjection φ n) = f.val + g.val
          rw [← hf', ← hg']; rfl
        rw [milutinCylinderAverageValue_eq φ hφ T hT (f + g) n (f' + g') hfg,
          milutinCylinderAverageValue_eq φ hφ T hT f n f' hf',
          milutinCylinderAverageValue_eq φ hφ T hT g n g' hg', map_add]
      map_smul' := by
        intro a f
        obtain ⟨n, f', hf'⟩ := f.property
        have haf : (a • f').comp (milutinLimitProjection φ n) = (a • f).val := by
          change (a • f').comp (milutinLimitProjection φ n) = a • f.val
          rw [← hf']; rfl
        rw [milutinCylinderAverageValue_eq φ hφ T hT (a • f) n (a • f') haf,
          milutinCylinderAverageValue_eq φ hφ T hT f n f' hf', map_smul]
        rfl }
    1 (fun f => by
      change ‖milutinCylinderAverageValue φ T f‖ ≤ 1 * ‖f‖
      obtain ⟨n, f', hf'⟩ := f.property
      rw [milutinCylinderAverageValue_eq φ hφ T hT f n f' hf', one_mul]
      calc
        ‖T n f'‖ ≤ ‖T n‖ * ‖f'‖ := (T n).le_opNorm f'
        _ ≤ ‖f'‖ := by simpa using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg f')
        _ = ‖f‖ := by
          change f'.comp (milutinLimitProjection φ n) = f.val at hf'
          rw [← norm_milutinCylinder_pullback φ hφ n f', hf']
          rfl)

theorem norm_milutinCylinderAverage_le (hbound : ∀ n, ‖T n‖ ≤ 1) :
    ‖milutinCylinderAverage φ hφ T hT hbound‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem milutinCylinderModule_denseRange :
    DenseRange (MilutinCylinderModule (𝕜 := 𝕜) φ).subtypeL :=
  denseRange_subtype_val.mpr (milutinCylinderAlgebra_dense φ)

variable [CompleteSpace E]

def milutinAverageExtension (hbound : ∀ n, ‖T n‖ ≤ 1) :
    C(MilutinInverseLimit φ, 𝕜) →L[𝕜] E :=
  (milutinCylinderAverage φ hφ T hT hbound).extend
    (MilutinCylinderModule (𝕜 := 𝕜) φ).subtypeL
    (milutinCylinderModule_denseRange φ)
    isUniformEmbedding_subtype_val.isUniformInducing

theorem milutinAverageExtension_apply_cylinder (hbound : ∀ n, ‖T n‖ ≤ 1)
    (n : ℕ) (f : C(K n, 𝕜)) :
    milutinAverageExtension φ hφ T hT hbound
      (f.comp (milutinLimitProjection φ n)) = T n f := by
  let g : MilutinCylinderModule (𝕜 := 𝕜) φ :=
    ⟨f.comp (milutinLimitProjection φ n), n, f, rfl⟩
  change (milutinCylinderAverage φ hφ T hT hbound).extend
    (MilutinCylinderModule (𝕜 := 𝕜) φ).subtypeL
    (milutinCylinderModule_denseRange φ)
    isUniformEmbedding_subtype_val.isUniformInducing
    ((MilutinCylinderModule (𝕜 := 𝕜) φ).subtypeL g) = T n f
  rw [ContinuousLinearMap.extend_eq]
  exact milutinCylinderAverageValue_eq φ hφ T hT g n f rfl

theorem norm_milutinAverageExtension_le (hbound : ∀ n, ‖T n‖ ≤ 1) :
    ‖milutinAverageExtension φ hφ T hT hbound‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp only [one_mul]
  refine (milutinCylinderModule_denseRange (𝕜 := 𝕜) φ).induction_on
    (p := fun u => ‖milutinAverageExtension φ hφ T hT hbound u‖ ≤ ‖u‖) g ?_ ?_
  · exact isClosed_le (milutinAverageExtension φ hφ T hT hbound).continuous.norm continuous_norm
  · intro f
    obtain ⟨n, f', hf'⟩ := f.property
    change f'.comp (milutinLimitProjection φ n) = f.val at hf'
    change ‖milutinAverageExtension φ hφ T hT hbound f.val‖ ≤ ‖f.val‖
    rw [← hf', milutinAverageExtension_apply_cylinder, norm_milutinCylinder_pullback φ hφ]
    exact ((T n).le_opNorm f').trans (by
      simpa using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg f'))

end ThesisCommon
