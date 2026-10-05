import JFA.ScalarCoefficient
import JFA.RightSlice
import JFA.CountableDual
import JFA.SeparableSubspace

/-! Representing the scalar parts of all slices of an operator X → F ⊗ε X
by a single vector of F. This is the central scalar extraction in Theorem 1.1. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {F X : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

-- Explicit projections avoid the pinned release's instance-search gap for
-- operators whose target is itself a subspace of an operator space.
instance sliceOperatorsContinuousAdd : ContinuousAdd (X →L[𝕜] InjectiveTensor 𝕜 F X) :=
  (ContinuousLinearMap.topologicalAddGroup :
    IsTopologicalAddGroup (X →L[𝕜] InjectiveTensor 𝕜 F X)).toContinuousAdd

instance sliceOperatorsNormedAddCommGroup : NormedAddCommGroup (X →L[𝕜] InjectiveTensor 𝕜 F X) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance sliceOperatorsNormedSpace : NormedSpace 𝕜 (X →L[𝕜] InjectiveTensor 𝕜 F X) :=
  ContinuousLinearMap.toNormedSpace

def sliceOperator (K : X →L[𝕜] InjectiveTensor 𝕜 F X) (φ : F →L[𝕜] 𝕜) : X →L[𝕜] X :=
  (leftSlice φ).comp K

theorem exists_representative_for_sequence (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (K : X →L[𝕜] InjectiveTensor 𝕜 F X)
    (φ : ℕ → F →L[𝕜] 𝕜) :
    ∃ f : F, ∀ n, φ n f = scalarCoefficient hX hfew (sliceOperator K (φ n)) := by
  let R := fun n => scalarRemainder hX hfew (sliceOperator K (φ n))
  obtain ⟨Y, hclosed, hsep, hY⟩ := exists_common_separable_subspace R
    (fun n => scalarRemainder_separable hX hfew (sliceOperator K (φ n)))
  obtain ⟨ψ, x, hx, hψ⟩ := exists_annihilator_of_separable hX Y hclosed hsep
  refine ⟨rightSlice ψ (K x), ?_⟩
  intro n
  have hzero : ψ (R n x) = 0 := hψ _ (hY n x)
  calc
    φ n (rightSlice ψ (K x)) = ψ (sliceOperator K (φ n) x) := rightSlice_pairing ψ (φ n) _
    _ = ψ ((scalarCoefficient hX hfew (sliceOperator K (φ n)) •
        ContinuousLinearMap.id 𝕜 X + R n) x) :=
      congrArg (fun V : X →L[𝕜] X => ψ (V x)) (scalar_decomposition hX hfew _)
    _ = scalarCoefficient hX hfew (sliceOperator K (φ n)) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, map_add, map_smul, hzero, hx, smul_eq_mul, mul_one, add_zero]

theorem exists_unique_scalar_representative [SeparableSpace F]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K : X →L[𝕜] InjectiveTensor 𝕜 F X) :
    ∃! f : F, ∀ φ : F →L[𝕜] 𝕜,
      φ f = scalarCoefficient hX hfew (sliceOperator K φ) := by
  obtain ⟨f, hf⟩ := exists_representative_for_sequence hX hfew K
    (normingSequence (𝕜 := 𝕜) (E := F))
  refine ⟨f, ?_, ?_⟩
  · intro φ
    let φ' : ℕ → F →L[𝕜] 𝕜
      | 0 => φ
      | n + 1 => normingSequence (𝕜 := 𝕜) (E := F) n
    obtain ⟨g, hg⟩ := exists_representative_for_sequence hX hfew K φ'
    have hgf : g = f := eq_of_normingSequence_eq (𝕜 := 𝕜)
      (fun n => (hg (n + 1)).trans (hf n).symm)
    exact hgf ▸ hg 0
  · intro g hg
    exact eq_of_normingSequence_eq (𝕜 := 𝕜)
      (fun n => (hg (normingSequence (𝕜 := 𝕜) (E := F) n)).trans (hf n).symm)

omit [CompleteSpace F] in
theorem scalar_representative_norm_le [SeparableSpace F] [CompleteSpace X]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K : X →L[𝕜] InjectiveTensor 𝕜 F X) (f : F)
    (hf : ∀ φ : F →L[𝕜] 𝕜, φ f = scalarCoefficient hX hfew (sliceOperator K φ)) :
    ‖f‖ ≤ ‖K‖ := by
  apply norm_le_of_normingSequence_le (𝕜 := 𝕜)
  intro n
  rw [hf]
  calc
    ‖scalarCoefficient hX hfew (sliceOperator K (normingSequence n))‖ ≤
        ‖sliceOperator K (normingSequence n)‖ := scalarCoefficient_norm_le hX hfew _
    _ ≤ ‖leftSlice (X := X) (normingSequence n)‖ * ‖K‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖normingSequence (𝕜 := 𝕜) (E := F) n‖ * ‖K‖ :=
      mul_le_mul_of_nonneg_right (norm_leftSlice_le _) (norm_nonneg K)
    _ ≤ 1 * ‖K‖ := mul_le_mul_of_nonneg_right (norm_normingSequence_le n) (norm_nonneg K)
    _ = ‖K‖ := one_mul _

variable [SeparableSpace F]

def scalarExtraction (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K : X →L[𝕜] InjectiveTensor 𝕜 F X) : F :=
  Classical.choose (exists_unique_scalar_representative hX hfew K).exists

theorem scalarExtraction_spec (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K : X →L[𝕜] InjectiveTensor 𝕜 F X) (φ : F →L[𝕜] 𝕜) :
    φ (scalarExtraction hX hfew K) = scalarCoefficient hX hfew (sliceOperator K φ) :=
  Classical.choose_spec (exists_unique_scalar_representative hX hfew K).exists φ

theorem scalarExtraction_add (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K L : X →L[𝕜] InjectiveTensor 𝕜 F X) :
    scalarExtraction hX hfew (K + L) = scalarExtraction hX hfew K + scalarExtraction hX hfew L := by
  apply NormedSpace.eq_iff_forall_dual_eq (𝕜 := 𝕜) |>.mpr
  intro φ
  simp only [map_add, scalarExtraction_spec, sliceOperator, ContinuousLinearMap.comp_add,
    scalarCoefficient_add]

theorem scalarExtraction_smul (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (a : 𝕜) (K : X →L[𝕜] InjectiveTensor 𝕜 F X) :
    scalarExtraction hX hfew (a • K) = a • scalarExtraction hX hfew K := by
  apply NormedSpace.eq_iff_forall_dual_eq (𝕜 := 𝕜) |>.mpr
  intro φ
  simp only [map_smul, scalarExtraction_spec, sliceOperator, ContinuousLinearMap.comp_smul,
    scalarCoefficient_smul, smul_eq_mul]

theorem norm_scalarExtraction_le [CompleteSpace X]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X)
    (K : X →L[𝕜] InjectiveTensor 𝕜 F X) : ‖scalarExtraction hX hfew K‖ ≤ ‖K‖ :=
  scalar_representative_norm_le hX hfew K _ (scalarExtraction_spec hX hfew K)

def scalarExtractionLinear (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) : (X →L[𝕜] InjectiveTensor 𝕜 F X) →ₗ[𝕜] F where
  toFun := scalarExtraction (F := F) hX hfew
  map_add' := by intro K L; exact scalarExtraction_add (F := F) hX hfew K L
  map_smul' := by intro a K; exact scalarExtraction_smul (F := F) hX hfew a K

def scalarExtractionL [CompleteSpace X] (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) : (X →L[𝕜] InjectiveTensor 𝕜 F X) →L[𝕜] F :=
  LinearMap.mkContinuous (E := X →L[𝕜] InjectiveTensor 𝕜 F X) (F := F)
    (scalarExtractionLinear (F := F) hX hfew)
    1 (fun K => by simpa only [one_mul] using norm_scalarExtraction_le (F := F) hX hfew K)

@[simp] theorem scalarExtractionL_apply [CompleteSpace X] (hX : ¬ SeparableSpace X)
    (hfew : HasFewOperators 𝕜 X) (K : X →L[𝕜] InjectiveTensor 𝕜 F X) :
    scalarExtractionL (F := F) hX hfew K = scalarExtraction hX hfew K := rfl

theorem norm_scalarExtractionL_le [CompleteSpace X]
    (hX : ¬ SeparableSpace X) (hfew : HasFewOperators 𝕜 X) :
    ‖scalarExtractionL (F := F) hX hfew‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end JFA
