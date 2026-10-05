import JFA.CZeroTopology
import JFA.TensorFunction

/-! The pointwise isometric embedding C₀(A) ⊗̂ε X → C₀(A,X), on the actual
C₀ spaces. Point evaluations give a bounded continuous function, and density
of finite tensors proves that it vanishes at infinity. Dual contractions give
the reverse norm inequality. Surjectivity is treated separately. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Filter Set
open scoped ZeroAtInfty TensorProduct BoundedContinuousFunction
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [TopologicalSpace A]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

omit [NormedSpace 𝕜 X] [CompleteSpace X] in
@[simp] theorem czero_sum_apply {ι : Type*} (s : Finset ι) (f : ι → C₀(A, X)) (a : A) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [Finset.sum_insert hi, ZeroAtInftyContinuousMap.add_apply, hs]

omit [NormedSpace 𝕜 X] [CompleteSpace X] in
theorem czero_vector_compact_tail (f : C₀(A, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set A, IsCompact K ∧ ∀ a ∉ K, ‖f a‖ < ε := by
  obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp
    (Metric.tendsto_nhds.mp (zero_at_infty f) ε hε)
  exact ⟨K, hK, fun a ha => by simpa only [dist_zero_right] using hbound ha⟩

def czeroPureFunction (f : C₀(A, 𝕜)) (x : X) : C₀(A, X) where
  toFun := fun a => f a • x
  continuous_toFun := f.continuous.smul continuous_const
  zero_at_infty' := by
    simpa only [zero_smul] using (zero_at_infty f).smul
      (tendsto_const_nhds : Tendsto (fun _ : A => x) (cocompact A) (𝓝 x))

omit [CompleteSpace X] in
@[simp] theorem czeroPureFunction_apply (f : C₀(A, 𝕜)) (x : X) (a : A) :
    czeroPureFunction f x a = f a • x := rfl

def czeroEvaluationPullback : C(DualBall 𝕜 C₀(A, 𝕜), X) →L[𝕜] (A →ᵇ X) :=
  LinearMap.mkContinuous {
    toFun := fun f => (BoundedContinuousFunction.mkOfCompact f).compContinuous
      ⟨czeroDualEvaluation, continuous_czeroDualEvaluation⟩
    map_add' := by intro f g; ext a; rfl
    map_smul' := by intro c f; ext a; rfl }
    1 (fun f => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun a =>
        f.norm_coe_le_norm (czeroDualEvaluation (𝕜 := 𝕜) a))

def tensorBoundedCzero : InjectiveTensor 𝕜 C₀(A, 𝕜) X →L[𝕜] (A →ᵇ X) :=
  czeroEvaluationPullback.comp tensorFunction

theorem tensorBoundedCzero_apply (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) (a : A) :
    tensorBoundedCzero z a = leftSlice (czeroEvaluation (𝕜 := 𝕜) a) z :=
  tensorFunction_apply z (czeroDualEvaluation a)

@[simp] theorem tensorBoundedCzero_pure (f : C₀(A, 𝕜)) (x : X) (a : A) :
    tensorBoundedCzero (injectivePure 𝕜 C₀(A, 𝕜) X f x) a = f a • x := by
  rw [tensorBoundedCzero_apply, leftSlice_pure]
  rfl

theorem norm_tensorBoundedCzero_le (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) :
    ‖tensorBoundedCzero z‖ ≤ ‖z‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg z)).mpr
  intro a
  change ‖tensorFunction z (czeroDualEvaluation a)‖ ≤ ‖z‖
  exact ((tensorFunction z).norm_coe_le_norm _).trans (norm_tensorFunction_le z)

theorem tensorBoundedCzero_mem_czero_range (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) :
    tensorBoundedCzero z ∈ range (ZeroAtInftyContinuousMap.toBCF : C₀(A, X) → A →ᵇ X) := by
  refine injectiveInclusion_dense.induction_on z
    (ZeroAtInftyContinuousMap.isClosed_range_toBCF.preimage tensorBoundedCzero.continuous) ?_
  intro w
  induction w using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, ?_⟩
    ext a
    simp
  | tmul f x =>
    refine ⟨czeroPureFunction f x, ?_⟩
    ext a
    exact (tensorBoundedCzero_pure f x a).symm
  | add w v hw hv =>
    obtain ⟨f, hf⟩ := hw
    obtain ⟨g, hg⟩ := hv
    refine ⟨f + g, ?_⟩
    rw [map_add, map_add, ← hf, ← hg]
    rfl

def tensorCzeroValue (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) : C₀(A, X) :=
  Classical.choose (tensorBoundedCzero_mem_czero_range z)

theorem tensorCzeroValue_toBCF (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) :
    (tensorCzeroValue z).toBCF = tensorBoundedCzero z :=
  Classical.choose_spec (tensorBoundedCzero_mem_czero_range z)

theorem tensorCzeroValue_apply (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) (a : A) :
    tensorCzeroValue z a = tensorBoundedCzero z a :=
  congrArg (fun f : A →ᵇ X => f a) (tensorCzeroValue_toBCF z)

def tensorCzeroFunction : InjectiveTensor 𝕜 C₀(A, 𝕜) X →L[𝕜] C₀(A, X) :=
  LinearMap.mkContinuous {
    toFun := tensorCzeroValue
    map_add' := by
      intro z w
      ext a
      simp only [tensorCzeroValue_apply, map_add, BoundedContinuousFunction.add_apply,
        ZeroAtInftyContinuousMap.add_apply]
    map_smul' := by
      intro c z
      ext a
      simp only [tensorCzeroValue_apply, map_smul, BoundedContinuousFunction.smul_apply,
        ZeroAtInftyContinuousMap.smul_apply, RingHom.id_apply] }
    1 (fun z => by
      change ‖tensorCzeroValue z‖ ≤ 1 * ‖z‖
      rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, tensorCzeroValue_toBCF]
      exact norm_tensorBoundedCzero_le z)

theorem tensorCzeroFunction_apply (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) (a : A) :
    tensorCzeroFunction z a = leftSlice (czeroEvaluation (𝕜 := 𝕜) a) z :=
  (tensorCzeroValue_apply z a).trans (tensorBoundedCzero_apply z a)

@[simp] theorem tensorCzeroFunction_pure (f : C₀(A, 𝕜)) (x : X) (a : A) :
    tensorCzeroFunction (injectivePure 𝕜 C₀(A, 𝕜) X f x) a = f a • x := by
  rw [tensorCzeroFunction_apply, leftSlice_pure]
  rfl

theorem norm_rightSlice_czero_le (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X)
    (ψ : X →L[𝕜] 𝕜) : ‖rightSlice ψ z‖ ≤ ‖ψ‖ * ‖tensorCzeroFunction z‖ := by
  change ‖(rightSlice ψ z).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro a
  change ‖rightSlice ψ z a‖ ≤ _
  have hpair := rightSlice_pairing ψ (czeroEvaluation (𝕜 := 𝕜) a) z
  change rightSlice ψ z a = ψ (leftSlice (czeroEvaluation (𝕜 := 𝕜) a) z) at hpair
  rw [hpair, ← tensorCzeroFunction_apply]
  exact (ψ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((tensorCzeroFunction z).toBCF.norm_coe_le_norm a) (norm_nonneg ψ))

theorem norm_tensorCzeroFunction (z : InjectiveTensor 𝕜 C₀(A, 𝕜) X) :
    ‖tensorCzeroFunction z‖ = ‖z‖ := by
  apply le_antisymm
  · change ‖tensorCzeroValue z‖ ≤ ‖z‖
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, tensorCzeroValue_toBCF]
    exact norm_tensorBoundedCzero_le z
  · change ‖z.val‖ ≤ ‖tensorCzeroFunction z‖
    apply (dualOperator_norm_le_iff z.val _ (norm_nonneg _)).mpr
    intro φ ψ
    have hpair := rightSlice_pairing ψ φ z
    change φ (rightSlice ψ z) = ψ (z.val φ) at hpair
    rw [← hpair]
    calc
      ‖φ (rightSlice ψ z)‖ ≤ ‖φ‖ * ‖rightSlice ψ z‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (‖ψ‖ * ‖tensorCzeroFunction z‖) :=
        mul_le_mul_of_nonneg_left (norm_rightSlice_czero_le z ψ) (norm_nonneg φ)
      _ = (‖tensorCzeroFunction z‖ * ‖φ‖) * ‖ψ‖ := by ring

def tensorCzeroIsometry : InjectiveTensor 𝕜 C₀(A, 𝕜) X →ₗᵢ[𝕜] C₀(A, X) where
  toLinearMap := tensorCzeroFunction.toLinearMap
  norm_map' := norm_tensorCzeroFunction

end JFA
