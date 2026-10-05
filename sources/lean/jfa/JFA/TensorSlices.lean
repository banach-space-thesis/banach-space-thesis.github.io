import JFA.TensorNormChecks
import Mathlib.Topology.DenseEmbedding

/-! Bounded insertion and left slice maps, and extensionality on elementary
tensors. These are the maps used to extract scalar-plus-separable coordinates. -/

noncomputable section
open scoped TensorProduct
namespace JFA
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def leftSlice (φ : E →L[𝕜] 𝕜) : InjectiveTensor 𝕜 E X →L[𝕜] X :=
  (ContinuousLinearMap.apply 𝕜 X φ).comp (InjectiveTensor 𝕜 E X).subtypeL

@[simp] theorem leftSlice_pure (φ : E →L[𝕜] 𝕜) (e : E) (x : X) :
    leftSlice φ (injectivePure 𝕜 E X e x) = φ e • x := rfl

theorem norm_leftSlice_le (φ : E →L[𝕜] 𝕜) : ‖leftSlice (X := X) φ‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro z
  change ‖z.val φ‖ ≤ ‖φ‖ * ‖z‖
  simpa [mul_comm] using z.val.le_opNorm φ

def injectivePureMap (e : E) : X →L[𝕜] InjectiveTensor 𝕜 E X :=
  LinearMap.mkContinuous
    ((injectiveInclusion 𝕜 E X).comp (TensorProduct.mk 𝕜 E X e)) ‖e‖
    (fun x => (norm_injectivePure e x).le)

@[simp] theorem injectivePureMap_apply (e : E) (x : X) :
    injectivePureMap e x = injectivePure 𝕜 E X e x := rfl

theorem norm_injectivePureMap_le (e : E) :
    ‖injectivePureMap (𝕜 := 𝕜) (X := X) e‖ ≤ ‖e‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg e) _

def injectiveLeftPureMap (x : X) : E →L[𝕜] InjectiveTensor 𝕜 E X :=
  LinearMap.mkContinuous
    ((injectiveInclusion 𝕜 E X).comp ((TensorProduct.mk 𝕜 E X).flip x)) ‖x‖
    (fun e => by simpa only [mul_comm] using (norm_injectivePure e x).le)

@[simp] theorem injectiveLeftPureMap_apply (e : E) (x : X) :
    injectiveLeftPureMap x e = injectivePure 𝕜 E X e x := rfl

@[simp] theorem injectivePureMap_add (e f : E) :
    injectivePureMap (𝕜 := 𝕜) (X := X) (e + f) = injectivePureMap e + injectivePureMap f := by
  apply ContinuousLinearMap.ext
  intro x
  change injectiveInclusion 𝕜 E X ((e + f) ⊗ₜ[𝕜] x) =
    injectiveInclusion 𝕜 E X (e ⊗ₜ[𝕜] x) + injectiveInclusion 𝕜 E X (f ⊗ₜ[𝕜] x)
  rw [TensorProduct.add_tmul, map_add]

@[simp] theorem injectivePureMap_smul (a : 𝕜) (e : E) :
    injectivePureMap (𝕜 := 𝕜) (X := X) (a • e) = a • injectivePureMap e := by
  apply ContinuousLinearMap.ext
  intro x
  change injectiveInclusion 𝕜 E X (a • (e ⊗ₜ[𝕜] x)) = a • injectiveInclusion 𝕜 E X (e ⊗ₜ[𝕜] x)
  exact map_smul _ _ _

/-- The algebraic tensor image is dense in its concrete epsilon completion. -/
theorem injectiveInclusion_dense : DenseRange (injectiveInclusion 𝕜 E X) := by
  rw [DenseRange, Subtype.dense_iff]
  have himage : Subtype.val '' Set.range (injectiveInclusion 𝕜 E X) =
      Set.range (tensorPairing 𝕜 E X) := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨injectiveInclusion 𝕜 E X w, ⟨w, rfl⟩, rfl⟩
  change closure (Set.range (tensorPairing 𝕜 E X)) ⊆ _
  exact (congrArg closure himage).symm.le

section Completion
variable {𝕜' : Type u} [RCLike 𝕜']
variable {E' X' A B : Type u}
  [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
  [NormedAddCommGroup X'] [NormedSpace 𝕜' X']
  [NormedAddCommGroup A] [NormedSpace 𝕜' A]
  [NormedAddCommGroup B] [NormedSpace 𝕜' B]

def completionPureMap (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (e : E') : X' →L[𝕜'] A :=
  LinearMap.mkContinuous (ι.comp (TensorProduct.mk 𝕜' E' X' e)) ‖e‖
    (fun x => by
      change ‖ι (e ⊗ₜ[𝕜'] x)‖ ≤ _
      rw [hι.2.2]
      exact p.pure_le e x)

@[simp] theorem completionPureMap_apply (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (e : E') (x : X') : completionPureMap p ι hι e x = ι (e ⊗ₜ[𝕜'] x) := rfl

theorem norm_completionPureMap_le (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (e : E') : ‖completionPureMap p ι hι e‖ ≤ ‖e‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg e) _

@[simp] theorem completionPureMap_add (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (e f : E') : completionPureMap p ι hι (e + f) =
      completionPureMap p ι hι e + completionPureMap p ι hι f := by
  ext x
  simp only [ContinuousLinearMap.add_apply, completionPureMap_apply,
    TensorProduct.add_tmul, map_add]

@[simp] theorem completionPureMap_smul (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (a : 𝕜') (e : E') : completionPureMap p ι hι (a • e) =
      a • completionPureMap p ι hι e := by
  ext x
  change ι (a • (e ⊗ₜ[𝕜'] x)) = a • ι (e ⊗ₜ[𝕜'] x)
  exact ι.map_smul a _

def completionLeftPureMap (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (x : X') : E' →L[𝕜'] A :=
  LinearMap.mkContinuous (ι.comp ((TensorProduct.mk 𝕜' E' X').flip x)) ‖x‖
    (fun e => by
      change ‖ι (e ⊗ₜ[𝕜'] x)‖ ≤ _
      rw [hι.2.2]
      simpa only [mul_comm] using p.pure_le e x)

@[simp] theorem completionLeftPureMap_apply (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (e : E') (x : X') : completionLeftPureMap p ι hι x e = ι (e ⊗ₜ[𝕜'] x) := rfl

theorem norm_completionLeftPureMap_le (p : ReasonableCrossnorm 𝕜' E' X')
    (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hι : IsTensorCompletion 𝕜' E' X' A p ι)
    (x : X') : ‖completionLeftPureMap p ι hι x‖ ≤ ‖x‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg x) _

/-- Equality on elementary tensors determines a bounded map on any completion. -/
theorem completion_ext (ι : E' ⊗[𝕜'] X' →ₗ[𝕜'] A) (hd : DenseRange ι)
    {S T : A →L[𝕜'] B}
    (h : ∀ e x, S (ι (e ⊗ₜ[𝕜'] x)) = T (ι (e ⊗ₜ[𝕜'] x))) : S = T := by
  apply ContinuousLinearMap.coeFn_injective
  apply hd.equalizer S.continuous T.continuous
  funext z
  change S (ι z) = T (ι z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e x => exact h e x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

end Completion
end JFA
