import BanachIsometric.FiniteTensorComparison
import BanachIsometric.RawTensorBoundarySquared

/-! Actual signed total boundary on finite ordered-face tensor chains.
Its comparison with the actual raw tensor boundary is proved, and genuine
square-zero follows by the already proved degreewise linear injection.
No homology injectivity is inferred. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularPrism SingularAW
open scoped TensorProduct DirectSum

variable {ι : Type} [LinearOrder ι] [Fintype ι]

def finiteTensorLeftComponent (K : Complex ι) : (p q : ℕ) →
    FiniteTensorChains K p q →ₗ[ℚ] FiniteBigradedTensorChains K
  | 0, _ => 0
  | p + 1, q => (finiteTensorInclusion K p q).comp
      (TensorProduct.map (finiteRationalBoundary K p) LinearMap.id)

def finiteTensorRightComponent (K : Complex ι) : (p q : ℕ) →
    FiniteTensorChains K p q →ₗ[ℚ] FiniteBigradedTensorChains K
  | _, 0 => 0
  | p, q + 1 => (-1 : ℚ) ^ p • (finiteTensorInclusion K p q).comp
      (TensorProduct.map LinearMap.id (finiteRationalBoundary K q))

def finiteTensorLeftBoundary (K : Complex ι) :
    FiniteBigradedTensorChains K →ₗ[ℚ] FiniteBigradedTensorChains K :=
  DirectSum.toModule ℚ (ℕ × ℕ) (FiniteBigradedTensorChains K)
    (fun ij => finiteTensorLeftComponent K ij.1 ij.2)

def finiteTensorRightBoundary (K : Complex ι) :
    FiniteBigradedTensorChains K →ₗ[ℚ] FiniteBigradedTensorChains K :=
  DirectSum.toModule ℚ (ℕ × ℕ) (FiniteBigradedTensorChains K)
    (fun ij => finiteTensorRightComponent K ij.1 ij.2)

def finiteTensorTotalBoundary (K : Complex ι) :
    FiniteBigradedTensorChains K →ₗ[ℚ] FiniteBigradedTensorChains K :=
  finiteTensorLeftBoundary K + finiteTensorRightBoundary K

theorem finiteTensorToRaw_leftComponent (K : Complex ι) (p q : ℕ) :
    (finiteTensorToRaw K).comp (finiteTensorLeftComponent K p q) =
      (rawTensorLeftComponent K.space K.space p q).comp
        (TensorProduct.map (finiteToRawSingularChain K p) (finiteToRawSingularChain K q)) := by
  cases p with
  | zero => simp only [finiteTensorLeftComponent, rawTensorLeftComponent,
      LinearMap.comp_zero, LinearMap.zero_comp]
  | succ p =>
    apply TensorProduct.ext
    ext a b
    simp only [finiteTensorLeftComponent, rawTensorLeftComponent, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, finiteTensorToRaw_inclusion]
    have h := LinearMap.congr_fun (finiteToRawSingularChain_boundary K p) a
    change rawBoundary p (finiteToRawSingularChain K (p + 1) a) =
      finiteToRawSingularChain K p (finiteRationalBoundary K p a) at h
    rw [h]

theorem finiteTensorToRaw_rightComponent (K : Complex ι) (p q : ℕ) :
    (finiteTensorToRaw K).comp (finiteTensorRightComponent K p q) =
      (rawTensorRightComponent K.space K.space p q).comp
        (TensorProduct.map (finiteToRawSingularChain K p) (finiteToRawSingularChain K q)) := by
  cases q with
  | zero => simp only [finiteTensorRightComponent, rawTensorRightComponent,
      LinearMap.comp_zero, LinearMap.zero_comp]
  | succ q =>
    apply TensorProduct.ext
    ext a b
    simp only [finiteTensorRightComponent, rawTensorRightComponent, LinearMap.comp_apply,
      LinearMap.smul_apply, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
      finiteTensorToRaw_inclusion]
    have h := LinearMap.congr_fun (finiteToRawSingularChain_boundary K q) b
    change rawBoundary q (finiteToRawSingularChain K (q + 1) b) =
      finiteToRawSingularChain K q (finiteRationalBoundary K q b) at h
    rw [h]

theorem finiteTensorToRaw_boundary (K : Complex ι) :
    (finiteTensorToRaw K).comp (finiteTensorTotalBoundary K) =
      (rawTensorTotalBoundary K.space K.space).comp (finiteTensorToRaw K) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply LinearMap.ext
  intro c
  change finiteTensorToRaw K (finiteTensorTotalBoundary K (finiteTensorInclusion K p q c)) = _
  simp only [finiteTensorTotalBoundary, LinearMap.add_apply, finiteTensorLeftBoundary,
    finiteTensorRightBoundary, finiteTensorInclusion, DirectSum.toModule_lof, map_add]
  rw [← LinearMap.comp_apply (finiteTensorToRaw K) (finiteTensorLeftComponent K p q),
    ← LinearMap.comp_apply (finiteTensorToRaw K) (finiteTensorRightComponent K p q),
    finiteTensorToRaw_leftComponent, finiteTensorToRaw_rightComponent]
  change _ = rawTensorTotalBoundary K.space K.space
    (finiteTensorToRaw K (finiteTensorInclusion K p q c))
  rw [finiteTensorToRaw_inclusion, rawTensorTotalBoundary, LinearMap.add_apply,
    rawTensorLeftBoundary_inclusion, rawTensorRightBoundary_inclusion]
  rfl

theorem finiteTensorTotalBoundary_squared (K : Complex ι) :
    (finiteTensorTotalBoundary K).comp (finiteTensorTotalBoundary K) = 0 := by
  apply LinearMap.ext
  intro c
  apply finiteTensorToRaw_injective K
  rw [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
  have h := LinearMap.congr_fun (finiteTensorToRaw_boundary K)
  change ∀ x, finiteTensorToRaw K (finiteTensorTotalBoundary K x) =
    rawTensorTotalBoundary K.space K.space (finiteTensorToRaw K x) at h
  rw [h, h]
  exact LinearMap.congr_fun (rawTensorTotalBoundary_squared K.space K.space) _

end BanachIsometric.FiniteNerve
