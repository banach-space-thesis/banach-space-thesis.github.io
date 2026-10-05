import Posets.WolfeNorming
import JLMS.CZeroTools

/-! Local compression estimates on an actual compact clopen band. The
insertion is merely supported and cell-constant; no preservation is assumed.
Only fixed continuous-function inequalities, not moving-cell masses, are
extended from the selected leaves to their closure. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]

local instance ordinalBandEstimatesDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalBandEstimatesDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

def ordinalBandRead (q : C(L, K)) : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.toContinuousMap.comp q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => (ContinuousMap.norm_le _ (by simpa using norm_nonneg f)).mpr
      (fun x => by simpa using JLMS.norm_CZero_apply_le f (q x)))

@[simp] theorem ordinalBandRead_apply (q : C(L, K)) (f : JLMS.CZero 𝕜 K) (x : L) :
    ordinalBandRead q f x = f (q x) := rfl

theorem ordinalBandRead_norm_le (q : C(L, K)) : ‖ordinalBandRead (𝕜 := 𝕜) q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  apply (ContinuousMap.norm_le _ (by simpa using norm_nonneg f)).mpr
  intro x
  simpa using JLMS.norm_CZero_apply_le f (q x)

def ordinalBandTotal (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (q : C(L, K)) (H : Set K) (hH : IsClopen H) (hcH : IsCompact H) : C(L, 𝕜) :=
  ordinalBandRead q (T (JLMS.clopenIndicator H hH hcH))

def ordinalBandCompression (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K)) : C(L, 𝕜) →L[𝕜] C(L, 𝕜) :=
  (ordinalBandRead q).comp (T.comp J)

theorem ordinalBand_atomic_apply_of_support (M : JLMS.AtomicDualModel 𝕜 K)
    (φ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜) (g : JLMS.CZero 𝕜 K)
    {U : Set K} (hg : Function.support g ⊆ U) :
    JLMS.atomicRestriction M U φ g = φ g := by
  have h := JLMS.atomicDual_apply_hasSum M φ g
  have hr := JLMS.atomicDual_apply_hasSum M (JLMS.atomicRestriction M U φ) g
  apply hr.unique
  apply h.congr_fun
  intro y
  rw [JLMS.atomicRestriction_coordinates]
  by_cases hy : y ∈ U
  · simp [hy]
  · have hgy : g y = 0 := by by_contra hn; exact hy (hg hn)
    simp [hy, hgy]

theorem ordinalBand_pointwise_error (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K))
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (hJ : ‖J‖ ≤ 1) (hsupp : ∀ f, Function.support (J f) ⊆ H)
    (x : L) (V : Set K) (hVH : V ⊆ H)
    (hconst : ∀ f : C(L, 𝕜), ∀ y ∈ V, J f y = f x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ‖JLMS.atomicRestriction M (H \ V) ((JLMS.evaluation (q x)).comp T)‖ ≤ ε)
    (f : C(L, 𝕜)) :
    ‖T (J f) (q x) - ordinalBandTotal T q H hH hcH x * f x‖ ≤ 2 * ε * ‖f‖ := by
  classical
  let b := JLMS.clopenIndicator (𝕜 := 𝕜) H hH hcH
  let g := J f - f x • b
  have hg : Function.support g ⊆ H \ V := by
    intro y hy
    have hHmem : y ∈ H := by
      by_contra hn
      have hJzero : J f y = 0 := by by_contra hz; exact hn (hsupp f hz)
      apply hy
      simp [g, b, hJzero, hn]
    refine ⟨hHmem, ?_⟩
    intro hVmem
    apply hy
    simp [g, b, hconst f y hVmem, hVH hVmem]
  have hgn : ‖g‖ ≤ 2 * ‖f‖ := by
    have hJn : ‖J f‖ ≤ ‖f‖ := (J.le_opNorm f).trans (by
      simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg f))
    have hbn : ‖f x • b‖ ≤ ‖f‖ := by
      rw [norm_smul]
      exact (mul_le_mul (f.norm_coe_le_norm x) (JLMS.norm_clopenIndicator_le H hH hcH)
        (norm_nonneg _) (norm_nonneg f)).trans_eq (mul_one _)
    exact (norm_sub_le _ _).trans (by linarith)
  let φ := (JLMS.evaluation (q x)).comp T
  have he : φ g = T (J f) (q x) - ordinalBandTotal T q H hH hcH x * f x := by
    simp only [φ, g, b, ContinuousLinearMap.comp_apply, map_sub, map_smul,
      JLMS.evaluation_apply, ZeroAtInftyContinuousMap.sub_apply,
      ZeroAtInftyContinuousMap.smul_apply, ordinalBandTotal, ordinalBandRead_apply,
      smul_eq_mul, mul_comm]
  rw [← he, ← ordinalBand_atomic_apply_of_support M φ g hg]
  calc
    _ ≤ ‖JLMS.atomicRestriction M (H \ V) φ‖ * ‖g‖ :=
      (JLMS.atomicRestriction M (H \ V) φ).le_opNorm g
    _ ≤ ε * (2 * ‖f‖) := mul_le_mul hmass hgn (norm_nonneg _) hε
    _ = 2 * ε * ‖f‖ := by ring

theorem ordinalBand_error_of_dense_leaves
    (A : C(L, 𝕜) →L[𝕜] C(L, 𝕜)) (a : C(L, 𝕜))
    {S : Set L} (hS : Dense S) {r : ℝ} (hr : 0 ≤ r)
    (hleaf : ∀ f : C(L, 𝕜), ∀ x ∈ S, ‖A f x - a x * f x‖ ≤ r * ‖f‖) :
    ‖A - ContinuousLinearMap.mul 𝕜 C(L, 𝕜) a‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hr (norm_nonneg f))).mpr
  intro x
  change ‖A f x - a x * f x‖ ≤ r * ‖f‖
  have hc : IsClosed {x : L | ‖A f x - a x * f x‖ ≤ r * ‖f‖} :=
    isClosed_le ((A f).continuous.sub (a.continuous.mul f.continuous)).norm continuous_const
  exact (closure_minimal (hleaf f) hc) (hS.closure_eq.symm ▸ Set.mem_univ x)

theorem ordinalBand_lower_of_dense_leaves (a : C(L, 𝕜))
    {S : Set L} (hS : Dense S) {γ : ℝ} (hleaf : ∀ x ∈ S, γ ≤ ‖a x‖) :
    ∀ x, γ ≤ ‖a x‖ := by
  intro x
  have hc : IsClosed {x : L | γ ≤ ‖a x‖} := isClosed_le continuous_const a.continuous.norm
  exact (closure_minimal hleaf hc) (hS.closure_eq.symm ▸ Set.mem_univ x)

end Posets
