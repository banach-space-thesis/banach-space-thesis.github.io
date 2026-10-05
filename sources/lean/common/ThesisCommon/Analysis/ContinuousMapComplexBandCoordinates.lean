import ThesisCommon.Analysis.ContinuousMapComplexPrincipalBand
import ThesisCommon.Analysis.ALBandCoordinates

/-! Bounded coordinates and synthesis for any disjoint family of actual
complex principal bands in C(K)*. This does not require a total family. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Set
open scoped Classical
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice

section GenericSynthesis
variable {𝕜 E I : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] (s : I → Submodule 𝕜 E)

def submoduleLpOneSynthesis : lp (fun i => s i) 1 →L[𝕜] E :=
  lpOneFamilyOperator (𝕜 := 𝕜) (F := E) (E := fun i => s i)
    (fun i => (s i).subtypeL) 1 zero_le_one (fun i => Submodule.norm_subtypeL_le (s i))

theorem norm_submoduleLpOneSynthesis_le : ‖submoduleLpOneSynthesis s‖ ≤ 1 :=
  norm_lpOneFamilyOperator_le _ _ zero_le_one _

theorem submoduleLpOneSynthesis_single (i : I) (x : s i) :
    submoduleLpOneSynthesis s (lp.single 1 i x) = x :=
  lpOneFamilyOperator_single (𝕜 := 𝕜) (E := fun j => s j) (F := E)
    (fun j => (s j).subtypeL) 1 zero_le_one (fun j => Submodule.norm_subtypeL_le (s j)) i x

end GenericSynthesis

variable {K I : Type*} [TopologicalSpace K] [CompactSpace K]

local instance : NormedAddCommGroup (C(K, ℂ) →L[ℂ] ℂ) := inferInstance
local instance : NormedSpace ℂ (C(K, ℂ) →L[ℂ] ℂ) := inferInstance

theorem continuousMap_dual_ext_coordinates {φ ψ : C(K, ℂ) →L[ℂ] ℂ}
    (hr : continuousMapDualRe φ = continuousMapDualRe ψ)
    (hi : continuousMapDualIm φ = continuousMapDualIm ψ) : φ = ψ := by
  rw [← continuousMapDual_decomposition φ, ← continuousMapDual_decomposition ψ, hr, hi]

def continuousMapComplexBandProjectionReal (e : C(K, ℝ) →L[ℝ] ℝ) :
    (C(K, ℂ) →L[ℂ] ℂ) →L[ℝ] (C(K, ℂ) →L[ℂ] ℂ) :=
  continuousMapDualOfReal.comp ((principalBandProjection e).comp continuousMapDualRe) +
    Complex.I • continuousMapDualOfReal.comp
      ((principalBandProjection e).comp continuousMapDualIm)

theorem continuousMapComplexBandProjectionReal_re (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualRe (continuousMapComplexBandProjectionReal e φ) =
      principalBandProjection e (continuousMapDualRe φ) := by
  simp [continuousMapComplexBandProjectionReal, continuousMapDualRe_smul]

theorem continuousMapComplexBandProjectionReal_im (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualIm (continuousMapComplexBandProjectionReal e φ) =
      principalBandProjection e (continuousMapDualIm φ) := by
  simp [continuousMapComplexBandProjectionReal, continuousMapDualIm_smul]

def continuousMapComplexBandProjection (e : C(K, ℝ) →L[ℝ] ℝ) :
    (C(K, ℂ) →L[ℂ] ℂ) →L[ℂ] (C(K, ℂ) →L[ℂ] ℂ) where
  toFun := continuousMapComplexBandProjectionReal e
  map_add' := map_add (continuousMapComplexBandProjectionReal e)
  map_smul' := by
    intro c φ
    apply continuousMap_dual_ext_coordinates
    · simp only [continuousMapComplexBandProjectionReal_re,
        continuousMapDualRe_smul, map_sub, map_smul, RingHom.id_apply,
        continuousMapComplexBandProjectionReal_im]
    · simp only [continuousMapComplexBandProjectionReal_im,
        continuousMapDualIm_smul, map_add, map_smul, RingHom.id_apply,
        continuousMapComplexBandProjectionReal_re]
  cont := (continuousMapComplexBandProjectionReal e).continuous

theorem continuousMapComplexBandProjection_re (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualRe (continuousMapComplexBandProjection e φ) =
      principalBandProjection e (continuousMapDualRe φ) :=
  continuousMapComplexBandProjectionReal_re e φ

theorem continuousMapComplexBandProjection_im (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapDualIm (continuousMapComplexBandProjection e φ) =
      principalBandProjection e (continuousMapDualIm φ) :=
  continuousMapComplexBandProjectionReal_im e φ

theorem continuousMapComplexBandProjection_mem (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    continuousMapComplexBandProjection e φ ∈ continuousMapComplexPrincipalBand e := by
  constructor
  · rw [continuousMapComplexBandProjection_re]
    exact (principalBand_orderClosed e).bandProjection_mem _
  · rw [continuousMapComplexBandProjection_im]
    exact (principalBand_orderClosed e).bandProjection_mem _

theorem continuousMapComplexBandProjection_norm_le (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : C(K, ℂ) →L[ℂ] ℂ) :
    ‖continuousMapComplexBandProjection e φ‖ ≤
      ‖principalBandProjection e (continuousMapDualRe φ)‖ +
      ‖principalBandProjection e (continuousMapDualIm φ)‖ := by
  change ‖continuousMapDualOfReal (principalBandProjection e (continuousMapDualRe φ)) +
    Complex.I • continuousMapDualOfReal (principalBandProjection e (continuousMapDualIm φ))‖ ≤ _
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul, Complex.norm_I, one_mul, norm_continuousMapDualOfReal,
      norm_continuousMapDualOfReal])

theorem continuousMapComplexBandProjection_self (e : C(K, ℝ) →L[ℝ] ℝ)
    (φ : continuousMapComplexPrincipalBand e) :
    continuousMapComplexBandProjection e φ = φ := by
  apply continuousMap_dual_ext_coordinates
  · rw [continuousMapComplexBandProjection_re]
    exact (principalBand_orderClosed e).bandProjection_eq_self φ.property.1
  · rw [continuousMapComplexBandProjection_im]
    exact (principalBand_orderClosed e).bandProjection_eq_self φ.property.2

theorem continuousMapComplexBandProjection_orthogonal
    {e f : C(K, ℝ) →L[ℝ] ℝ} (h : |e| ⊓ |f| = 0)
    (φ : continuousMapComplexPrincipalBand f) :
    continuousMapComplexBandProjection e φ = 0 := by
  apply continuousMap_dual_ext_coordinates
  · rw [continuousMapComplexBandProjection_re, map_zero]
    apply (principalBandProjection_eq_zero_iff _ _).mpr
    rw [inf_comm]
    exact principalBand_disjoint_of_disjoint h (self_mem_principalBand e) φ.property.1
  · rw [continuousMapComplexBandProjection_im, map_zero]
    apply (principalBandProjection_eq_zero_iff _ _).mpr
    rw [inf_comm]
    exact principalBand_disjoint_of_disjoint h (self_mem_principalBand e) φ.property.2

variable (a : I → (C(K, ℝ) →L[ℝ] ℝ))
  (hd : Pairwise (fun i j => |a i| ⊓ |a j| = 0))

include hd in
theorem continuousMapComplexBandProjection_finite_norm_le
    (s : Finset I) (φ : C(K, ℂ) →L[ℂ] ℂ) :
    ∑ i ∈ s, ‖continuousMapComplexBandProjection (a i) φ‖ ≤ 2 * ‖φ‖ := by
  calc
    _ ≤ ∑ i ∈ s, (‖principalBandProjection (a i) (continuousMapDualRe φ)‖ +
      ‖principalBandProjection (a i) (continuousMapDualIm φ)‖) :=
      Finset.sum_le_sum (fun i _ => continuousMapComplexBandProjection_norm_le (a i) φ)
    _ = (∑ i ∈ s, ‖principalBandProjection (a i) (continuousMapDualRe φ)‖) +
      ∑ i ∈ s, ‖principalBandProjection (a i) (continuousMapDualIm φ)‖ := Finset.sum_add_distrib
    _ ≤ ‖continuousMapDualRe φ‖ + ‖continuousMapDualIm φ‖ := add_le_add
      (alBandProjection_finite_sum_norm_le continuousMapDual_norm_add_of_nonneg a hd s _)
      (alBandProjection_finite_sum_norm_le continuousMapDual_norm_add_of_nonneg a hd s _)
    _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (norm_continuousMapFunctionalRe_le φ)
      (norm_continuousMapFunctionalIm_le φ)
    _ = 2 * ‖φ‖ := (two_mul _).symm

def continuousMapComplexBandCoefficients (φ : C(K, ℂ) →L[ℂ] ℂ) :
    lp (fun i => continuousMapComplexPrincipalBand (a i)) 1 :=
  ⟨fun i => ⟨continuousMapComplexBandProjection (a i) φ,
    continuousMapComplexBandProjection_mem (a i) φ⟩, memℓp_gen (by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        summable_of_sum_le (fun i => norm_nonneg (continuousMapComplexBandProjection (a i) φ))
          (fun s => continuousMapComplexBandProjection_finite_norm_le a hd s φ))⟩

theorem continuousMapComplexBandCoefficients_norm_le (φ : C(K, ℂ) →L[ℂ] ℂ) :
    ‖continuousMapComplexBandCoefficients a hd φ‖ ≤ 2 * ‖φ‖ := by
  rw [← (lpOneFamily_hasSum_norm (continuousMapComplexBandCoefficients a hd φ)).tsum_eq]
  exact (lpOneFamily_hasSum_norm (continuousMapComplexBandCoefficients a hd φ)).summable.tsum_le_of_sum_le
    (fun s => continuousMapComplexBandProjection_finite_norm_le a hd s φ)

def continuousMapComplexBandCoordinates :
    (C(K, ℂ) →L[ℂ] ℂ) →L[ℂ] lp (fun i => continuousMapComplexPrincipalBand (a i)) 1 :=
  LinearMap.mkContinuous
    { toFun := continuousMapComplexBandCoefficients a hd
      map_add' := by
        intro φ ψ
        apply lp.ext
        funext i
        exact Subtype.ext (map_add (continuousMapComplexBandProjection (a i)) φ ψ)
      map_smul' := by
        intro c φ
        apply lp.ext
        funext i
        exact Subtype.ext (map_smul (continuousMapComplexBandProjection (a i)) c φ) }
    2 (continuousMapComplexBandCoefficients_norm_le a hd)

theorem norm_continuousMapComplexBandCoordinates_le :
    ‖continuousMapComplexBandCoordinates a hd‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem continuousMapComplexBandCoordinates_apply (φ : C(K, ℂ) →L[ℂ] ℂ) (i : I) :
    (continuousMapComplexBandCoordinates a hd φ i : C(K, ℂ) →L[ℂ] ℂ) =
      continuousMapComplexBandProjection (a i) φ := rfl

def continuousMapComplexBandSynthesis :
    lp (fun i => continuousMapComplexPrincipalBand (a i)) 1 →L[ℂ] (C(K, ℂ) →L[ℂ] ℂ) :=
  submoduleLpOneSynthesis (𝕜 := ℂ) (E := C(K, ℂ) →L[ℂ] ℂ)
    (fun i => continuousMapComplexPrincipalBand (a i))

theorem norm_continuousMapComplexBandSynthesis_le :
    ‖continuousMapComplexBandSynthesis a‖ ≤ 1 :=
  norm_submoduleLpOneSynthesis_le (fun i => continuousMapComplexPrincipalBand (a i))

theorem continuousMapComplexBandCoordinates_comp_synthesis :
    (continuousMapComplexBandCoordinates a hd).comp (continuousMapComplexBandSynthesis a) =
      ContinuousLinearMap.id ℂ _ := by
  apply lp.ext_continuousLinearMap (by norm_num : (1 : ENNReal) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro φ
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    ContinuousLinearMap.id_apply]
  change continuousMapComplexBandCoordinates a hd
    (submoduleLpOneSynthesis (fun j => continuousMapComplexPrincipalBand (a j))
      (lp.single 1 i φ)) = lp.single 1 i φ
  rw [submoduleLpOneSynthesis_single]
  apply lp.ext
  funext j
  apply Subtype.ext
  rw [continuousMapComplexBandCoordinates_apply]
  by_cases h : j = i
  · subst j
    rw [lp.single_apply_self]
    exact continuousMapComplexBandProjection_self (a i) φ
  · rw [lp.single_apply_ne (E := fun k => continuousMapComplexPrincipalBand (a k)) 1 i φ h]
    exact continuousMapComplexBandProjection_orthogonal (hd h) φ

end ThesisCommon
