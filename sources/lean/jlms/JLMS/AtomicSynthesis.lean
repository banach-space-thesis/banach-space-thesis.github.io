import JLMS.AtomicDual
import JLMS.PhaseFunctions
import JLMS.ScatteredTopology

/-!
# Isometric synthesis of ℓ¹ point masses

An absolutely summable combination of point evaluations defines a bounded
functional. Compact clopen phase functions show that synthesis preserves
the norm on a scattered locally compact Hausdorff space. Surjectivity is
the separate Riesz representation argument.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

local instance atomicSynthesisDualGroup : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance atomicSynthesisDualSpace : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem summable_atomic_values (a : ellOneOn 𝕜 K) (f : CZero 𝕜 K) :
    Summable (fun x : K => a x * f x) :=
  ((ellOneOn_summable_norm a).mul_right ‖f‖).of_norm_bounded
    (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_CZero_apply_le f x) (norm_nonneg _))

theorem norm_atomic_values_tsum_le (a : ellOneOn 𝕜 K) (f : CZero 𝕜 K) :
    ‖∑' x : K, a x * f x‖ ≤ ‖a‖ * ‖f‖ := by
  calc
    _ ≤ ∑' x : K, ‖a x * f x‖ := norm_tsum_le_tsum_norm
      (((ellOneOn_summable_norm a).mul_right ‖f‖).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_CZero_apply_le f x) (norm_nonneg _)))
    _ ≤ ∑' x : K, ‖a x‖ * ‖f‖ := tsum_le_tsum
      (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_CZero_apply_le f x) (norm_nonneg _))
      (((ellOneOn_summable_norm a).mul_right ‖f‖).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_CZero_apply_le f x) (norm_nonneg _)))
      ((ellOneOn_summable_norm a).mul_right ‖f‖)
    _ = ‖a‖ * ‖f‖ := by rw [tsum_mul_right, ellOneOn_norm_eq_tsum]

/-- The functional represented by an ℓ¹ family of point masses. -/
def atomicFunctional (a : ellOneOn 𝕜 K) : CZero 𝕜 K →L[𝕜] 𝕜 :=
  ({ toFun f := ∑' x : K, a x * f x
     map_add' f g := by
       change (∑' x : K, a x * (f x + g x)) = _
       simp_rw [mul_add]
       exact (summable_atomic_values a f).tsum_add (summable_atomic_values a g)
     map_smul' c f := by
       change (∑' x : K, a x * (c * f x)) = c * _
       simp_rw [mul_left_comm (a := a _) (b := c)]
       exact tsum_mul_left } : CZero 𝕜 K →ₗ[𝕜] 𝕜).mkContinuous
    ‖a‖ (norm_atomic_values_tsum_le a)

@[simp] theorem atomicFunctional_apply (a : ellOneOn 𝕜 K) (f : CZero 𝕜 K) :
    atomicFunctional a f = ∑' x : K, a x * f x := rfl

theorem norm_atomicFunctional_le (a : ellOneOn 𝕜 K) : ‖atomicFunctional a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (norm_atomic_values_tsum_le a)

/-- Synthesis is a bounded linear operator, with operator norm at most one. -/
def atomicSynthesis : ellOneOn 𝕜 K →L[𝕜] (CZero 𝕜 K →L[𝕜] 𝕜) :=
  ({ toFun := atomicFunctional
     map_add' a b := by
       apply ContinuousLinearMap.ext
       intro f
       change (∑' x : K, (a x + b x) * f x) = _
       simp_rw [add_mul]
       exact (summable_atomic_values a f).tsum_add (summable_atomic_values b f)
     map_smul' c a := by
       apply ContinuousLinearMap.ext
       intro f
       change (∑' x : K, (c * a x) * f x) = c * _
       simp_rw [mul_assoc]
       exact tsum_mul_left } : ellOneOn 𝕜 K →ₗ[𝕜] (CZero 𝕜 K →L[𝕜] 𝕜)).mkContinuous
    1 (fun a : ellOneOn 𝕜 K => by simpa using norm_atomicFunctional_le a)

@[simp] theorem atomicSynthesis_apply (a : ellOneOn 𝕜 K) :
    atomicSynthesis (𝕜 := 𝕜) (K := K) a = atomicFunctional a := rfl

@[simp] theorem atomicFunctional_single (x : K) (c : 𝕜) :
    atomicFunctional (lp.single 1 x c) = c • evaluation x := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  rw [atomicFunctional_apply, tsum_eq_single x]
  · simp
  · intro y hy
    simp [lp.single_apply, hy]

theorem atomicFunctional_finset_apply (s : Finset K) (a : ellOneOn 𝕜 K) (f : CZero 𝕜 K) :
    atomicFunctional (restrictionL1 (s : Set K) a) f = ∑ x ∈ s, a x * f x := by
  rw [restrictionL1_finset]
  change atomicSynthesis (𝕜 := 𝕜) (K := K) (∑ x ∈ s, lp.single 1 x (a x)) f = _
  rw [map_sum]
  simp only [ContinuousLinearMap.sum_apply, atomicSynthesis_apply, atomicFunctional_single,
    ContinuousLinearMap.smul_apply, evaluation_apply, smul_eq_mul]

variable [LocallyCompactSpace K] [T2Space K]

/-- Finite point masses have exactly the ℓ¹ norm, by simultaneous phase interpolation. -/
theorem norm_atomicFunctional_finset (hK : IsScattered K) (s : Finset K)
    (a : ellOneOn 𝕜 K) :
    ‖atomicFunctional (restrictionL1 (s : Set K) a)‖ = ‖restrictionL1 (s : Set K) a‖ := by
  classical
  obtain ⟨U⟩ := exists_neighborhoodFamily hK (fun x : ↥s => x.val) Subtype.val_injective
  let η := neighborhoodPhaseFunction U (fun x : ↥s => a x.val)
  have hη : ‖η‖ ≤ 1 := neighborhoodPhaseFunction_norm_le U _
  have hvalue : atomicFunctional (restrictionL1 (s : Set K) a) η =
      (‖restrictionL1 (s : Set K) a‖ : 𝕜) := by
    rw [atomicFunctional_finset_apply, restrictionL1_finset_norm, RCLike.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show η x = scalarPhase (a x) from neighborhoodPhaseFunction_at_point U _ ⟨x, hx⟩,
      mul_comm, scalarPhase_mul]
  apply le_antisymm (norm_atomicFunctional_le _) _
  have hb := (atomicFunctional (restrictionL1 (s : Set K) a)).le_opNorm η
  rw [hvalue, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hb
  exact hb.trans (by simpa using mul_le_mul_of_nonneg_left hη (norm_nonneg _))

/-- Finite truncation extends the norm identity to every ℓ¹ family. -/
theorem norm_atomicFunctional (hK : IsScattered K) (a : ellOneOn 𝕜 K) :
    ‖atomicFunctional a‖ = ‖a‖ := by
  apply le_antisymm (norm_atomicFunctional_le a)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs⟩ := exists_finite_restrictionL1_tail a (half_pos hε)
  have hnorm := norm_sub_norm_le a (restrictionL1 (s : Set K) a)
  have hfun := norm_sub_norm_le (atomicFunctional (restrictionL1 (s : Set K) a)) (atomicFunctional a)
  rw [norm_atomicFunctional_finset hK] at hfun
  have hbound : ‖atomicFunctional (restrictionL1 (s : Set K) a) - atomicFunctional a‖ ≤
      ‖a - restrictionL1 (s : Set K) a‖ := by
    rw [norm_sub_rev]
    change ‖atomicSynthesis (𝕜 := 𝕜) (K := K) a -
      atomicSynthesis (𝕜 := 𝕜) (K := K) (restrictionL1 (s : Set K) a)‖ ≤ _
    rw [← map_sub]
    exact norm_atomicFunctional_le _
  linarith

end JLMS
