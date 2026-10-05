import JLMS.CZeroTools
import JLMS.L1Restriction

/-!
# The atomic dual interface in Section 4

The structure specifies the complete Rudin representation, including point
evaluations. It is data, not an existence axiom. This file proves its coordinate
calculus; existence for arbitrary scattered K is proved in `JLMS.Rudin`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace JLMS

variable (𝕜 : Type*) [RCLike 𝕜]
variable (K : Type*) [TopologicalSpace K]

/-- A coordinate identification of the dual with ℓ¹(K), preserving point masses. -/
structure AtomicDualModel where
  representation : (CZero 𝕜 K →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] ellOneOn 𝕜 K
  pointMass : ∀ k : K,
    representation.symm (lp.single 1 k (1 : 𝕜)) = evaluation (𝕜 := 𝕜) k

/-- The locally compact variant of Rudin's theorem used in Section 4. -/
def RudinRepresentation [LocallyCompactSpace K] [T2Space K] : Prop :=
  IsScattered K → Nonempty (AtomicDualModel 𝕜 K)

variable {𝕜 K} (M : AtomicDualModel 𝕜 K)

-- Cache the dual-space instances locally so nested operator spaces elaborate
-- through the intended scalar field rather than searching the real scalar tower.
local instance : NormedAddCommGroup (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance : NormedSpace 𝕜 (CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

/-- The coordinate operator of the supplied atomic representation. -/
def atomicCoordinates : (CZero 𝕜 K →L[𝕜] 𝕜) →L[𝕜] ellOneOn 𝕜 K :=
  M.representation.toLinearIsometry.toContinuousLinearMap

/-- Actual restriction on the dual, transported through the representation. -/
def atomicRestriction (C : Set K) :
    (CZero 𝕜 K →L[𝕜] 𝕜) →L[𝕜] (CZero 𝕜 K →L[𝕜] 𝕜) :=
  M.representation.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((restrictionL1 C).comp (atomicCoordinates M))

@[simp] theorem atomicCoordinates_apply (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    atomicCoordinates M φ = M.representation φ := rfl

@[simp] theorem atomicRestriction_coordinates (C : Set K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    M.representation (atomicRestriction M C φ) = restrictionL1 C (M.representation φ) :=
  M.representation.apply_symm_apply _

@[simp] theorem atomicRestriction_norm (C : Set K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    ‖atomicRestriction M C φ‖ = ‖restrictionL1 C (M.representation φ)‖ := by
  rw [← M.representation.norm_map (atomicRestriction M C φ), atomicRestriction_coordinates]

theorem atomicRestriction_norm_le (C : Set K) : ‖atomicRestriction (𝕜 := 𝕜) M C‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro φ
  rw [one_mul, atomicRestriction_norm, ← M.representation.norm_map φ]
  exact restrictL1_norm_le C _

theorem atomicRestriction_compact (s : Finset K) :
    IsCompactOperator (atomicRestriction M (s : Set K)) := by
  exact ((restrictionL1_compact (𝕜 := 𝕜) s).comp_clm (atomicCoordinates M)).clm_comp
    M.representation.symm.toLinearIsometry.toContinuousLinearMap

/-- The point-mass condition extends to arbitrary scalar coefficients. -/
theorem atomicDual_single (k : K) (a : 𝕜) :
    M.representation.symm (lp.single 1 k a) = a • evaluation (𝕜 := 𝕜) k := by
  have h : (lp.single 1 k a : ellOneOn 𝕜 K) = a • lp.single 1 k (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      lp.single_smul (E := fun _ : K => 𝕜) 1 k a (1 : 𝕜)
  rw [h, map_smul, M.pointMass]

/-- The representation recovers a functional by a convergent sum of atoms. -/
theorem atomicDual_hasSum (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    HasSum (fun k => M.representation φ k • evaluation (𝕜 := 𝕜) k) φ := by
  have h := lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) (M.representation φ)
  have hmap := h.map M.representation.symm.toLinearIsometry.toContinuousLinearMap
    M.representation.symm.continuous
  change HasSum (fun k => M.representation.symm (lp.single 1 k (M.representation φ k)))
    (M.representation.symm (M.representation φ)) at hmap
  simpa only [atomicDual_single, LinearIsometryEquiv.symm_apply_apply] using hmap

/-- The scalar pairing is the same atomic series as in the paper. -/
theorem atomicDual_apply_hasSum (φ : CZero 𝕜 K →L[𝕜] 𝕜) (f : CZero 𝕜 K) :
    HasSum (fun k => M.representation φ k * f k) (φ f) := by
  have h := (atomicDual_hasSum M φ).map (ContinuousLinearMap.apply 𝕜 𝕜 f)
    (ContinuousLinearMap.apply 𝕜 𝕜 f).continuous
  change HasSum (fun k => (M.representation φ k • evaluation (𝕜 := 𝕜) k) f) (φ f) at h
  simpa only [ContinuousLinearMap.smul_apply, evaluation_apply, smul_eq_mul] using h

theorem atomicRestriction_finset (s : Finset K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    atomicRestriction M (s : Set K) φ =
      ∑ k ∈ s, M.representation φ k • evaluation (𝕜 := 𝕜) k := by
  change M.representation.symm (restrictionL1 (s : Set K) (M.representation φ)) = _
  rw [restrictionL1_finset, map_sum]
  exact Finset.sum_congr rfl (fun k _ => atomicDual_single M k _)

theorem atomicRestriction_finset_apply (s : Finset K) (φ : CZero 𝕜 K →L[𝕜] 𝕜)
    (f : CZero 𝕜 K) : atomicRestriction M (s : Set K) φ f =
      ∑ k ∈ s, M.representation φ k * f k := by
  rw [atomicRestriction_finset]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    evaluation_apply, smul_eq_mul]

theorem atomicRestriction_norm_union (C D : Set K) (hCD : Disjoint C D)
    (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    ‖atomicRestriction M (C ∪ D) φ‖ =
      ‖atomicRestriction M C φ‖ + ‖atomicRestriction M D φ‖ := by
  simp only [atomicRestriction_norm]
  exact restrictionL1_norm_union _ _ hCD _

theorem exists_finite_atomicRestriction_tail (φ : CZero 𝕜 K →L[𝕜] 𝕜)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset K, ‖φ - atomicRestriction M (s : Set K) φ‖ < ε := by
  obtain ⟨s, hs⟩ := exists_finite_restrictionL1_tail (M.representation φ) hε
  refine ⟨s, ?_⟩
  rwa [← M.representation.norm_map, map_sub, atomicRestriction_coordinates]

theorem atomicDual_countable_support (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    (Function.support (M.representation φ)).Countable :=
  ellOneOn_countable_support _

theorem atomicRestriction_tail_norm_mono {C D : Set K} (hCD : C ⊆ D)
    (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    ‖φ - atomicRestriction M D φ‖ ≤ ‖φ - atomicRestriction M C φ‖ := by
  rw [← M.representation.norm_map (φ - atomicRestriction M D φ),
    ← M.representation.norm_map (φ - atomicRestriction M C φ)]
  simp only [map_sub, atomicRestriction_coordinates]
  exact restrictionL1_tail_norm_mono hCD _

theorem atomicRestriction_compl (C : Set K) (φ : CZero 𝕜 K →L[𝕜] 𝕜) :
    φ - atomicRestriction M C φ = atomicRestriction M Cᶜ φ := by
  apply M.representation.injective
  simp only [map_sub, atomicRestriction_coordinates]
  exact restrictionL1_tail_eq C _

end JLMS
