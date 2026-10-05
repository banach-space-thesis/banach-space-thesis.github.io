import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UnitInterval

/-! Contractive pullbacks, restrictions and interval extension operators
on actual compact continuous-function spaces. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L]

def continuousMapPullback (f : C(K, L)) : C(L, 𝕜) →L[𝕜] C(K, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun g => g.comp f
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun g => (ContinuousMap.norm_le _ (by simpa only [one_mul] using norm_nonneg g)).2
      (fun x => by simpa only [one_mul] using g.norm_coe_le_norm (f x)))

@[simp] theorem continuousMapPullback_apply (f : C(K, L)) (g : C(L, 𝕜)) (x : K) :
    continuousMapPullback f g x = g (f x) := rfl

theorem norm_continuousMapPullback_le (f : C(K, L)) :
    ‖continuousMapPullback (𝕜 := 𝕜) f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

def continuousMapRestrict (A : Set K) [CompactSpace A] : C(K, 𝕜) →L[𝕜] C(A, 𝕜) :=
  continuousMapPullback ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem continuousMapRestrict_apply (A : Set K) [CompactSpace A]
    (f : C(K, 𝕜)) (x : A) : continuousMapRestrict A f x = f x := rfl

theorem norm_continuousMapRestrict_le (A : Set K) [CompactSpace A] :
    ‖continuousMapRestrict (𝕜 := 𝕜) A‖ ≤ 1 := norm_continuousMapPullback_le _

def continuousMapHomeomorphEquiv (e : K ≃ₜ L) : C(K, 𝕜) ≃L[𝕜] C(L, 𝕜) :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun f => f.comp ⟨e.symm, e.symm.continuous⟩
      invFun := fun f => f.comp ⟨e, e.continuous⟩
      left_inv := by intro f; ext x; simp
      right_inv := by intro f; ext x; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1 1
    (fun f => (ContinuousMap.norm_le _ (by simpa only [one_mul] using norm_nonneg f)).2
      (fun x => by simpa only [one_mul] using f.norm_coe_le_norm (e.symm x)))
    (fun f => (ContinuousMap.norm_le _ (by simpa only [one_mul] using norm_nonneg f)).2
      (fun x => by simpa only [one_mul] using f.norm_coe_le_norm (e x)))

instance unitSubintervalCompactSpace (a b : UnitInterval) : CompactSpace (Set.Icc a b) :=
  isCompact_iff_compactSpace.mp isClosed_Icc.isCompact

def unitIntervalExtend (a b : UnitInterval) (hab : a ≤ b) :
    C(Set.Icc a b, 𝕜) →L[𝕜] C(UnitInterval, 𝕜) := by
  letI : Fact (a ≤ b) := ⟨hab⟩
  exact continuousMapPullback (ContinuousMap.projIccCM (a := a) (b := b))

theorem norm_unitIntervalExtend_le (a b : UnitInterval) (hab : a ≤ b) :
    ‖unitIntervalExtend (𝕜 := 𝕜) a b hab‖ ≤ 1 := by
  exact norm_continuousMapPullback_le _

theorem unitIntervalRestrict_comp_extend (a b : UnitInterval) (hab : a ≤ b) :
    (continuousMapRestrict (𝕜 := 𝕜) (Set.Icc a b)).comp (unitIntervalExtend a b hab) =
      ContinuousLinearMap.id 𝕜 C(Set.Icc a b, 𝕜) := by
  ext f x
  change f (Set.projIcc a b hab x.val) = f x
  rw [Set.projIcc_of_mem hab x.property]

theorem norm_unitIntervalExtend (a b : UnitInterval) (hab : a ≤ b) :
    ‖unitIntervalExtend (𝕜 := 𝕜) a b hab‖ = 1 := by
  letI : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  apply le_antisymm (norm_unitIntervalExtend_le a b hab)
  have h := ContinuousLinearMap.opNorm_comp_le
    (continuousMapRestrict (𝕜 := 𝕜) (Set.Icc a b)) (unitIntervalExtend a b hab)
  rw [unitIntervalRestrict_comp_extend, ContinuousLinearMap.norm_id] at h
  apply h.trans
  simpa only [one_mul] using (mul_le_mul_of_nonneg_right
    (norm_continuousMapRestrict_le (𝕜 := 𝕜) (Set.Icc a b))
      (norm_nonneg (unitIntervalExtend (𝕜 := 𝕜) a b hab)))

end ThesisCommon
