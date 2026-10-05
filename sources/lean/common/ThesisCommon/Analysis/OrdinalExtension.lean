import ThesisCommon.Analysis.OrdinalRetraction
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Norm-one simultaneous extensions from nonempty closed subsets of ordinal
intervals. Compactness of the subset is expressed by its actual compact-space
instance; every closed subset of an ordinal interval has this instance. -/
noncomputable section
open Set Topology
universe u v
namespace ThesisCommon

def ordinalEmbeddedRetraction {K : Type v} [TopologicalSpace K] [CompactSpace K]
    [Nonempty K] {f : K → Ordinal.{u}} (hf : IsEmbedding f) : C(Ordinal.{u}, K) :=
  let e := hf.toHomeomorph
  let r := ordinalCompactRetraction (isCompact_range hf.continuous) (range_nonempty f)
  ⟨fun x => e.symm (r x), e.symm.continuous.comp r.continuous⟩

theorem ordinalEmbeddedRetraction_apply {K : Type v} [TopologicalSpace K] [CompactSpace K]
    [Nonempty K] {f : K → Ordinal.{u}} (hf : IsEmbedding f) (a : K) :
    ordinalEmbeddedRetraction hf (f a) = a := by
  let e := hf.toHomeomorph
  apply e.injective
  change e (e.symm _) = e a
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact ordinalCeiling_eq_of_mem (mem_range_self a)

def ordinalIntervalRetraction {α : Ordinal.{u}} (A : Set (OrdinalInterval α))
    [CompactSpace A] [Nonempty A] : C(OrdinalInterval α, A) :=
  let f : A → Ordinal.{u} := fun a => a.val.val
  let hf : IsEmbedding f := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  (ordinalEmbeddedRetraction hf).comp ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem ordinalIntervalRetraction_apply {α : Ordinal.{u}}
    (A : Set (OrdinalInterval α)) [CompactSpace A] [Nonempty A] (a : A) :
    ordinalIntervalRetraction A a.val = a :=
  ordinalEmbeddedRetraction_apply _ a

variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalClosedExtend {α : Ordinal.{u}} (A : Set (OrdinalInterval α))
    [CompactSpace A] [Nonempty A] : C(A, 𝕜) →L[𝕜] OrdinalContinuous 𝕜 α :=
  continuousMapPullback (ordinalIntervalRetraction A)

theorem norm_ordinalClosedExtend_le {α : Ordinal.{u}} (A : Set (OrdinalInterval α))
    [CompactSpace A] [Nonempty A] : ‖ordinalClosedExtend (𝕜 := 𝕜) A‖ ≤ 1 :=
  norm_continuousMapPullback_le _

theorem ordinalClosedRestrict_comp_extend {α : Ordinal.{u}}
    (A : Set (OrdinalInterval α)) [CompactSpace A] [Nonempty A] :
    (continuousMapRestrict (𝕜 := 𝕜) A).comp (ordinalClosedExtend A) =
      ContinuousLinearMap.id 𝕜 C(A, 𝕜) := by
  ext f a
  change f (ordinalIntervalRetraction A a.val) = f a
  rw [ordinalIntervalRetraction_apply]

theorem norm_ordinalClosedExtend {α : Ordinal.{u}} (A : Set (OrdinalInterval α))
    [CompactSpace A] [Nonempty A] : ‖ordinalClosedExtend (𝕜 := 𝕜) A‖ = 1 := by
  apply le_antisymm (norm_ordinalClosedExtend_le A)
  have h := ContinuousLinearMap.opNorm_comp_le
    (continuousMapRestrict (𝕜 := 𝕜) A) (ordinalClosedExtend A)
  rw [ordinalClosedRestrict_comp_extend, ContinuousLinearMap.norm_id] at h
  apply h.trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_continuousMapRestrict_le (𝕜 := 𝕜) A)
    (norm_nonneg (ordinalClosedExtend (𝕜 := 𝕜) A))

/-- The exact norm-one conclusion used in the manuscript, with the necessary
nonemptiness hypothesis explicit. -/
theorem ordinal_exists_norm_one_extension {α : Ordinal.{u}}
    (A : Set (OrdinalInterval α)) [CompactSpace A] (hne : A.Nonempty) :
    ∃ S : C(A, 𝕜) →L[𝕜] OrdinalContinuous 𝕜 α,
      ‖S‖ = 1 ∧ (continuousMapRestrict A).comp S = ContinuousLinearMap.id 𝕜 C(A, 𝕜) := by
  letI : Nonempty A := hne.to_subtype
  exact ⟨ordinalClosedExtend A, norm_ordinalClosedExtend A, ordinalClosedRestrict_comp_extend A⟩

end ThesisCommon
