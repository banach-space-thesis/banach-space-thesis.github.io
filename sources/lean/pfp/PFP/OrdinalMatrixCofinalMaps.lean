import JLMS.CZeroSumEquiv
import JLMS.CZeroSumOperators
import PFP.OrdinalMatrixSmallCodomain
/-! Coordinate insertion on a Banach c₀ sum and contractive retractions
between ordinal C-spaces. These are actual bounded maps used to recover the
whole sum from a cofinal subsequence of larger blocks. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS Filter Topology
universe u v
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000

def cZeroSum_insertFun {I J : Type u} {E : J → Type v}
    [∀ j, Zero (E j)] (e : I → J) (x : ∀ i, E (e i)) (j : J) : E j :=
  if h : ∃ i, e i = j then h.choose_spec ▸ x h.choose else 0

@[simp] theorem cZeroSum_insertFun_apply {I J : Type u} {E : J → Type v}
    [∀ j, Zero (E j)] (e : I → J) (he : Function.Injective e)
    (x : ∀ i, E (e i)) (i : I) : cZeroSum_insertFun e x (e i) = x i := by
  classical
  unfold cZeroSum_insertFun
  rw [dif_pos ⟨i, rfl⟩]
  generalize_proofs h
  have hi : h.choose = i := he h.choose_spec
  exact eq_of_heq ((eqRec_heq _ _).trans (congr_arg_heq x hi))

def cZeroSum_insert {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e)
    (x : CZeroSum 𝕜 (fun i => E (e i))) : CZeroSum 𝕜 E := by
  classical
  apply CZeroSum.mk (cZeroSum_insertFun e (fun i => x i))
  apply (tendsto_norm_cofinite_iff_finite _).mpr
  intro ε hε
  apply ((x.finite_norm_ge hε).image e).subset
  intro j hj
  change ε ≤ ‖cZeroSum_insertFun e (fun i => x i) j‖ at hj
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    exact ⟨i, by simpa only [cZeroSum_insertFun_apply e he] using hj, rfl⟩
  · simp only [cZeroSum_insertFun, dif_neg h, norm_zero] at hj
    exact (hε.not_ge hj).elim

@[simp] theorem cZeroSum_insert_apply {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e)
    (x : CZeroSum 𝕜 (fun i => E (e i))) (j : J) :
    cZeroSum_insert e he x j = cZeroSum_insertFun e (fun i => x i) j := rfl

def cZeroSum_insertCLM {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e) :
    CZeroSum 𝕜 (fun i => E (e i)) →L[𝕜] CZeroSum 𝕜 E := by
  classical
  let A : CZeroSum 𝕜 (fun i => E (e i)) →ₗ[𝕜] CZeroSum 𝕜 E := {
    toFun := cZeroSum_insert e he
    map_add' x y := by
      ext j
      by_cases h : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := h
        simp [cZeroSum_insertFun_apply e he]
      · simp [cZeroSum_insertFun, h]
    map_smul' a x := by
      ext j
      by_cases h : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := h
        simp [cZeroSum_insertFun_apply e he]
      · simp [cZeroSum_insertFun, h] }
  apply A.mkContinuous 1
  intro x
  rw [one_mul]
  apply CZeroSum.norm_le (norm_nonneg x)
  intro j
  change ‖cZeroSum_insertFun e (fun i => x i) j‖ ≤ ‖x‖
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    simpa only [cZeroSum_insertFun_apply e he] using x.norm_apply_le_norm i
  · simp [cZeroSum_insertFun, h]

@[simp] theorem cZeroSum_insertCLM_apply_selected {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e)
    (x : CZeroSum 𝕜 (fun i => E (e i))) (i : I) :
    cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) e he x (e i) = x i :=
  cZeroSum_insertFun_apply e he (fun i => x i) i

theorem norm_cZeroSum_insertCLM_le {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e) :
    ‖cZeroSum_insertCLM (𝕜 := 𝕜) (E := E) e he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply CZeroSum.norm_le (norm_nonneg x)
  intro j
  change ‖cZeroSum_insertFun e (fun i => x i) j‖ ≤ ‖x‖
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    simpa only [cZeroSum_insertFun_apply e he] using x.norm_apply_le_norm i
  · simp [cZeroSum_insertFun, h]

theorem norm_cZeroSum_comapCLM_le {I J : Type u} {E : J → Type v}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace 𝕜 (E j)]
    (e : I → J) (he : Function.Injective e) :
    ‖CZeroSum.comapCLM (𝕜 := 𝕜) (E := E) e he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using CZeroSum.norm_comap_le e he x

def ordinalInitialSegmentRead (α β : Ordinal.{ordU}) (h : α ≤ β) :
    OrdinalC 𝕜 β →L[𝕜] OrdinalC 𝕜 α :=
  ThesisCommon.continuousMapPullback
    ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans h⟩,
      continuous_subtype_val.subtype_mk _⟩

def ordinalInitialSegmentExtend (α β : Ordinal.{ordU}) :
    OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 β :=
  ThesisCommon.continuousMapPullback
    ((ordinalIntervalClamp α).comp ⟨Subtype.val, continuous_subtype_val⟩)

@[simp] theorem ordinalInitialSegmentRead_extend (α β : Ordinal.{ordU}) (h : α ≤ β)
    (f : OrdinalC 𝕜 α) :
    ordinalInitialSegmentRead α β h (ordinalInitialSegmentExtend α β f) = f := by
  ext x
  change f ⟨min x.val α, _⟩ = f x
  congr 1
  exact Subtype.ext (min_eq_left x.property.2)

theorem norm_ordinalInitialSegmentRead_le (α β : Ordinal.{ordU}) (h : α ≤ β) :
    ‖ordinalInitialSegmentRead (𝕜 := 𝕜) α β h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm _)

theorem norm_ordinalInitialSegmentExtend_le (α β : Ordinal.{ordU}) :
    ‖ordinalInitialSegmentExtend (𝕜 := 𝕜) α β‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm _)

end Posets.UniverseRegularMatrix


