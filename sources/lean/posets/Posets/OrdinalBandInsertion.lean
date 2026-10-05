import Posets.WolfeLaminarEmbeddingClopenTop
import Posets.OrdinalBandCompressionClosure
import ThesisCommon.Analysis.ContinuousMapPullback

/-! Actual insertion into a compact clopen band: pull back along a continuous
coordinate map, then extend by zero. A section of the coordinate map reads
the inserted function exactly. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L]
variable (H : Set K) [CompactSpace H] (hH : IsClopen H) (p : C(H, L))

def ordinalBandInsert : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K :=
  (wolfeClopenZeroExtension H hH).toContinuousLinearMap.comp
    (ThesisCommon.continuousMapPullback p)

@[simp] theorem ordinalBandInsert_apply_mem (f : C(L, 𝕜)) (x : H) :
    ordinalBandInsert H hH p f x = f (p x) :=
  wolfeClopenZeroExtend_apply_mem H hH (f.comp p) x

@[simp] theorem ordinalBandInsert_apply_notMem (f : C(L, 𝕜)) {x : K} (hx : x ∉ H) :
    ordinalBandInsert H hH p f x = 0 :=
  wolfeClopenZeroExtend_apply_notMem H hH (f.comp p) hx

theorem ordinalBandInsert_norm_le : ‖ordinalBandInsert (𝕜 := 𝕜) H hH p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖wolfeClopenZeroExtension (𝕜 := 𝕜) H hH (f.comp p)‖ ≤ 1 * ‖f‖
  rw [(wolfeClopenZeroExtension (𝕜 := 𝕜) H hH).norm_map, one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (p x))

theorem ordinalBandInsert_support (f : C(L, 𝕜)) :
    Function.support (ordinalBandInsert H hH p f) ⊆ H := by
  intro x hx
  by_contra hnot
  exact hx (ordinalBandInsert_apply_notMem H hH p f hnot)

theorem ordinalBandInsert_constant_on_fiber (f : C(L, 𝕜)) (x y : H)
    (hxy : p x = p y) : ordinalBandInsert H hH p f x = ordinalBandInsert H hH p f y := by
  simp only [ordinalBandInsert_apply_mem, hxy]

theorem ordinalBandInsert_read (q : C(L, H)) (hq : Function.RightInverse q p)
    (f : C(L, 𝕜)) (x : L) : ordinalBandInsert H hH p f (q x) = f x := by
  rw [ordinalBandInsert_apply_mem, hq x]

theorem ordinalBandInsert_read_comp (q : C(L, H)) (hq : Function.RightInverse q p) :
    (ordinalBandRead (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ q)).comp
      (ordinalBandInsert (𝕜 := 𝕜) H hH p) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) := by
  ext f x
  exact ordinalBandInsert_read H hH p q hq f x

end Posets
