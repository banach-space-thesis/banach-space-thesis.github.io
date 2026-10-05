import JLMS.OrdinalSpaceBlocksDecomposition

/-! A bounded anchored reader for arbitrary ordinal-index blocks.
Ceiling residuals vanish on the embedded boundary, so their block norms
vanish along the cofinite filter even at uncountable cofinality. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000
variable {𝕜 : Type*} [RCLike 𝕜] {γ β : Ordinal.{u}}
attribute [local instance] JLMS.ordinalLimitFunctionGroup JLMS.ordinalLimitFunctionSpace

variable (g : C(JLMS.OrdinalInterval γ, JLMS.OrdinalInterval β))
  (hg : StrictMono g)
  (htop : g ⟨γ, Ordinal.zero_le _, le_rfl⟩ = ⟨β, Ordinal.zero_le _, le_rfl⟩)

include hg htop in
theorem ordinalEmbeddingCeiling_eq_block_right (i : Iio γ)
    (x : JLMS.OrdinalInterval β) (hx : x ∈ JLMS.ordinalSpaceBlockSet g i) :
    JLMS.ordinalEmbeddingCeiling g x =
      ⟨Order.succ i.val, Ordinal.zero_le _, Order.succ_le_of_lt i.property⟩ := by
  apply Subtype.ext
  apply le_antisymm
  · exact (JLMS.ordinalEmbeddingCeiling_le_iff g hg.monotone htop x
      ⟨Order.succ i.val, Ordinal.zero_le _, Order.succ_le_of_lt i.property⟩).mpr hx.2
  · apply Order.succ_le_of_lt
    by_contra hn
    have hle : JLMS.ordinalEmbeddingCeiling g x ≤
        (⟨i.val, Ordinal.zero_le _, i.property.le⟩ : JLMS.OrdinalInterval γ) := le_of_not_gt hn
    have hh := (JLMS.ordinalEmbeddingCeiling_le_iff g hg.monotone htop x
      ⟨i.val, Ordinal.zero_le _, i.property.le⟩).mp hle
    exact hx.1.not_ge hh

def ordinalCeilingResidual (f : JLMS.OrdinalC 𝕜 β) : JLMS.OrdinalC 𝕜 β :=
  f - JLMS.ordinalSpaceCeilingExtension g hg htop (JLMS.ordinalSpaceRestriction g f)

theorem ordinalCeilingResidual_range_zero (f : JLMS.OrdinalC 𝕜 β)
    (x : JLMS.OrdinalInterval γ) : ordinalCeilingResidual g hg htop f (g x) = 0 := by
  simp only [ordinalCeilingResidual, ContinuousMap.sub_apply,
    JLMS.ordinalSpaceCeilingExtension_apply, JLMS.ordinalSpaceRestriction_apply,
    JLMS.ordinalEmbeddingCeiling_apply_image g hg htop, sub_self]

variable {I : Type*} {D : I → Type*}
  [∀ i, TopologicalSpace (D i)] [∀ i, CompactSpace (D i)]

local instance anchoredReadCoordinateGroup (i : I) : NormedAddCommGroup C(D i, 𝕜) := inferInstance
local instance anchoredReadCoordinateSpace (i : I) : NormedSpace 𝕜 C(D i, 𝕜) := inferInstance
local instance anchoredReadSumGroup :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance
local instance anchoredReadSumSpace :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜))) := inferInstance

def ordinalAnchoredReadCoordinate (k : I → Iio γ)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (f : JLMS.OrdinalC 𝕜 β) (i : I) : C(D i, 𝕜) :=
  f.comp (q i) - ContinuousMap.const _
    (f (g ⟨Order.succ (k i).val, Ordinal.zero_le _, Order.succ_le_of_lt (k i).property⟩))

@[simp] theorem ordinalAnchoredReadCoordinate_apply (k : I → Iio γ)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β)) (f : JLMS.OrdinalC 𝕜 β)
    (i : I) (x : D i) :
    ordinalAnchoredReadCoordinate g k q f i x = f (q i x) -
      f (g ⟨Order.succ (k i).val, Ordinal.zero_le _, Order.succ_le_of_lt (k i).property⟩) := rfl

theorem ordinalAnchoredReadCoordinate_eq_residual (k : I → Iio γ)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i))
    (f : JLMS.OrdinalC 𝕜 β) (i : I) (x : D i) :
    ordinalAnchoredReadCoordinate g k q f i x = ordinalCeilingResidual g hg htop f (q i x) := by
  change f (q i x) - f (g _) = f (q i x) - f (g (JLMS.ordinalEmbeddingCeiling g (q i x)))
  rw [ordinalEmbeddingCeiling_eq_block_right g hg htop (k i) (q i x) (hq i x)]

theorem ordinalAnchoredReadCoordinate_norm_le (k : I → Iio γ)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (f : JLMS.OrdinalC 𝕜 β) (i : I) :
    ‖ordinalAnchoredReadCoordinate g k q f i‖ ≤ 2 * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖f (q i x) - f (g _)‖ ≤ 2 * ‖f‖
  exact (norm_sub_le _ _).trans (by
    have := f.norm_coe_le_norm (q i x)
    have := f.norm_coe_le_norm (g ⟨Order.succ (k i).val, Ordinal.zero_le _,
      Order.succ_le_of_lt (k i).property⟩)
    linarith)

include hg htop in
theorem ordinalAnchoredReadCoordinate_tendsto
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (k : I → Iio γ) (hk : Function.Injective k)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i))
    (f : JLMS.OrdinalC 𝕜 β) :
    Tendsto (fun i => ‖ordinalAnchoredReadCoordinate g k q f i‖) cofinite (𝓝 0) := by
  have ht := (JLMS.tendsto_norm_ordinalSpaceBlockRestrictions g hg hzero htop
    (ordinalCeilingResidual g hg htop f) (ordinalCeilingResidual_range_zero g hg htop f)).comp
      hk.tendsto_cofinite
  apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) ht
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  rw [ordinalAnchoredReadCoordinate_eq_residual g hg htop k q hq f i x]
  exact ((ordinalCeilingResidual g hg htop f).restrict (JLMS.ordinalSpaceBlockSet g (k i))).norm_coe_le_norm
    ⟨q i x, hq i x⟩

def ordinalAnchoredBlockReadback
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (k : I → Iio γ) (hk : Function.Injective k)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i)) :
    JLMS.OrdinalC 𝕜 β →L[𝕜] JLMS.CZeroSum 𝕜 (fun i => C(D i, 𝕜)) :=
  LinearMap.mkContinuous
    { toFun := fun f => JLMS.CZeroSum.mk (ordinalAnchoredReadCoordinate g k q f)
        (ordinalAnchoredReadCoordinate_tendsto g hg htop hzero k hk q hq f)
      map_add' := by
        intro f f'
        apply JLMS.CZeroSum.ext
        intro i
        ext x
        change (f (q i x) + f' (q i x)) - (f (g _) + f' (g _)) =
          (f (q i x) - f (g _)) + (f' (q i x) - f' (g _))
        ring
      map_smul' := by
        intro c f
        apply JLMS.CZeroSum.ext
        intro i
        ext x
        change c * f (q i x) - c * f (g _) = c * (f (q i x) - f (g _))
        ring }
    2 (fun f => JLMS.CZeroSum.norm_le (by positivity)
      (ordinalAnchoredReadCoordinate_norm_le g k q f))

@[simp] theorem ordinalAnchoredBlockReadback_apply
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (k : I → Iio γ) (hk : Function.Injective k)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i))
    (f : JLMS.OrdinalC 𝕜 β) (i : I) (x : D i) :
    ordinalAnchoredBlockReadback g hg htop hzero k hk q hq f i x = f (q i x) -
      f (g ⟨Order.succ (k i).val, Ordinal.zero_le _, Order.succ_le_of_lt (k i).property⟩) := rfl

theorem ordinalAnchoredBlockReadback_norm_le
    (hzero : g ⟨0, le_rfl, Ordinal.zero_le _⟩ = ⟨0, le_rfl, Ordinal.zero_le _⟩)
    (k : I → Iio γ) (hk : Function.Injective k)
    (q : ∀ i, C(D i, JLMS.OrdinalInterval β))
    (hq : ∀ i x, q i x ∈ JLMS.ordinalSpaceBlockSet g (k i)) :
    ‖ordinalAnchoredBlockReadback (𝕜 := 𝕜) g hg htop hzero k hk q hq‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  apply JLMS.CZeroSum.norm_le (by positivity)
  exact ordinalAnchoredReadCoordinate_norm_le g k q f

end Posets
