import Posets.OrdinalLiftSelection
import Posets.OrdinalLiftGraph
import ThesisCommon.Analysis.OrdinalClosedCopies

/-! Continuous, uniformly bounded point-evaluation lifts on a further
closed ordinal copy, obtained from the compact Hahn--Banach graph. -/
noncomputable section
open Set Topology TopologicalSpace ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_ordinalLiftRows [SeparableSpace E] {α : Ordinal.{0}}
    (hα : α ≠ 0) (hcα : α.card ≤ Cardinal.aleph0)
    (J : OrdinalContinuous 𝕜 (ω ^ α) →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ a, c * ‖a‖ ≤ ‖J a‖) :
    ∃ e : OrdinalClosedCopy (ω ^ α) (ω ^ α),
    ∃ μ : C(OrdinalInterval (ω ^ α), WeakDual 𝕜 E),
      (∀ t, ‖WeakDual.toStrongDual (μ t)‖ ≤ 1 / c) ∧
      ∀ t a, μ t (J a) = a (e.val t) := by
  letI instCountableOrdinal : Countable (OrdinalInterval (ω ^ α)) :=
    ordinalInterval_countable_of_card (omega_power_card_le_aleph0 hcα)
  letI instMetricOrdinal : MetrizableSpace (OrdinalInterval (ω ^ α)) :=
    alspach_countable_compact_metrizable _
  letI instMetricGraph : MetrizableSpace (OrdinalLiftGraph J (1 / c)) :=
    ordinalLiftGraph_metrizable J (1 / c)
  let p := ordinalLiftGraphProjection J (1 / c)
  have hp : p '' univ = univ := by
    rw [image_univ]
    exact (ordinalLiftGraphProjection_surjective J hc hlower).range_eq
  obtain ⟨g, _, hgi⟩ := ordinalLift_exists_continuous_section hα hcα p isCompact_univ hp
  let e : OrdinalClosedCopy (ω ^ α) (ω ^ α) := ⟨p.comp g, hgi⟩
  let μ : C(OrdinalInterval (ω ^ α), WeakDual 𝕜 E) :=
    ⟨fun t => (g t).val.2.val, continuous_subtype_val.comp
      (continuous_snd.comp (continuous_subtype_val.comp g.continuous))⟩
  exact ⟨e, μ, fun t => (g t).val.2.property, fun t a => (g t).property a⟩

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def ordinalLiftRowsLinearMap (μ : C(K, WeakDual 𝕜 E)) : E →ₗ[𝕜] C(K, 𝕜) where
  toFun a := ⟨fun t => μ t a, (WeakDual.eval_continuous a).comp μ.continuous⟩
  map_add' a b := by ext t; exact map_add (WeakDual.toStrongDual (μ t)) a b
  map_smul' r a := by ext t; exact map_smul (WeakDual.toStrongDual (μ t)) r a

theorem ordinalLiftRowsLinearMap_bound (μ : C(K, WeakDual 𝕜 E)) {r : ℝ} (hr : 0 ≤ r)
    (hμ : ∀ t, ‖WeakDual.toStrongDual (μ t)‖ ≤ r) (a : E) :
    ‖ordinalLiftRowsLinearMap μ a‖ ≤ r * ‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hr (norm_nonneg a))).mpr
  intro t
  exact ((WeakDual.toStrongDual (μ t)).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (hμ t) (norm_nonneg a))

def ordinalLiftRowsOperator (μ : C(K, WeakDual 𝕜 E)) {r : ℝ} (hr : 0 ≤ r)
    (hμ : ∀ t, ‖WeakDual.toStrongDual (μ t)‖ ≤ r) : E →L[𝕜] C(K, 𝕜) :=
  (ordinalLiftRowsLinearMap μ).mkContinuous r (ordinalLiftRowsLinearMap_bound μ hr hμ)

theorem norm_ordinalLiftRowsOperator_le (μ : C(K, WeakDual 𝕜 E)) {r : ℝ} (hr : 0 ≤ r)
    (hμ : ∀ t, ‖WeakDual.toStrongDual (μ t)‖ ≤ r) :
    ‖ordinalLiftRowsOperator μ hr hμ‖ ≤ r :=
  ContinuousLinearMap.opNorm_le_bound _ hr (ordinalLiftRowsLinearMap_bound μ hr hμ)

end Posets
