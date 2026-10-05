import JLMS.Definitions
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Continuous functions are constant on an ordinal tail of uncountable cofinality

Continuity gives a tail for each positive geometric accuracy. Uncountable
cofinality bounds all countably many starting points below the endpoint.
Beyond their supremum, every accuracy holds, so the values equal the endpoint.
This is a reusable topological ingredient for the initial-ordinal argument.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u

theorem exists_constant_ordinal_tail {M : Type*} [MetricSpace M]
    {α : Ordinal.{u}} (hα : Cardinal.aleph0 < α.cof)
    (f : Ordinal.{u} → M) (hf : ContinuousAt f α) :
    ∃ β < α, ∀ x, β < x → x ≤ α → f x = f α := by
  have hαpos : 0 < α := by
    apply pos_iff_ne_zero.mpr
    intro h
    simp [h] at hα
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hrone : r < 1 := by norm_num [r]
  have htail (n : ℕ) : ∃ β < α,
      ∀ x ∈ Set.Ioc β α, dist (f x) (f α) < r ^ n := by
    have hh := hf.eventually (Metric.ball_mem_nhds (f α) (pow_pos hr n))
    obtain ⟨β, hβα, hβ⟩ :=
      (SuccOrder.hasBasis_nhds_Ioc_of_exists_lt ⟨0, hαpos⟩).mem_iff.mp hh
    exact ⟨β, hβα, fun x hx => hβ hx⟩
  choose b hb hbound using htail
  have hs : (⨆ n, b n) < α :=
    Ordinal.iSup_lt_ord_lift (by simpa using hα) hb
  refine ⟨⨆ n, b n, hs, fun x hx hxα => ?_⟩
  have hdist (n : ℕ) : dist (f x) (f α) ≤ r ^ n :=
    (hbound n x ⟨(Ordinal.le_iSup b n).trans_lt hx, hxα⟩).le
  have hzero : dist (f x) (f α) ≤ 0 :=
    ge_of_tendsto (show Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 (0 : ℝ)) from
      tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hrone)
      (Filter.Eventually.of_forall hdist)
  exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)

def ordinalIntervalClamp (α : Ordinal.{u}) : C(Ordinal.{u}, OrdinalInterval α) where
  toFun x := ⟨min x α, by exact ⟨Ordinal.zero_le _, min_le_right _ _⟩⟩
  continuous_toFun := (continuous_id.min continuous_const).subtype_mk _

@[simp] theorem ordinalIntervalClamp_coe (α : Ordinal.{u}) (x : OrdinalInterval α) :
    ordinalIntervalClamp α x = x := by
  apply Subtype.ext
  exact min_eq_left x.property.2

theorem exists_constant_ordinalC_tail {𝕜 : Type*} [RCLike 𝕜]
    {α : Ordinal.{u}} (hα : Cardinal.aleph0 < α.cof) (f : OrdinalC 𝕜 α) :
    ∃ β < α, ∀ x : OrdinalInterval α, β < x.val → f x = f ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
  obtain ⟨β, hβ, hh⟩ := exists_constant_ordinal_tail hα
    (fun x => f (ordinalIntervalClamp α x))
    (f.continuous.comp (ordinalIntervalClamp α).continuous).continuousAt
  refine ⟨β, hβ, fun x hx => ?_⟩
  have he : ordinalIntervalClamp α α = ⟨α, Ordinal.zero_le _, le_rfl⟩ := by
    apply Subtype.ext
    exact min_self α
  simpa only [ordinalIntervalClamp_coe, he] using hh x.val hx x.property.2

end JLMS
