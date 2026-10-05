import JLMS.OrdinalTailConstancy
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Constant tails for functions continuous below an uncountable-cofinality endpoint

No value at the endpoint is used. Persistent oscillation would supply two
interlaced increasing sequences. Their common supremum is below the endpoint,
where continuity contradicts that oscillation. Bounding countably many
accuracy cutoffs then gives exact constancy. This applies to Ogden's last
matrix column once its continuity below the endpoint has been established.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u
variable {M : Type*} [MetricSpace M]

theorem exists_small_diameter_ordinal_tail {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (f : Ordinal.{u} → M)
    (hf : ContinuousOn f (Set.Iio α)) {ε : ℝ} (hε : 0 < ε) :
    ∃ β < α, ∀ x, β < x → x < α → ∀ y, β < y → y < α → dist (f x) (f y) < ε := by
  by_contra h
  push_neg at h
  have hbad (β : {β : Ordinal.{u} // β < α}) := h β.val β.property
  choose X hX hXα Y hY hYα hdist using hbad
  let next (β : {β : Ordinal.{u} // β < α}) : {β : Ordinal.{u} // β < α} :=
    ⟨max (X β) (Y β), max_lt (hXα β) (hYα β)⟩
  have hαpos : 0 < α := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    simp [hzero] at hα
  let b (n : ℕ) : {β : Ordinal.{u} // β < α} := next^[n] ⟨0, hαpos⟩
  have hbsucc (n) : b (n + 1) = next (b n) := Function.iterate_succ_apply' next n _
  have hb (n) : (b n).val < (b (n + 1)).val := by
    rw [hbsucc]
    exact (hX (b n)).trans_le (le_max_left _ _)
  have hmono : Monotone (fun n => (b n).val) := (strictMono_nat_of_lt_succ hb).monotone
  let γ : Ordinal.{u} := ⨆ n, (b n).val
  have hγ : γ < α := Ordinal.iSup_lt_ord_lift (by simpa using hα) (fun n => (b n).property)
  have ht : Tendsto (fun n => (b n).val) atTop (𝓝 γ) :=
    tendsto_atTop_ciSup hmono ⟨γ, by
      rintro _ ⟨n, rfl⟩
      exact Ordinal.le_iSup (fun n => (b n).val) n⟩
  have ht' : Tendsto (fun n => (b (n + 1)).val) atTop (𝓝 γ) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have htX : Tendsto (fun n => X (b n)) atTop (𝓝 γ) :=
    ht.squeeze ht' (fun n => (hX (b n)).le) (fun n => by rw [hbsucc]; exact le_max_left _ _)
  have htY : Tendsto (fun n => Y (b n)) atTop (𝓝 γ) :=
    ht.squeeze ht' (fun n => (hY (b n)).le) (fun n => by rw [hbsucc]; exact le_max_right _ _)
  have hfc : ContinuousAt f γ := (hf γ hγ).continuousAt (isOpen_Iio.mem_nhds hγ)
  have hlimit : Tendsto (fun n => dist (f (X (b n))) (f (Y (b n)))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hfc.tendsto.comp htX).dist (hfc.tendsto.comp htY)
  have he : ε ≤ 0 := ge_of_tendsto hlimit (Eventually.of_forall (fun n => hdist (b n)))
  exact (not_le_of_gt hε) he

theorem exists_constant_ordinal_interior_tail {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (f : Ordinal.{u} → M)
    (hf : ContinuousOn f (Set.Iio α)) :
    ∃ β < α, ∀ x, β < x → x < α → ∀ y, β < y → y < α → f x = f y := by
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hrone : r < 1 := by norm_num [r]
  have h (n : ℕ) := exists_small_diameter_ordinal_tail hα f hf (pow_pos hr n)
  choose b hb hbound using h
  refine ⟨⨆ n, b n, Ordinal.iSup_lt_ord_lift (by simpa using hα) hb, ?_⟩
  intro x hx hxα y hy hyα
  have hd (n) : dist (f x) (f y) ≤ r ^ n :=
    (hbound n x ((Ordinal.le_iSup b n).trans_lt hx) hxα
      y ((Ordinal.le_iSup b n).trans_lt hy) hyα).le
  have hz : dist (f x) (f y) ≤ 0 := ge_of_tendsto
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hrone) (Eventually.of_forall hd)
  exact dist_eq_zero.mp (le_antisymm hz dist_nonneg)

end JLMS
