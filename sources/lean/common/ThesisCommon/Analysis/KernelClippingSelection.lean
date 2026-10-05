import ThesisCommon.Analysis.KernelClipping
import Mathlib.Topology.Order.IntermediateValue

/-! A measurable clipping-level selector for continuous decreasing tails.
The zero-budget case is handled separately by leaving the kernel unchanged. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThesisCommon

/-- The first nonnegative level at which a tail is within its positive budget. -/
def continuousTailLevel (R : ℝ → ℝ) (d : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ R t ≤ d}

theorem continuousTailLevel_set_nonempty {R : ℝ → ℝ} {d : ℝ}
    (hlim : Tendsto R atTop (𝓝 0)) (hd : 0 < d) :
    {t : ℝ | 0 ≤ t ∧ R t ≤ d}.Nonempty := by
  have he : ∀ᶠ t in atTop, R t < d := hlim.eventually (gt_mem_nhds hd)
  obtain ⟨t, ht, hRt⟩ := ((eventually_ge_atTop (0 : ℝ)).and he).exists
  exact ⟨t, ht, hRt.le⟩

theorem continuousTailLevel_mem {R : ℝ → ℝ} {d : ℝ}
    (hc : Continuous R) (hlim : Tendsto R atTop (𝓝 0)) (hd : 0 < d) :
    0 ≤ continuousTailLevel R d ∧ R (continuousTailLevel R d) ≤ d := by
  exact ((isClosed_le continuous_const continuous_id).inter
    (isClosed_le hc continuous_const)).csInf_mem
      (continuousTailLevel_set_nonempty hlim hd) ⟨0, fun t ht => ht.1⟩

theorem continuousTailLevel_le {R : ℝ → ℝ} {d t : ℝ}
    (ht : 0 ≤ t) (hRt : R t ≤ d) : continuousTailLevel R d ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, hRt⟩

theorem continuousTailLevel_eq_zero {R : ℝ → ℝ} {d : ℝ}
    (hc : Continuous R) (hlim : Tendsto R atTop (𝓝 0)) (hd : 0 < d) (hR : R 0 ≤ d) :
    continuousTailLevel R d = 0 :=
  le_antisymm (continuousTailLevel_le le_rfl hR) (continuousTailLevel_mem hc hlim hd).1

/-- A positive budget is attained exactly unless it already exceeds the whole mass. -/
theorem continuousTailLevel_value {R : ℝ → ℝ} {d : ℝ}
    (hc : Continuous R) (hlim : Tendsto R atTop (𝓝 0)) (hd : 0 < d) :
    R (continuousTailLevel R d) = min (R 0) d := by
  by_cases hR : R 0 ≤ d
  · rw [continuousTailLevel_eq_zero hc hlim hd hR, min_eq_left hR]
  · rw [min_eq_right (le_of_not_ge hR)]
    have hm := continuousTailLevel_mem hc hlim hd
    apply le_antisymm hm.2
    by_contra! hlt
    obtain ⟨t, ht, htd⟩ := intermediate_value_Icc' hm.1 hc.continuousOn
      ⟨hlt.le, le_of_not_ge hR⟩
    have hlevel : continuousTailLevel R d ≤ t := continuousTailLevel_le ht.1 htd.le
    have hteq : t = continuousTailLevel R d := le_antisymm ht.2 hlevel
    rw [hteq] at htd
    exact hlt.ne htd

theorem continuousTailLevel_lt_iff {R : ℝ → ℝ} {d a : ℝ}
    (hc : Continuous R) (ha : Antitone R) (hlim : Tendsto R atTop (𝓝 0)) (hd : 0 < d) :
    continuousTailLevel R d < a ↔
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < a ∧ R q ≤ d := by
  constructor
  · intro hlt
    obtain ⟨q, hlq, hqa⟩ := exists_rat_btwn hlt
    have hm := continuousTailLevel_mem hc hlim hd
    exact ⟨q, hm.1.trans hlq.le, hqa, (ha hlq.le).trans hm.2⟩
  · rintro ⟨q, hq, hqa, hRq⟩
    exact (continuousTailLevel_le hq hRq).trans_lt hqa

/-- Rational sublevel tests make the selected real level measurable; the
parameter space has no separability or countable-generation hypothesis. -/
theorem measurable_continuousTailLevel {X : Type*} [MeasurableSpace X]
    {R : X → ℝ → ℝ} {d : X → ℝ}
    (hm : ∀ q : ℚ, Measurable (fun x => R x q)) (hdm : Measurable d)
    (hc : ∀ x, Continuous (R x)) (ha : ∀ x, Antitone (R x))
    (hlim : ∀ x, Tendsto (R x) atTop (𝓝 0)) (hd : ∀ x, 0 < d x) :
    Measurable (fun x => continuousTailLevel (R x) (d x)) := by
  apply measurable_of_Iio
  intro a
  have heq : (fun x => continuousTailLevel (R x) (d x)) ⁻¹' Iio a =
      ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ)), ⋃ (_ : (q : ℝ) < a), {x | R x q ≤ d x} := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_setOf_eq, exists_prop]
    exact continuousTailLevel_lt_iff (hc x) (ha x) (hlim x) (hd x)
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => measurableSet_le (hm q) hdm

end ThesisCommon
