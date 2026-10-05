import ThesisCommon.Analysis.IntervalL1SubtypeEquiv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! A continuum of pairwise singular probability measures on the interval,
each with its genuine L1 space isometric to Lebesgue L1. The construction
uses the Borel isomorphism theorem on the square and its vertical fibres. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal unitInterval

namespace ThesisCommon.IntervalDisjointLebesgue

theorem not_countable_interval : ¬ Countable unitInterval := by
  intro h
  have hc : (Icc (0 : ℝ) 1).Countable := Set.to_countable _
  have := Cardinal.Real.Icc_countable_iff.mp hc
  norm_num at this

theorem not_countable_square : ¬ Countable (unitInterval × unitInterval) := by
  intro h
  letI := h
  exact not_countable_interval
    (Function.Injective.countable (f := fun x : unitInterval => (x, (0 : unitInterval)))
      (fun _ _ h => congrArg Prod.fst h))

/-- A fixed actual Borel coding of the square into the interval. -/
def squareEquiv : (unitInterval × unitInterval) ≃ᵐ unitInterval :=
  PolishSpace.measurableEquivOfNotCountable not_countable_square not_countable_interval

def fibre (t : unitInterval) (s : unitInterval) : unitInterval := squareEquiv (t, s)

theorem measurable_fibre (t : unitInterval) : Measurable (fibre t) :=
  squareEquiv.measurable.comp (measurable_const.prodMk measurable_id)

def read : unitInterval → unitInterval := fun x => (squareEquiv.symm x).2

theorem measurable_read : Measurable read := measurable_snd.comp squareEquiv.symm.measurable

@[simp] theorem read_fibre (t s : unitInterval) : read (fibre t s) = s := by
  simp [read, fibre]

def carrier (t : unitInterval) : Set unitInterval := {x | (squareEquiv.symm x).1 = t}

theorem measurableSet_carrier (t : unitInterval) : MeasurableSet (carrier t) :=
  (measurable_fst.comp squareEquiv.symm.measurable) (measurableSet_singleton t)

@[simp] theorem fibre_mem_carrier (t s : unitInterval) : fibre t s ∈ carrier t := by
  simp [fibre, carrier]

theorem carrier_disjoint {s t : unitInterval} (h : s ≠ t) :
    Disjoint (carrier s) (carrier t) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h (hx.symm.trans hy)

/-- The pushforward of Lebesgue probability on a single vertical fibre. -/
def measure (t : unitInterval) : Measure unitInterval := volume.map (fibre t)

instance measure_isProbability (t : unitInterval) : IsProbabilityMeasure (measure t) := by
  unfold measure
  exact Measure.isProbabilityMeasure_map (measurable_fibre t).aemeasurable

theorem measurePreserving_fibre (t : unitInterval) :
    MeasurePreserving (fibre t) volume (measure t) := ⟨measurable_fibre t, rfl⟩

theorem measurePreserving_read (t : unitInterval) :
    MeasurePreserving read (measure t) volume where
  measurable := measurable_read
  map_eq := by
    rw [measure, Measure.map_map measurable_read (measurable_fibre t)]
    have h : read ∘ fibre t = id := funext (read_fibre t)
    rw [h, Measure.map_id]

theorem measure_carrier_compl (t : unitInterval) : measure t (carrier t)ᶜ = 0 := by
  rw [measure, Measure.map_apply (measurable_fibre t) (measurableSet_carrier t).compl]
  have h : fibre t ⁻¹' (carrier t)ᶜ = ∅ := by ext s; simp
  rw [h, measure_empty]

theorem mutuallySingular {s t : unitInterval} (h : s ≠ t) :
    (measure s).MutuallySingular (measure t) := by
  refine ⟨(carrier s)ᶜ, (measurableSet_carrier s).compl,
    measure_carrier_compl s, ?_⟩
  rw [compl_compl]
  exact measure_mono_null (Set.disjoint_left.mp (carrier_disjoint h))
    (measure_carrier_compl t)

variable (𝕜 : Type*) [RCLike 𝕜]

def pullback (t : unitInterval) :
    Lp 𝕜 1 (measure t) →ₗᵢ[𝕜] Lp 𝕜 1 (volume : Measure unitInterval) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (fibre t) (measurePreserving_fibre t)

def extension (t : unitInterval) :
    Lp 𝕜 1 (volume : Measure unitInterval) →ₗᵢ[𝕜] Lp 𝕜 1 (measure t) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 read (measurePreserving_read t)

theorem pullback_extension (t : unitInterval) (f : Lp 𝕜 1 (volume : Measure unitInterval)) :
    pullback 𝕜 t (extension 𝕜 t f) = f := by
  apply Lp.ext
  have he := (measurePreserving_fibre t).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving f (measurePreserving_read t))
  filter_upwards [Lp.coeFn_compMeasurePreserving (extension 𝕜 t f)
    (measurePreserving_fibre t), he] with x hx hxe
  change pullback 𝕜 t (extension 𝕜 t f) x = _ at hx ⊢
  rw [hx]
  change extension 𝕜 t f (fibre t x) = f x
  simpa only [Function.comp_apply, read_fibre] using hxe

/-- The fibre measure has exactly the usual scalar Lebesgue L1 space. -/
def l1Equiv (t : unitInterval) :
    Lp 𝕜 1 (measure t) ≃ₗᵢ[𝕜] IntervalLp 𝕜 ⟨1, le_rfl⟩ :=
  (LinearIsometryEquiv.ofSurjective (pullback 𝕜 t)
    (fun f => ⟨extension 𝕜 t f, pullback_extension 𝕜 t f⟩)).trans
      (IntervalL1Subtype.equiv 𝕜)

end ThesisCommon.IntervalDisjointLebesgue
