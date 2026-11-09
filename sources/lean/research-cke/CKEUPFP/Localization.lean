import CKEUPFP.LocalDefect
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The countable-base localization argument

The first theorem isolates the covering argument in Proposition 3.5. The
local-smallness and measurability inputs remain explicit: they must be proved
for the actual diagonal field before this result proves the paper's proposition.
-/

noncomputable section

namespace CKEUPFP

variable {K : Type*} [TopologicalSpace K] [SecondCountableTopology K] [Uncountable K]

/-- A monotone local quantity that becomes small around every point is small
on an uncountable set for at least one member of a countable base. -/
theorem exists_basis_uncountable_small
    (ρ : Set K → K → ℝ) (η : ℝ)
    (hmono : ∀ {O U : Set K}, O ⊆ U → ∀ t, ρ O t ≤ ρ U t)
    (hsmall : ∀ t : K, ∃ U : Set K, IsOpen U ∧ t ∈ U ∧ ρ U t < η) :
    ∃ O ∈ TopologicalSpace.countableBasis K,
      ¬ ({t : K | t ∈ O ∧ ρ O t < η} : Set K).Countable := by
  classical
  by_contra h
  have hc : ∀ O : TopologicalSpace.countableBasis K,
      ({t : K | t ∈ (O : Set K) ∧ ρ O t < η} : Set K).Countable := by
    intro O
    by_contra hO
    exact h ⟨O, O.property, hO⟩
  have hcover : (Set.univ : Set K) ⊆
      ⋃ O : TopologicalSpace.countableBasis K, {t : K | t ∈ (O : Set K) ∧ ρ O t < η} := by
    intro t _
    obtain ⟨U, hU, htU, hρ⟩ := hsmall t
    obtain ⟨O, hO, htO, hOU⟩ :=
      (TopologicalSpace.isBasis_countableBasis K).exists_subset_of_mem_open htU hU
    exact Set.mem_iUnion.mpr ⟨⟨O, hO⟩, htO, (hmono hOU t).trans_lt hρ⟩
  exact Set.not_countable_univ ((Set.countable_iUnion hc).mono hcover)

/-- The measurable version of the same localization argument. -/
theorem exists_open_uncountable_borel_small [MeasurableSpace K] [BorelSpace K]
    (ρ : Set K → K → ℝ) (η : ℝ)
    (hmono : ∀ {O U : Set K}, O ⊆ U → ∀ t, ρ O t ≤ ρ U t)
    (hsmall : ∀ t : K, ∃ U : Set K, IsOpen U ∧ t ∈ U ∧ ρ U t < η)
    (hmeas : ∀ O : Set K, IsOpen O → Measurable (ρ O)) :
    ∃ O : Set K, IsOpen O ∧
      MeasurableSet {t : K | t ∈ O ∧ ρ O t < η} ∧
      ¬ ({t : K | t ∈ O ∧ ρ O t < η} : Set K).Countable := by
  obtain ⟨O, hO, hunc⟩ := exists_basis_uncountable_small ρ η hmono hsmall
  have hopen := TopologicalSpace.isOpen_of_mem_countableBasis hO
  exact ⟨O, hopen, hopen.measurableSet.inter
    (measurableSet_lt (hmeas O hopen) measurable_const), hunc⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompactSpace K]

/-- Apply localization once local smallness and Borelness have been proved for
the supplied field. This theorem does not postulate an atom field. -/
theorem localDefect_localization_of_local_smallness [MeasurableSpace K] [BorelSpace K]
    (T : C(K, E) →L[𝕜] C(K, E)) (A : K → E →L[𝕜] E) (η : ℝ)
    (hsmall : ∀ t : K, ∃ U : Set K,
      IsOpen U ∧ t ∈ U ∧ localDefect T A U t < η)
    (hmeas : ∀ O : Set K, IsOpen O → Measurable (localDefect T A O)) :
    ∃ O : Set K, IsOpen O ∧
      MeasurableSet {t : K | t ∈ O ∧ localDefect T A O t < η} ∧
      ¬ ({t : K | t ∈ O ∧ localDefect T A O t < η} : Set K).Countable :=
  exists_open_uncountable_borel_small (localDefect T A) η
    (fun h t => localDefect_mono T A h t) hsmall hmeas

end CKEUPFP
