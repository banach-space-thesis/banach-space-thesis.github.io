import ThesisCommon.Analysis.CountableMetricClopen
import ThesisCommon.Analysis.OrdinalBakerLocality

/-! Splitting off one point of a finite Cantor--Bendixson derivative by a
clopen neighborhood. Iterating this operation reduces the finite terminal
derivative to singleton terminal derivatives. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon
variable {K : Type u} [MetricSpace K] [Countable K]

theorem countableMetric_clopen_isolates_finite {D : Set K} (hD : D.Finite)
    {p : K} (hp : p ∈ D) :
    ∃ U : Set K, IsClopen U ∧ p ∈ U ∧ D ∩ U = {p} := by
  have hf : (D \ {p}).Finite := hD.diff
  have ho : IsOpen (D \ {p})ᶜ := hf.isClosed.isOpen_compl
  have hn : p ∈ (D \ {p})ᶜ := by simp
  obtain ⟨U, hU, hpU, hUD⟩ := countableMetric_exists_clopen_nhds p (ho.mem_nhds hn)
  refine ⟨U, hU, hpU, ?_⟩
  ext x
  constructor
  · rintro ⟨hxD, hxU⟩
    change x = p
    by_contra hxp
    exact hUD hxU ⟨hxD, hxp⟩
  · rintro rfl
    exact ⟨hp, hpU⟩

/-- A finite nonempty derivative can be split into a singleton and the
remaining points by clopen subsets of the original compact space. -/
theorem countableCompact_terminal_clopen_split {A : Set K} {α : Ordinal.{u}}
    (hfin : (ordinalDerived A α).Finite) {p : K} (hp : p ∈ ordinalDerived A α) :
    ∃ U : Set K, IsClopen U ∧ p ∈ U ∧
      ordinalDerived (A ∩ U) α = {p} ∧
      ordinalDerived (A \ U) α = ordinalDerived A α \ {p} := by
  obtain ⟨U, hU, hpU, hDU⟩ := countableMetric_clopen_isolates_finite hfin hp
  refine ⟨U, hU, hpU, ?_, ?_⟩
  · rw [ordinalDerived_inter_clopen A hU, hDU]
  · rw [show A \ U = A ∩ Uᶜ from rfl, ordinalDerived_inter_clopen A hU.compl]
    ext x
    constructor
    · rintro ⟨hxD, hxU⟩
      refine ⟨hxD, ?_⟩
      rintro rfl
      exact hxU hpU
    · rintro ⟨hxD, hxp⟩
      refine ⟨hxD, ?_⟩
      intro hxU
      exact hxp (hDU ▸ (show x ∈ ordinalDerived A α ∩ U from ⟨hxD, hxU⟩))

end ThesisCommon
