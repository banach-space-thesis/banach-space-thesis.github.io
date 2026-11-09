import SurveyStatements.P1BasicSequences
import SurveyStatements.P1PhaseCompactness
import Mathlib.Topology.Sequences

/-!
The compactness passage from finite-length phased block choices to infinitely
many choices with the same partial-sum bound.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Finite families of possible blocks and the compact phase circle allow the
source's diagonal passage. Values at levels beyond the finite construction
can be filled with arbitrary admissible choices before applying this lemma. -/
theorem finiteFamily_phase_compactness (D : ℕ → Finset X)
    (v : ℕ → ℕ → X) (a : ℕ → ℕ → ℂ)
    (hv : ∀ L j, v L j ∈ D j) (ha : ∀ L j, a L j ∈ unitScalars)
    {C : ℝ}
    (hbound : ∀ L N, N ≤ L → ‖sequencePartialSum (v L) (a L) N‖ ≤ C) :
    ∃ d : ℕ → X, ∃ α : ℕ → ℂ,
      (∀ j, d j ∈ D j) ∧ (∀ j, α j ∈ unitScalars) ∧
      ∀ N, ‖sequencePartialSum d α N‖ ≤ C := by
  let S : Set (ℕ → X × ℂ) := {z | ∀ j, z j ∈ (D j : Set X) ×ˢ unitScalars}
  have hS : IsCompact S := isCompact_pi_infinite (fun j =>
    (D j).finite_toSet.isCompact.prod isCompact_unitScalars)
  let z : ℕ → ℕ → X × ℂ := fun L j => (v L j, a L j)
  have hz : ∀ L, z L ∈ S := fun L j => ⟨hv L j, ha L j⟩
  obtain ⟨b, hb, φ, hφ, hlim⟩ := hS.tendsto_subseq hz
  refine ⟨fun j => (b j).1, fun j => (b j).2,
    fun j => (hb j).1, fun j => (hb j).2, ?_⟩
  intro N
  have hvec (j : ℕ) : Tendsto (fun k => v (φ k) j) atTop (𝓝 (b j).1) := by
    have hj := ((continuous_apply j).tendsto b).comp hlim
    exact (continuous_fst.tendsto (b j)).comp hj
  have hphase (j : ℕ) : Tendsto (fun k => a (φ k) j) atTop (𝓝 (b j).2) := by
    have hj := ((continuous_apply j).tendsto b).comp hlim
    exact (continuous_snd.tendsto (b j)).comp hj
  have hpartial : Tendsto (fun k => sequencePartialSum (v (φ k)) (a (φ k)) N)
      atTop (𝓝 (sequencePartialSum (fun j => (b j).1) (fun j => (b j).2) N)) := by
    exact tendsto_finset_sum _ fun j _ => (hphase j).smul (hvec j)
  have hevent : ∀ᶠ k : ℕ in atTop,
      ‖sequencePartialSum (v (φ k)) (a (φ k)) N‖ ≤ C := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
    exact hbound (φ k) N hk
  exact le_of_tendsto hpartial.norm hevent

end SurveyStatements.P1
