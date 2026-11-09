import SurveyStatements.P5Support.HaarCountableTraceCluster
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! Restricting an infinite reservoir to one fixed finite choice and
preserving every trace limit registered before that restriction. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P5OperatorReduction

theorem finite_choice_frequently {Ω : Type*} [Finite Ω]
    (r : ℕ → ℕ) (good : Ω → ℕ → Prop)
    (hgood : ∀ᶠ n in atTop, ∃ θ, good θ (r n)) :
    ∃ θ, ∃ᶠ n in atTop, good θ (r n) := by
  classical
  by_contra hnot
  have hnone (θ : Ω) : ∀ᶠ n in atTop, ¬ good θ (r n) :=
    not_frequently.mp (fun hθ => hnot ⟨θ, hθ⟩)
  have hall : ∀ᶠ n in atTop, ∀ θ, ¬ good θ (r n) := eventually_all.mpr hnone
  obtain ⟨n, hn, hno⟩ := (hgood.and hall).exists
  obtain ⟨θ, hθ⟩ := hn
  exact hno θ hθ

theorem exists_fixed_good_reservoir {Ω : Type*} [Finite Ω]
    (r : ℕ → ℕ) (hr : StrictMono r) (good : Ω → ℕ → Prop)
    (hgood : ∀ᶠ n in atTop, ∃ θ, good θ (r n)) :
    ∃ θ, ∃ s : ℕ → ℕ, StrictMono s ∧
      StrictMono (r ∘ s) ∧ Tendsto s atTop atTop ∧
      Tendsto (r ∘ s) atTop atTop ∧ ∀ n, good θ (r (s n)) := by
  obtain ⟨θ, hθ⟩ := finite_choice_frequently r good hgood
  obtain ⟨s, hs, hsgood⟩ := extraction_of_frequently_atTop hθ
  exact ⟨θ, s, hs, hr.comp hs, hs.tendsto_atTop,
    (hr.comp hs).tendsto_atTop, hsgood⟩

theorem reservoir_preserves_registered_trace_limits {I : Type*}
    {E : I → Type*} [∀ i, TopologicalSpace (E i)]
    (r s : ℕ → ℕ) (hs : StrictMono s)
    (v : ℕ → (i : I) → E i) (a : (i : I) → E i)
    (htrace : ∀ i, Tendsto (fun n => v (r n) i) atTop (𝓝 (a i))) :
    ∀ i, Tendsto (fun n => v (r (s n)) i) atTop (𝓝 (a i)) :=
  fun i => (htrace i).comp hs.tendsto_atTop

theorem reservoir_extract_countable_bounded_traces {𝕜 I : Type*}
    [RCLike 𝕜] [Countable I] (r : ℕ → ℕ) (hr : StrictMono r)
    (v : ℕ → I → 𝕜) {M : ℝ} (hv : ∀ n i, ‖v (r n) i‖ ≤ M) :
    ∃ a : I → 𝕜, ∃ s : ℕ → ℕ, StrictMono s ∧
      StrictMono (r ∘ s) ∧ (∀ i, ‖a i‖ ≤ M) ∧
      ∀ i, Tendsto (fun n => v (r (s n)) i) atTop (𝓝 (a i)) := by
  obtain ⟨a, s, hs, ha, htrace⟩ :=
    SurveyStatements.P5Support.haar_countable_trace_cluster (fun n i => v (r n) i) hv
  exact ⟨a, s, hs, hr.comp hs, ha, htrace⟩

end SurveyStatements.P5OperatorReduction
