import ThesisCommon.Analysis.FiniteSeparation
import ThesisCommon.Analysis.SeparatedCuts
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.SetTheory.Cardinal.Continuum

/-! Counting uniformly separated cuts for bounded real-valued tests.
The bounds apply to finitely additive measures without countable additivity. -/
noncomputable section
open Set Cardinal
universe u
namespace ThesisCommon

theorem finite_test_separated_cuts_countable {D I : Type u} (ev : D → I → ℝ)
    (hbound : ∀ d i, |ev d i| ≤ 1) (F : Finset I) (M : Set D) :
    Set.Countable {A | A ⊆ M ∧ FinitelySeparated ev (↑F) A (M \ A)} := by
  classical
  let X := F → Set.Icc (-1 : ℝ) 1
  let f : D → X := fun d i => ⟨ev d i.val, abs_le.mp (hbound d i.val)⟩
  apply (metric_separated_cuts_countable f M).mono
  rintro A ⟨hAM, ε, hε, G, hGF, hgap⟩
  refine ⟨hAM, ε, hε, ?_⟩
  intro x hx y hy
  obtain ⟨i, hiG, hi⟩ := hgap x hx y hy
  have hiF : i ∈ F := hGF hiG
  have hdist := dist_le_pi_dist (f x) (f y) (⟨i, hiF⟩ : F)
  exact hi.trans (by simpa only [Subtype.dist_eq, Real.dist_eq] using hdist)

theorem separated_cuts_cardinal_le {D I : Type u} (ev : D → I → ℝ)
    (hbound : ∀ d i, |ev d i| ≤ 1) (M : Set D) :
    #{A : Set D // A ⊆ M ∧ FinitelySeparated ev Set.univ A (M \ A)} ≤ max #I ℵ₀ := by
  classical
  let cuts : Finset I → Set (Set D) := fun F =>
    {A | A ⊆ M ∧ FinitelySeparated ev (↑F) A (M \ A)}
  have hcount (F : Finset I) : (cuts F).Countable :=
    finite_test_separated_cuts_countable ev hbound F M
  have hcover : {A | A ⊆ M ∧ FinitelySeparated ev Set.univ A (M \ A)} ⊆ ⋃ F, cuts F := by
    rintro A ⟨hAM, ε, hε, F, _, hgap⟩
    exact Set.mem_iUnion.mpr ⟨F, hAM, ε, hε, F, Set.Subset.rfl, hgap⟩
  have hfinset : #(Finset I) ≤ max #I ℵ₀ := by
    calc
      #(Finset I) ≤ #(List I) := Cardinal.mk_le_of_surjective List.toFinset_surjective
      _ ≤ max #I ℵ₀ := by simpa only [max_comm] using Cardinal.mk_list_le_max I
  calc
    _ ≤ #(⋃ F, cuts F) := Cardinal.mk_le_mk_of_subset hcover
    _ ≤ Cardinal.sum (fun F => #(cuts F)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : Finset I => ℵ₀) := Cardinal.sum_le_sum _ _ (fun F => by
      haveI : Countable (cuts F) := (hcount F).to_subtype
      exact Cardinal.mk_le_aleph0)
    _ = #(Finset I) * ℵ₀ := by simpa using Cardinal.sum_const (Finset I) ℵ₀
    _ ≤ max #I ℵ₀ * max #I ℵ₀ := mul_le_mul' hfinset (le_max_right _ _)
    _ = max #I ℵ₀ := Cardinal.mul_eq_self (le_max_right _ _)

/-- The strict continuum bound of Sigma Lemma 4.3, with the two algebras
combined into one disjoint type of bounded tests. -/
theorem separated_cuts_lt_continuum {D I : Type u} (ev : D → I → ℝ)
    (hbound : ∀ d i, |ev d i| ≤ 1) (M : Set D) (hI : #I < 𝔠) :
    #{A : Set D // A ⊆ M ∧ FinitelySeparated ev Set.univ A (M \ A)} < 𝔠 :=
  (separated_cuts_cardinal_le ev hbound M).trans_lt
    (max_lt hI Cardinal.aleph0_lt_continuum)

end ThesisCommon
