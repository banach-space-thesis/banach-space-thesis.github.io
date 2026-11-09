import SurveyStatements.P1GoldstineSequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! The double Goldstine triangular sequence. -/
noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
open Set Filter Topology

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

local instance : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
local instance : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
local instance : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance

def TriangularStepSpec (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X))) (n : ℕ)
    (u : ℕ → X) (v : ℕ → StrongDual ℂ X) (p : X × StrongDual ℂ X) : Prop :=
  ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 ∧ ‖ξ p.2 - ψ ξ‖ < 1 / ((n : ℝ) + 1) ∧
    (∀ k, k < n → ‖p.2 (u k)‖ < 1 / ((n : ℝ) + 1)) ∧
    (∀ k, k < n → ‖v k p.1 - ξ (v k)‖ < 1 / ((n : ℝ) + 1)) ∧
    ‖p.2 p.1 - ξ p.2‖ < 1 / ((n : ℝ) + 1)

theorem exists_triangular_step (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X)))
    (hξ : ‖ξ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    (hvanish : ∀ x : X, ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0)
    (n : ℕ) (u : ℕ → X) (v : ℕ → StrongDual ℂ X) :
    ∃ p : X × StrongDual ℂ X, TriangularStepSpec ξ ψ n u v p := by
  classical
  have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨f, hfnorm, hf⟩ := goldstine_finite_approximation ψ hψ
    (insert ξ ((Finset.range n).image (fun k => NormedSpace.inclusionInDoubleDual ℂ X (u k)))) hε
  obtain ⟨x, hxnorm, hx⟩ := goldstine_finite_approximation ξ hξ
    (insert f ((Finset.range n).image v)) hε
  refine ⟨(x, f), hxnorm, hfnorm, hf ξ (Finset.mem_insert_self _ _), ?_, ?_,
    hx f (Finset.mem_insert_self _ _)⟩
  · intro k hk
    have h := hf (NormedSpace.inclusionInDoubleDual ℂ X (u k))
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))
    simpa only [hvanish, sub_zero] using h
  · intro k hk
    exact hx (v k)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))

def triangularPairs (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X)))
    (hξ : ‖ξ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    (hvanish : ∀ x : X, ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0)
    (n : ℕ) : X × StrongDual ℂ X :=
  (exists_triangular_step ξ ψ hξ hψ hvanish n
    (fun k => if h : k < n then (triangularPairs ξ ψ hξ hψ hvanish k).1 else 0)
    (fun k => if h : k < n then (triangularPairs ξ ψ hξ hψ hvanish k).2 else 0)).choose
termination_by n

theorem triangularPairs_spec (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X)))
    (hξ : ‖ξ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    (hvanish : ∀ x : X, ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0)
    (n : ℕ) :
    TriangularStepSpec ξ ψ n
      (fun k => (triangularPairs ξ ψ hξ hψ hvanish k).1)
      (fun k => (triangularPairs ξ ψ hξ hψ hvanish k).2)
      (triangularPairs ξ ψ hξ hψ hvanish n) := by
  have h := (exists_triangular_step ξ ψ hξ hψ hvanish n
    (fun k => if h : k < n then (triangularPairs ξ ψ hξ hψ hvanish k).1 else 0)
    (fun k => if h : k < n then (triangularPairs ξ ψ hξ hψ hvanish k).2 else 0)).choose_spec
  rw [← triangularPairs] at h
  rcases h with ⟨hnormx, hnormf, herror, hlow, hupp, hdiag⟩
  refine ⟨hnormx, hnormf, herror, ?_, ?_, hdiag⟩
  · intro k hk
    simpa only [dif_pos hk] using hlow k hk
  · intro k hk
    simpa only [dif_pos hk] using hupp k hk

theorem exists_goldstine_triangular_sequence (ξ : StrongDual ℂ (StrongDual ℂ X))
    (ψ : StrongDual ℂ (StrongDual ℂ (StrongDual ℂ X)))
    (hξ : ‖ξ‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1)
    (hvanish : ∀ x : X, ψ (NormedSpace.inclusionInDoubleDual ℂ X x) = 0) :
    ∃ s : ℕ → X, ∃ f : ℕ → StrongDual ℂ X,
      (∀ n, ‖s n‖ ≤ 1) ∧ (∀ n, ‖f n‖ ≤ 1) ∧
      Tendsto (fun n => ξ (f n)) atTop (𝓝 (ψ ξ)) ∧
      (∀ k, Tendsto (fun n => f n (s k)) atTop (𝓝 0)) ∧
      (∀ k, Tendsto (fun n => f k (s n)) atTop (𝓝 (ξ (f k)))) := by
  let s : ℕ → X := fun n => (triangularPairs ξ ψ hξ hψ hvanish n).1
  let f : ℕ → StrongDual ℂ X := fun n => (triangularPairs ξ ψ hξ hψ hvanish n).2
  have hspec (n : ℕ) := triangularPairs_spec ξ ψ hξ hψ hvanish n
  refine ⟨s, f, fun n => (hspec n).1, fun n => (hspec n).2.1, ?_, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hspec n).2.2.1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro k
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [sub_zero] using ((hspec n).2.2.2.1 k (by omega)).le
  · intro k
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact ((hspec n).2.2.2.2.1 k (by omega)).le

end SurveyStatements.P1
