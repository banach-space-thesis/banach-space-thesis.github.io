import SurveyStatements.P5OperatorReductionReservoir
import Mathlib.Order.WellFounded
import Lean.Elab.Tactic.Omega

/-! Diagonal fusion of nested increasing reservoirs. Every earlier trace
limit survives, even though later stages refine the reservoir again. -/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace SurveyStatements.P5OperatorReduction

theorem reservoir_stage_refines_earlier (r s : ℕ → ℕ → ℕ)
    (hs : ∀ n, StrictMono (s n))
    (hstep : ∀ n, r (n + 1) = r n ∘ s n)
    (k n : ℕ) (hkn : k ≤ n) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ r n = r k ∘ t := by
  revert hkn
  induction n with
  | zero =>
      intro hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact ⟨id, strictMono_id, rfl⟩
  | succ n ih =>
      intro hk
      by_cases hkn : k ≤ n
      · obtain ⟨t, ht, heq⟩ := ih hkn
        refine ⟨t ∘ s n, ht.comp (hs n), ?_⟩
        rw [hstep n, heq] <;> rfl
      · have heq : k = n + 1 := by omega
        subst k
        exact ⟨id, strictMono_id, rfl⟩

theorem reservoir_diagonal_strictMono (r s : ℕ → ℕ → ℕ)
    (hr : ∀ n, StrictMono (r n)) (hs : ∀ n, StrictMono (s n))
    (hstep : ∀ n, r (n + 1) = r n ∘ s n) :
    StrictMono (fun n => r n n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [hstep n]
  exact (hr n) ((Nat.lt_succ_self n).trans_le ((hs n).id_le (n + 1)))

theorem reservoir_diagonal_tendsto_atTop (r s : ℕ → ℕ → ℕ)
    (hr : ∀ n, StrictMono (r n)) (hs : ∀ n, StrictMono (s n))
    (hstep : ∀ n, r (n + 1) = r n ∘ s n) :
    Tendsto (fun n => r n n) atTop atTop :=
  (reservoir_diagonal_strictMono r s hr hs hstep).tendsto_atTop

theorem reservoir_diagonal_preserves_limit {E : Type*} [TopologicalSpace E]
    (r s : ℕ → ℕ → ℕ) (hs : ∀ n, StrictMono (s n))
    (hstep : ∀ n, r (n + 1) = r n ∘ s n)
    (k : ℕ) (v : ℕ → E) (a : E)
    (hv : Tendsto (fun n => v (r k n)) atTop (𝓝 a)) :
    Tendsto (fun n => v (r n n)) atTop (𝓝 a) := by
  rw [tendsto_def]
  intro U hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hv.eventually hU)
  filter_upwards [eventually_ge_atTop (max k N)] with n hn
  obtain ⟨t, ht, heq⟩ := reservoir_stage_refines_earlier r s hs hstep k n
    ((le_max_left k N).trans hn)
  change v (r n n) ∈ U
  rw [heq]
  exact hN (t n) (((le_max_right k N).trans hn).trans (ht.id_le n))

theorem reservoir_diagonal_preserves_registered_traces {I : Type*}
    {E : I → Type*} [∀ i, TopologicalSpace (E i)]
    (r s : ℕ → ℕ → ℕ) (hs : ∀ n, StrictMono (s n))
    (hstep : ∀ n, r (n + 1) = r n ∘ s n)
    (stage : I → ℕ) (v : ℕ → (i : I) → E i) (a : (i : I) → E i)
    (hv : ∀ i, Tendsto (fun n => v (r (stage i) n) i) atTop (𝓝 (a i))) :
    ∀ i, Tendsto (fun n => v (r n n) i) atTop (𝓝 (a i)) :=
  fun i => reservoir_diagonal_preserves_limit r s hs hstep (stage i)
    (fun n => v n i) (a i) (hv i)

end SurveyStatements.P5OperatorReduction
