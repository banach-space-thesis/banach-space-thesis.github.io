import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic

/-! The concrete index for repeating a sequence over successive intervals
with strictly increasing endpoints. -/
noncomputable section
open Filter
namespace ThesisCommon

def jamesStepIndex (σ : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun j => σ j ≤ n) n

theorem jamesStepIndex_monotone (σ : ℕ → ℕ) : Monotone (jamesStepIndex σ) := by
  intro n m hnm
  exact Nat.findGreatest_mono (fun _ h => h.trans hnm) hnm

@[simp] theorem jamesStepIndex_at_endpoint (σ : ℕ → ℕ) (hσ : StrictMono σ) (n : ℕ) :
    jamesStepIndex σ (σ n) = n := by
  apply Nat.findGreatest_eq_iff.mpr
  exact ⟨hσ.id_le n, fun _ => le_rfl, fun _ h _ => not_le_of_gt (hσ h)⟩

theorem jamesStepIndex_tendsto (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    Tendsto (jamesStepIndex σ) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (σ N)] with n hn
  exact Nat.le_findGreatest ((hσ.id_le N).trans hn) hn

theorem jamesStepIndex_eq_of_interval (σ : ℕ → ℕ) (hσ : StrictMono σ)
    {m n : ℕ} (hl : σ m ≤ n) (hr : n < σ (m + 1)) : jamesStepIndex σ n = m := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨(hσ.id_le m).trans hl, fun _ => hl, ?_⟩
  intro k hk _ hkn
  exact (not_lt_of_ge ((hσ.monotone (by omega)).trans hkn)) hr

end ThesisCommon
