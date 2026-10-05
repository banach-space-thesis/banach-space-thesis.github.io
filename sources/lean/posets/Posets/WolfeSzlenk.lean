import Posets.WolfeMassBounds
import Posets.WolfeMonotonicity
import Posets.SzlenkOperator

/-! Wolfe witnesses supply actual norm-separated weak-star children.
Consequently each countable Wolfe level is contained in a Szlenk iterate at
every strictly smaller positive scale. This is a comparison of two genuine
derivations, not an operator-preservation converse. -/

noncomputable section
open Set Filter Topology Order
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (M : JLMS.AtomicDualModel 𝕜 K)
local instance wolfeSzlenkDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfeSzlenkDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem wolfeMass_le_norm_sub_add
    (μ ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : Set K) :
    wolfeMass M μ U ≤ ‖WeakDual.toStrongDual μ - WeakDual.toStrongDual ν‖ +
      wolfeMass M ν U := by
  calc
    wolfeMass M μ U = wolfeMass M ((μ - ν) + ν) U := by rw [sub_add_cancel]
    _ ≤ wolfeMass M (μ - ν) U + wolfeMass M ν U := wolfeMass_add_le M _ _ U
    _ ≤ _ := add_le_add_right (wolfeMass_le_norm M (μ - ν) U) _

theorem wolfeSequence_eventually_norm_separated
    (μ : ℕ → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ℕ → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) {ε δ : ℝ} (hδε : δ < ε)
    (hmass : ∀ n, ε ≤ wolfeMass M (μ n) (U n))
    (ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) :
    ∀ᶠ n in atTop, δ < ‖WeakDual.toStrongDual (μ n) - WeakDual.toStrongDual ν‖ := by
  have hfin := wolfeMass_positive_indices_finite M ν U hU (sub_pos.mpr hδε)
  have hev : ∀ᶠ n in atTop, wolfeMass M ν (U n) < ε - δ := by
    simpa only [Nat.cofinite_eq_atTop, mem_setOf_eq, not_le] using hfin.eventually_cofinite_notMem
  filter_upwards [hev] with n hn
  have hbound := wolfeMass_le_norm_sub_add M (μ n) ν (U n)
  have hm := hmass n
  linarith

theorem wolfeSequence_mem_szlenkDeriv
    (μ : ℕ → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ℕ → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) {ε δ : ℝ} (hδε : δ < ε)
    (hmass : ∀ n, ε ≤ wolfeMass M (μ n) (U n))
    {ν : WeakDual 𝕜 (JLMS.CZero 𝕜 K)} (hconv : Tendsto μ atTop (𝓝 ν))
    {B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))} (hν : ν ∈ B) (hB : ∀ n, μ n ∈ B) :
    ν ∈ szlenkDeriv δ B := by
  refine ⟨hν, ?_⟩
  intro V hV hνV
  have hmem : ∀ᶠ n in atTop, μ n ∈ V := hconv (hV.mem_nhds hνV)
  have hev := hmem.and (wolfeSequence_eventually_norm_separated M μ U hU hδε hmass ν)
  obtain ⟨n, hnV, hn⟩ := hev.exists
  exact ⟨μ n, ⟨hB n, hnV⟩, ν, ⟨hν, hνV⟩, hn⟩

theorem wolfeFamily_subset_szlenkIterate {ε δ : ℝ} (hδε : δ < ε)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal)
    (hc : α.card ≤ Cardinal.aleph0) :
    ∀ p ∈ wolfeFamily M ε B α, p.1 ∈ szlenkIterate δ B α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p hp
      simpa only [szlenkIterate_zero] using (wolfeFamily_subset_base M ε B 0 hp).1
  | succ α ih =>
      intro p hp
      have hαc : α.card ≤ Cardinal.aleph0 := (Ordinal.card_le_card (le_succ α)).trans hc
      have hpre : p ∈ wolfeFamily M ε B α :=
        wolfeFamily_antitone_on_countable M ε B hc (le_succ α) hp
      obtain ⟨_, c, hc', hch⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
      rw [szlenkIterate_succ]
      exact wolfeSequence_mem_szlenkDeriv M (fun n => (c n).1) (fun n => (c n).2)
        hch.2.1 hδε (fun n => (wolfeFamily_subset_base M ε B α (hc' n)).2.2)
        hch.1 (ih hαc p hpre) (fun n => ih hαc (c n) (hc' n))
  | limit α hα ih =>
      intro p hp
      rw [szlenkIterate_limit δ B α hα]
      apply mem_iInter.mpr
      intro β
      exact ih β.val β.property ((Ordinal.card_le_card β.property.le).trans hc) p
        (wolfeFamily_antitone_on_countable M ε B hc β.property.le hp)

theorem wolfeFamily_empty_of_szlenkIterate_empty {ε δ : ℝ} (hδε : δ < ε)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal)
    (hc : α.card ≤ Cardinal.aleph0) (h : szlenkIterate δ B α = ∅) :
    wolfeFamily M ε B α = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have := wolfeFamily_subset_szlenkIterate M hδε B α hc p hp
  simp only [h, mem_empty_iff_false] at this

end Posets
