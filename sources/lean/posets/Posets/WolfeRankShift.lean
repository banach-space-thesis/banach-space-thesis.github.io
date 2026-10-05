import Posets.WolfeMonotonicity

/-! The rank-shift estimate stated after Alspach's Lemma 3.2: projection of
P_(γ+η) is contained in the η-th derived set of the projection of P_γ. No
closedness of that projection and no distinctness of the initial children are
assumed. -/

noncomputable section
open Set Filter Topology Order ThesisCommon
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

def wolfeMeasures (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)) := Prod.fst '' wolfeFamily M ε B α

theorem wolfeFamily_add_subset_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (γ η : Ordinal.{u}) (hc : (γ + η).card ≤ Cardinal.aleph0) :
    ∀ p ∈ wolfeFamily M ε B (γ + η),
      p.1 ∈ ordinalDerived (wolfeMeasures M ε B γ) η := by
  induction η using Ordinal.limitRecOn with
  | zero =>
      intro p hp
      rw [add_zero] at hp
      simpa only [ordinalDerived_zero] using
        (show p.1 ∈ wolfeMeasures M ε B γ from ⟨p, hp, rfl⟩)
  | succ η ih =>
      intro p hp
      rw [Ordinal.add_succ] at hp
      obtain ⟨_, c, hchild, hconv, hdisj, _⟩ :=
        (mem_wolfeFamily_succ M ε B (γ + η) p).mp hp
      have hc' : (γ + η).card ≤ Cardinal.aleph0 :=
        (Ordinal.card_le_card (by rw [Ordinal.add_succ]; exact le_succ _)).trans hc
      rw [ordinalDerived_succ]
      exact wolfeSequence_mem_derivedSet M (fun n => (c n).1) (fun n => (c n).2)
        hdisj hε (fun n => (wolfeFamily_subset_base M ε B (γ + η) (hchild n)).2.2)
        hconv (fun n => ih hc' (c n) (hchild n))
  | limit η hη ih =>
      intro p hp
      rw [ordinalDerived_limit _ hη]
      apply mem_iInter₂.mpr
      intro β hβ
      have hle : γ + β ≤ γ + η := add_le_add_left hβ.le γ
      exact ih β hβ ((Ordinal.card_le_card hle).trans hc) p
        (wolfeFamily_antitone_on_countable M ε B hc hle hp)

theorem wolfeMeasures_add_subset_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (γ η : Ordinal.{u}) (hc : (γ + η).card ≤ Cardinal.aleph0) :
    wolfeMeasures M ε B (γ + η) ⊆ ordinalDerived (wolfeMeasures M ε B γ) η := by
  rintro μ ⟨p, hp, rfl⟩
  exact wolfeFamily_add_subset_ordinalDerived M hε B γ η hc p hp

theorem wolfeFamily_empty_of_shifted_derived_empty (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K)))
    (γ η : Ordinal.{u}) (hc : (γ + η).card ≤ Cardinal.aleph0)
    (he : ordinalDerived (wolfeMeasures M ε B γ) η = ∅) :
    wolfeFamily M ε B (γ + η) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := wolfeFamily_add_subset_ordinalDerived M hε B γ η hc p hp
  simp only [he, mem_empty_iff_false] at h

end Posets
