import ThesisCommon.Analysis.CountableCompactShellGluing
import ThesisCommon.Analysis.CountableCompactFiniteModels
import ThesisCommon.Analysis.CountableCompactSubtypeRanks
import ThesisCommon.Analysis.CountableCompactTerminalSplit

/-! The countable compact metric ordinal classification. Transfinite
induction handles the singleton terminal derivative through clopen shells;
induction on its finite cardinality glues the remaining terminal points. -/
noncomputable section
open Set Topology Order
universe u
namespace ThesisCommon

theorem countableCompact_ordinal_model_at (α : Ordinal.{u}) :
    ∀ (K : Type u) [MetricSpace K] [CompactSpace K] [Countable K] [Nonempty K],
      (ordinalDerived (univ : Set K) α).Finite →
      (ordinalDerived (univ : Set K) α).Nonempty →
      ∃ β : Ordinal.{u}, Nonempty (K ≃ₜ OrdinalInterval β) := by
  classical
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro K instMetric instCompact instCountable instNonempty hfin hne
    by_cases hα : α = 0
    · subst α
      letI : Finite K := Set.finite_univ_iff.mp (by simpa only [ordinalDerived_zero] using hfin)
      exact finiteCompact_exists_ordinal_model K
    have singletonCase : ∀ (L : Type u) [MetricSpace L] [CompactSpace L]
        [Countable L] [Nonempty L] (p : L),
        ordinalDerived (univ : Set L) α = {p} →
        ∃ β : Ordinal.{u}, Nonempty (L ≃ₜ OrdinalInterval β) := by
      intro L _ _ _ _ p hD
      apply countableCompactShell_glue_ordinal_models p
        (ordinalDerived_point_not_isolated α hα (by rw [hD]; simp))
      intro n hn
      obtain ⟨β, hβ, hf, hneq, _⟩ := countableCompactShell_rank_lt p hD n hn
      let B : Set L := countableClopenShell p n
      letI : Nonempty B := hn.to_subtype
      exact ih β hβ B
        (ordinalDerived_subtype_finite B (countableClopenShell_isClopen p n).isClosed β hf)
        (ordinalDerived_subtype_nonempty B (countableClopenShell_isClopen p n).isClosed β hneq)
    have multiplicityCase : ∀ n : ℕ, ∀ (L : Type u) [MetricSpace L] [CompactSpace L]
        [Countable L] [Nonempty L],
        (ordinalDerived (univ : Set L) α).Finite →
        (ordinalDerived (univ : Set L) α).Nonempty →
        (ordinalDerived (univ : Set L) α).ncard = n →
        ∃ β : Ordinal.{u}, Nonempty (L ≃ₜ OrdinalInterval β) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ihN =>
        intro L _ _ _ _ hf hn hcard
        obtain ⟨p, hp⟩ := hn
        obtain ⟨U, hU, hpU, hDU, hDV⟩ := countableCompact_terminal_clopen_split hf hp
        simp only [univ_inter] at hDU
        have hcompl : (univ : Set L) \ U = Uᶜ := by ext x; simp
        rw [hcompl] at hDV
        letI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isClosed.isCompact
        letI : Nonempty U := ⟨⟨p, hpU⟩⟩
        obtain ⟨β, ⟨eU⟩⟩ := singletonCase U ⟨p, hpU⟩
          (ordinalDerived_subtype_singleton U hU.isClosed α hpU hDU)
        by_cases hC : Nonempty ↥(Uᶜ)
        · letI : Nonempty ↥(Uᶜ) := hC
          letI : CompactSpace ↥(Uᶜ) := isCompact_iff_compactSpace.mp hU.compl.isClosed.isCompact
          have hfC : (ordinalDerived (univ : Set ↥(Uᶜ)) α).Finite :=
            ordinalDerived_subtype_finite Uᶜ hU.compl.isClosed α (by rw [hDV]; exact hf.diff)
          have modelC : ∃ γ : Ordinal.{u}, Nonempty (↥(Uᶜ) ≃ₜ OrdinalInterval γ) := by
            by_cases he : ordinalDerived (univ : Set ↥(Uᶜ)) α = ∅
            · obtain ⟨γ, hγ, hfinγ, hnγ, _⟩ :=
                countableCompact_exists_terminal_rank_lt isCompact_univ
                  (show (univ : Set ↥(Uᶜ)).Nonempty from Set.univ_nonempty) he
              exact ih γ hγ ↥(Uᶜ) hfinγ hnγ
            · have hc : (ordinalDerived (univ : Set ↥(Uᶜ)) α).ncard < n := by
                rw [ordinalDerived_subtype_ncard Uᶜ hU.compl.isClosed α, hDV, ← hcard]
                exact Set.ncard_diff_singleton_lt_of_mem hp hf
              exact ihN _ hc ↥(Uᶜ) hfC (Set.nonempty_iff_ne_empty.mpr he) rfl
          obtain ⟨γ, ⟨eV⟩⟩ := modelC
          exact ⟨β + 1 + γ, compactClopen_glue_ordinal_models U hU eU eV⟩
        · letI : IsEmpty ↥(Uᶜ) := not_nonempty_iff.mp hC
          exact ⟨β, ⟨(compactClopenSumHomeomorph U hU).symm.trans
            ((Homeomorph.sumEmpty U ↥(Uᶜ)).trans eU)⟩⟩
    exact multiplicityCase _ K hfin hne rfl

/-- Every nonempty countable compact metric space has an actual compact
ordinal interval model, with the original subspace and order topologies. -/
theorem countableCompact_exists_ordinal_model (K : Type u) [MetricSpace K]
    [CompactSpace K] [Countable K] [Nonempty K] :
    ∃ α : Ordinal.{u}, Nonempty (K ≃ₜ OrdinalInterval α) := by
  obtain ⟨α, hfin, hne, _⟩ := countableCompact_exists_finite_nonempty_derivative
    isCompact_univ (show (univ : Set K).Nonempty from Set.univ_nonempty)
  exact countableCompact_ordinal_model_at α K hfin hne

end ThesisCommon
