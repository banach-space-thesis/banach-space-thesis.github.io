import ThesisCommon.Analysis.CountableCompactRankBound
import ThesisCommon.Analysis.CountableCompactTerminalSplit

/-! A well-founded assembly principle for countable compact metric spaces.
The outer induction decreases the terminal derivative rank; the inner finite
induction splits the terminal derivative into singleton pieces. -/
noncomputable section
open Set ThesisCommon
namespace Posets

/-- To establish a property of every nonempty compact subset, it suffices to
glue clopen pieces and to handle a singleton terminal derivative using compact
pieces that avoid its terminal point. No bound or regularity assumption on
the countable Cantor--Bendixson rank is introduced. -/
theorem countableCompact_induction_on_terminal_derivative
    {K : Type} [MetricSpace K] [CompactSpace K] [Countable K]
    (P : Set K → Prop)
    (hsplit : ∀ A : Set K, IsCompact A → ∀ U : Set K, IsClopen U →
      P (A ∩ U) → P (A \ U) → P A)
    (hsingle : ∀ (A : Set K), IsCompact A → ∀ (α : Ordinal.{0}) (p : K),
      ordinalDerived A α = {p} →
      (∀ B : Set K, IsCompact B → B ⊆ A → B.Nonempty → Disjoint B {p} → P B) → P A)
    (A : Set K) (hA : IsCompact A) (hne : A.Nonempty) : P A := by
  classical
  have hind (α : Ordinal.{0}) : ∀ D : Set K, D.Finite →
      ∀ A : Set K, IsCompact A → ordinalDerived A α = D → D.Nonempty → P A := by
    induction α using Ordinal.induction with
    | h α ih =>
      have hsingleton (A : Set K) (hA : IsCompact A) (p : K)
          (hd : ordinalDerived A α = {p}) : P A := by
        apply hsingle A hA α p hd
        intro B hB hBA hn hdisj
        obtain ⟨β, hβα, hfin, hne, _⟩ := countableCompact_piece_rank_lt (α := α) hA hB hBA hn
          (by simpa only [hd] using hdisj)
        exact ih β hβα _ hfin B hB rfl hne
      intro D hD
      induction D, hD using Set.Finite.induction_on with
      | empty =>
        intro A hA hd hn
        exact (Set.not_nonempty_empty hn).elim
      | @insert p D hpD hD ihD =>
        intro A hA hd _
        by_cases hn : D.Nonempty
        · have hp : p ∈ ordinalDerived A α := hd.symm ▸ Set.mem_insert p D
          obtain ⟨U, hU, _, hleft, hright⟩ := countableCompact_terminal_clopen_split
            (hd.symm ▸ hD.insert p) hp
          apply hsplit A hA U hU
          · exact hsingleton (A ∩ U) (hA.inter_right hU.isClosed) p hleft
          · apply ihD (A \ U) (hA.diff hU.isOpen) _ hn
            simpa only [hd, Set.insert_diff_of_mem, Set.mem_singleton_iff,
              Set.diff_singleton_eq_self hpD] using hright
        · have he : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
          apply hsingleton A hA p
          simpa [he] using hd
  obtain ⟨α, hfin, hn, _⟩ := countableCompact_exists_finite_nonempty_derivative hA hne
  exact hind α _ hfin A hA rfl hn

end Posets
