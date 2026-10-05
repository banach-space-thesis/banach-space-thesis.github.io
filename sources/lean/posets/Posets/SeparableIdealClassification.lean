import Posets.SeparableIdealCountableInduction
import Posets.SeparableIdealPointAssembly

/-! Classification of nonempty countable compact metric spaces by ordinal intervals. -/
noncomputable section
open Set ThesisCommon Topology
namespace Posets

theorem countableCompact_subset_hasOrdinalCompactModel
    {K : Type} [MetricSpace K] [CompactSpace K] [Countable K]
    (A : Set K) (hA : IsCompact A) (hne : A.Nonempty) : HasOrdinalCompactModel A := by
  apply countableCompact_induction_on_terminal_derivative
    (fun B : Set K => HasOrdinalCompactModel B) _ _ A hA hne
  · intro B hB U hU hleft hright
    exact hasOrdinalCompactModel_of_clopen_pieces B hB U hU hleft hright
  · intro B hB α p hd hrec
    have hp : p ∈ B := by
      have hsub : ordinalDerived B α ⊆ B := by
        simpa using ordinalDerived_antitone hB.isClosed (show 0 ≤ α from bot_le)
      exact hsub (hd.symm ▸ Set.mem_singleton p)
    letI : CompactSpace B := isCompact_iff_compactSpace.mp hB
    let pB : B := ⟨p, hp⟩
    apply hasOrdinalCompactModel_of_compact_pieces_away pB
    intro C hC hn hdisj
    have hcomp : IsCompact (Subtype.val '' C : Set K) := hC.image continuous_subtype_val
    have hsub : (Subtype.val '' C : Set K) ⊆ B := by
      rintro x ⟨y, _, rfl⟩
      exact y.property
    have hnp : Disjoint (Subtype.val '' C : Set K) {p} := by
      apply Set.disjoint_singleton_right.mpr
      rintro ⟨y, hy, he⟩
      have he' : y = pB := Subtype.ext he
      exact Set.disjoint_singleton_right.mp hdisj (he' ▸ hy)
    exact (hrec _ hcomp hsub (hn.image Subtype.val) hnp).of_homeomorph
      (IsEmbedding.subtypeVal.homeomorphImage C)

/-- The countable compact metric classification, including finite spaces.
The empty space is excluded because an ordinal interval contains its zero point. -/
theorem countableCompact_hasOrdinalCompactModel
    (K : Type) [MetricSpace K] [CompactSpace K] [Countable K] [Nonempty K] :
    HasOrdinalCompactModel K :=
  (countableCompact_subset_hasOrdinalCompactModel (univ : Set K) isCompact_univ
    Set.univ_nonempty).of_homeomorph (Homeomorph.Set.univ K).symm

end Posets
