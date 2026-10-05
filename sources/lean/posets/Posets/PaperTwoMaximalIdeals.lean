import Posets.PaperTwoMaximalIdealsAbstract
import Posets.PaperTwoMaximalIdealsEllOne
import Posets.PaperTwoMaximalIdealsNonseparable
import Posets.OrdinalIdealTransportRegularFactorization
import ThesisCommon.Analysis.IntervalPrimariness
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Exact opening observation of Section 3: B(C[0,1] ⊕ C[0,ω₁]) has
precisely two maximal ideals. Both actual relative nonfactorisation ideals
are exhibited, and ordinary and closed maximal ideals are counted explicitly. -/
noncomputable section
open ThesisCommon Set
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

abbrev PaperTwoMaximalSpace (𝕜 : Type) [RCLike 𝕜] :=
  IntervalContinuous 𝕜 × OrdinalSpace 𝕜 (Cardinal.aleph 1).ord

def paperIntervalNonfactorization : Set (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜) :=
  {T | DoesNotFactorIdentity 𝕜 T (IntervalContinuous 𝕜)}

def paperOmegaOneNonfactorization : Set (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜) :=
  {T | DoesNotFactorIdentity 𝕜 T (OrdinalSpace 𝕜 (Cardinal.aleph 1).ord)}

theorem paper_two_maximal_ideals :
    paperIntervalNonfactorization (𝕜 := 𝕜) ≠ paperOmegaOneNonfactorization ∧
      ∀ I : Set (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜),
        IsMaximalAlgebraIdeal 𝕜 I ↔
          I = paperIntervalNonfactorization ∨ I = paperOmegaOneNonfactorization := by
  letI : Nonempty (ThesisCommon.OrdinalInterval (Cardinal.aleph 1).ord) :=
    ⟨⟨0, le_rfl, Ordinal.zero_le _⟩⟩
  apply paper_two_maximal_ideals_of_pfp interval_hasUPFP.hasPFP
    (initialOrdinal_hasPFP Cardinal.isRegular_aleph_one Cardinal.aleph0_lt_aleph_one)
  · exact paper_interval_not_complemented_in_scattered _
      (JLMS.scattered_ordinalInterval _)
  · apply paper_nonseparable_not_complemented_in_separable
    apply paper_ordinal_nonseparable
    simpa only [Cardinal.card_ord] using Cardinal.aleph0_lt_aleph_one

theorem paper_two_maximal_closed_ideals :
    paperIntervalNonfactorization (𝕜 := 𝕜) ≠ paperOmegaOneNonfactorization ∧
      ∀ I : Set (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜),
        IsMaximalClosedIdeal 𝕜 I ↔
          I = paperIntervalNonfactorization ∨ I = paperOmegaOneNonfactorization := by
  refine ⟨paper_two_maximal_ideals.1, ?_⟩
  intro I
  exact (isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal (𝕜 := 𝕜) I).symm.trans
    (paper_two_maximal_ideals.2 I)

theorem paper_card_two_of_classification {X : Type*} (P : X → Prop) (x y : X)
    (hxy : x ≠ y) (hP : ∀ z, P z ↔ z = x ∨ z = y) : Nat.card {z // P z} = 2 := by
  classical
  let f : Bool → {z // P z} := fun b =>
    if b then ⟨y, (hP y).mpr (Or.inr rfl)⟩ else ⟨x, (hP x).mpr (Or.inl rfl)⟩
  have hi : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f, Subtype.mk.injEq]
  have hs : Function.Surjective f := by
    intro z
    rcases (hP z.val).mp z.property with h | h
    · exact ⟨false, Subtype.ext (by simpa [f] using h.symm)⟩
    · exact ⟨true, Subtype.ext (by simpa [f] using h.symm)⟩
  have h := Nat.card_eq_of_bijective f ⟨hi, hs⟩
  simpa using h.symm

theorem paper_two_maximal_ideals_card :
    Nat.card {I : Set (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜) //
      IsMaximalAlgebraIdeal 𝕜 I} = 2 :=
  paper_card_two_of_classification _ _ _ paper_two_maximal_ideals.1 paper_two_maximal_ideals.2

theorem paper_two_maximal_closed_ideals_card :
    Nat.card (MaximalClosedIdeals 𝕜
      (PaperTwoMaximalSpace 𝕜 →L[𝕜] PaperTwoMaximalSpace 𝕜)) = 2 :=
  paper_card_two_of_classification _ _ _
    paper_two_maximal_closed_ideals.1 paper_two_maximal_closed_ideals.2

end Posets
