import Posets.IdealCountRealizationFactors
import Posets.IdealMaximalTransfer
import Posets.TheoremQuotients

/-! The forward realization and simultaneous ideal counts in Proposition 8.4. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable (r : ℕ) {k : ℕ} (P : Fin k → Type)
  [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)] [∀ i, LocallyFiniteOrder (P i)]

abbrev idealCountAlgebra (m : ℕ) : Type :=
  paddedFiniteAlgebra (𝕜 := 𝕜) (idealCountFiniteFactor (𝕜 := 𝕜) r P) m

theorem idealCountAlgebra_admissible (m : ℕ) :
    AdmissibleAlgebra 𝕜 (idealCountAlgebra (𝕜 := 𝕜) r P m) :=
  paddedFiniteAlgebra_admissible (idealCountFiniteFactor (𝕜 := 𝕜) r P)
    (fun i => cZeroIncidenceFactor_admissible r P (finSumFinEquiv.symm i)) m

def idealCountAlgebra_closedIdealEquiv :
    ClosedIdeal 𝕜 (NormedProduct (idealCountAlgebra (𝕜 := 𝕜) r P)) ≃
      ClosedIdeal 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) :=
  (paddedFiniteAlgebra_closedIdealEquiv (idealCountFiniteFactor (𝕜 := 𝕜) r P)).trans
    (idealCountFiniteFactor_closedIdealEquiv r P)

def idealCountAlgebra_maximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (NormedProduct (idealCountAlgebra (𝕜 := 𝕜) r P)) ≃
      MaximalClosedIdeals 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) :=
  (paddedFiniteAlgebra_maximalClosedIdealEquiv (idealCountFiniteFactor (𝕜 := 𝕜) r P)).trans
    (idealCountFiniteFactor_maximalClosedIdealEquiv r P)

instance cZeroIncidenceProduct_finite_closedIdeals :
    Finite (ClosedIdeal 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) :=
  Finite.of_equiv (∀ i, ClosedIdeal 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i))
    (productClosedIdealOrderIso (𝕜 := 𝕜) (cZeroIncidenceFactor (𝕜 := 𝕜) r P)).toEquiv.symm

instance cZeroIncidenceProduct_finite_maximalClosedIdeals :
    Finite (MaximalClosedIdeals 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) :=
  Finite.of_equiv (Σ i, MaximalClosedIdeals 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i))
    (productMaximalClosedIdealEquiv (𝕜 := 𝕜) (cZeroIncidenceFactor (𝕜 := 𝕜) r P)).symm

def cZeroIncidenceProduct_closedIdealEquivFin :
    ClosedIdeal 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) ≃
      Fin (3 ^ r * ∏ i, idealCount (P i)) :=
  Finite.equivFinOfCardEq (cZeroIncidenceProduct_closedIdeal_card r P)

def cZeroIncidenceProduct_maximalClosedIdealEquivFin :
    MaximalClosedIdeals 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i) ≃
      Fin (r + ∑ i, Fintype.card (P i)) :=
  Finite.equivFinOfCardEq (cZeroIncidenceProduct_maximalClosedIdeal_card r P)

theorem furnishedIdealCount_product :
    FurnishedIdealCount 𝕜 (3 ^ r * ∏ i, idealCount (P i)) := by
  let C := idealCountAlgebra (𝕜 := 𝕜) r P
  have hC : ∀ m, AdmissibleAlgebra 𝕜 (C m) := idealCountAlgebra_admissible r P
  obtain ⟨𝒜, had, θ, ρ, hs, hρ, hθ⟩ := theorem_1_5_proof 𝕜 C hC
  let e := ((strongSplitNontrivialIdealEquiv θ ρ hs had).symm.trans
    (idealCountAlgebra_closedIdealEquiv (𝕜 := 𝕜) r P)).trans
      (cZeroIncidenceProduct_closedIdealEquivFin (𝕜 := 𝕜) r P)
  exact ⟨C, inferInstance, inferInstance, inferInstance, hC,
    𝒜, had, ⟨θ, ρ, hs, hρ, hθ⟩, ⟨e⟩⟩

theorem nontrivial_of_maximalClosedIdeal {C : Type}
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (I : MaximalClosedIdeals 𝕜 C) : Nontrivial C := by
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  letI := h
  apply I.property.2.1
  exact Set.eq_univ_of_forall (fun c => (Subsingleton.elim (0 : C) c) ▸ I.property.1.2.1)

theorem idealCountAlgebra_nontrivial [∀ i, Nonempty (P i)] (hpos : 1 ≤ r + k) :
    Nontrivial (NormedProduct (idealCountAlgebra (𝕜 := 𝕜) r P)) := by
  have hi : Nonempty (Fin r ⊕ Fin k) := by
    by_cases hr : 0 < r
    · exact ⟨Sum.inl ⟨0, hr⟩⟩
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  let i := Classical.choice hi
  have hj : Nonempty (MaximalClosedIdeals 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) := by
    cases i with
    | inl i => exact ⟨(cZeroMaximalClosedIdealEquivFinOne (𝕜 := 𝕜)).symm 0⟩
    | inr i => exact ⟨(finiteIncidenceMaximalClosedIdealEquiv (𝕜 := 𝕜) (P := P i)).symm
        (Classical.choice (inferInstance : Nonempty (P i)))⟩
  let J := (productMaximalClosedIdealEquiv (𝕜 := 𝕜)
    (cZeroIncidenceFactor (𝕜 := 𝕜) r P)).symm ⟨i, Classical.choice hj⟩
  exact nontrivial_of_maximalClosedIdeal
    ((idealCountAlgebra_maximalClosedIdealEquiv (𝕜 := 𝕜) r P).symm J)

theorem exists_space_with_idealCounts [∀ i, Nonempty (P i)] (hpos : 1 ≤ r + k) :
    ∃ 𝒜 : Set (Set ℕ), IsAlmostDisjoint 𝒜 ∧
      Nonempty (NontrivialClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (3 ^ r * ∏ i, idealCount (P i))) ∧
      Nonempty (MaximalClosedIdeals 𝕜 (Space 𝕜 𝒜 →L[𝕜] Space 𝕜 𝒜) ≃
        Fin (r + ∑ i, Fintype.card (P i))) := by
  let C := idealCountAlgebra (𝕜 := 𝕜) r P
  letI : Nontrivial (NormedProduct C) := idealCountAlgebra_nontrivial r P hpos
  obtain ⟨𝒜, had, θ, ρ, hs, _, _⟩ := theorem_1_5_proof 𝕜 C (idealCountAlgebra_admissible r P)
  let e := ((strongSplitNontrivialIdealEquiv θ ρ hs had).symm.trans
    (idealCountAlgebra_closedIdealEquiv (𝕜 := 𝕜) r P)).trans
      (cZeroIncidenceProduct_closedIdealEquivFin (𝕜 := 𝕜) r P)
  let eM := ((strongSplitMaximalIdealEquiv θ ρ hs had).symm.trans
    (idealCountAlgebra_maximalClosedIdealEquiv (𝕜 := 𝕜) r P)).trans
      (cZeroIncidenceProduct_maximalClosedIdealEquivFin (𝕜 := 𝕜) r P)
  exact ⟨𝒜, had, ⟨e⟩, ⟨eM⟩⟩

end Posets
