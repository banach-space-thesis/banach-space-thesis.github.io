import Posets.ProductIdealMaximal
import Posets.Definitions
import JFA.CZeroIdeals
import Mathlib.Tactic.FinCases

/-! The scalar c₀ operator algebra contributes three closed ideals and one
maximal closed ideal to the finite-product counts in Proposition 8.4. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type*} [RCLike 𝕜]

theorem closedIdeal_operator_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : Set (E →L[𝕜] E)) :
    IsClosedIdeal 𝕜 I ↔ JFA.IsClosedOperatorIdeal 𝕜 E I := Iff.rfl

def cZeroClosedIdealAt (n : Fin 3) : ClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
  if n = 0 then ⟨{0}, JFA.zeroOperators_closedIdeal⟩
  else if n = 1 then ⟨JFA.compactOperators 𝕜 (cZero 𝕜), JFA.compactOperators_closedIdeal⟩
  else ⊤

theorem cZeroClosedIdealAt_bijective : Function.Bijective (cZeroClosedIdealAt (𝕜 := 𝕜)) := by
  have hs := JFA.cZero_compact_ideal_strict (𝕜 := 𝕜)
  have h0K : ({0} : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) ≠ JFA.compactOperators 𝕜 (cZero 𝕜) := hs.1.ne
  have hKtop : JFA.compactOperators 𝕜 (cZero 𝕜) ≠ Set.univ := hs.2.ne
  have h0top : ({0} : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) ≠ Set.univ :=
    (hs.1.trans hs.2).ne
  obtain ⟨T, _, hT⟩ := Set.exists_of_ssubset hs.1
  letI : Nontrivial (cZero 𝕜 →L[𝕜] cZero 𝕜) :=
    ⟨⟨T, 0, by simpa only [Set.mem_singleton_iff] using hT⟩⟩
  constructor
  · intro i j hij
    have hv := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [cZeroClosedIdealAt]
    exact hT (hv ▸ Set.mem_univ T)
  · intro I
    rcases (JFA.cZero_closedIdeal_classification I.val).mp I.property with h | h | h
    · exact ⟨0, Subtype.ext (by simpa [cZeroClosedIdealAt] using h.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [cZeroClosedIdealAt] using h.symm)⟩
    · exact ⟨2, Subtype.ext (by simpa [cZeroClosedIdealAt] using h.symm)⟩

def cZeroClosedIdealEquivFinThree :
    ClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) ≃ Fin 3 :=
  (Equiv.ofBijective cZeroClosedIdealAt cZeroClosedIdealAt_bijective).symm

theorem cZeroClosedIdeal_card : Nat.card (ClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜)) = 3 := by
  rw [Nat.card_congr (cZeroClosedIdealEquivFinThree (𝕜 := 𝕜)), Nat.card_fin]

theorem cZero_maximalClosedIdeal_iff (I : Set (cZero 𝕜 →L[𝕜] cZero 𝕜)) :
    IsMaximalClosedIdeal 𝕜 I ↔ I = JFA.compactOperators 𝕜 (cZero 𝕜) := by
  have hs := JFA.cZero_compact_ideal_strict (𝕜 := 𝕜)
  constructor
  · intro hI
    rcases (JFA.cZero_closedIdeal_classification I).mp hI.1 with h0 | hK | htop
    · subst I
      rcases hI.2.2 _ JFA.compactOperators_closedIdeal hs.1.le with h | h
      · exact (hs.1.ne h.symm).elim
      · exact (hs.2.ne h).elim
    · exact hK
    · exact (hI.2.1 htop).elim
  · rintro rfl
    refine ⟨JFA.compactOperators_closedIdeal, hs.2.ne, ?_⟩
    intro J hJ hKJ
    rcases (JFA.cZero_closedIdeal_classification J).mp hJ with h0 | hK | htop
    · subst J
      exact (hs.1.not_ge hKJ).elim
    · exact Or.inl hK
    · exact Or.inr htop

def cZeroMaximalClosedIdealEquivFinOne :
    MaximalClosedIdeals 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨JFA.compactOperators 𝕜 (cZero 𝕜),
    (cZero_maximalClosedIdeal_iff _).mpr rfl⟩
  left_inv I := Subtype.ext ((cZero_maximalClosedIdeal_iff I.val).mp I.property).symm
  right_inv _ := Subsingleton.elim _ _

theorem cZeroMaximalClosedIdeal_card :
    Nat.card (MaximalClosedIdeals 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜)) = 1 := by
  rw [Nat.card_congr (cZeroMaximalClosedIdealEquivFinOne (𝕜 := 𝕜)), Nat.card_fin]

theorem cZero_hasUniqueMaximalClosedIdeal :
    HasUniqueMaximalClosedIdeal 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) := by
  refine ⟨JFA.compactOperators 𝕜 (cZero 𝕜), (cZero_maximalClosedIdeal_iff _).mpr rfl, ?_⟩
  intro I hI
  exact (cZero_maximalClosedIdeal_iff I).mp hI

def cZeroNontrivialClosedIdealEquivFinOne :
    NontrivialClosedIdeals 𝕜 (cZero 𝕜 →L[𝕜] cZero 𝕜) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨JFA.compactOperators 𝕜 (cZero 𝕜), JFA.compactOperators_closedIdeal,
    (JFA.cZero_compact_ideal_strict (𝕜 := 𝕜)).1.ne.symm,
    (JFA.cZero_compact_ideal_strict (𝕜 := 𝕜)).2.ne⟩
  left_inv I := by
    apply Subtype.ext
    rcases (JFA.cZero_closedIdeal_classification I.val).mp I.property.1 with h | h | h
    · exact (I.property.2.1 h).elim
    · exact h.symm
    · exact (I.property.2.2 h).elim
  right_inv _ := Subsingleton.elim _ _

end Posets
