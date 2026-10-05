import Posets.IncidenceMaximalUpsets
import Posets.IncidenceIdealClosed

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option synthInstance.maxHeartbeats 200000

namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

section FiniteAlgebra
variable {A : Type} [NormedRing A] [NormedAlgebra 𝕜 A] [FiniteDimensional 𝕜 A]

omit [FiniteDimensional 𝕜 A] in
@[simp] theorem mem_closedIdealToTwoSided (I : ThesisCommon.ClosedIdeal 𝕜 A) (a : A) :
    a ∈ closedIdealToTwoSided I ↔ a ∈ I.val :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

theorem finiteClosedIdealEquivTwoSided_le_iff (I J : ThesisCommon.ClosedIdeal 𝕜 A) :
    finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) I ≤ finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) J ↔ I.val ⊆ J.val := by
  change (∀ a, a ∈ closedIdealToTwoSided I → a ∈ closedIdealToTwoSided J) ↔ _
  simp only [mem_closedIdealToTwoSided]
  rfl

theorem finiteClosedIdealEquivTwoSided_eq_top_iff (I : ThesisCommon.ClosedIdeal 𝕜 A) :
    finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) I = ⊤ ↔ I.val = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro a
    apply (mem_closedIdealToTwoSided I a).mp
    change a ∈ finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) I
    rw [h]
    exact TwoSidedIdeal.mem_top A
  · intro h
    apply TwoSidedIdeal.ext
    intro a
    change a ∈ closedIdealToTwoSided I ↔ a ∈ (⊤ : TwoSidedIdeal A)
    simp [h, TwoSidedIdeal.mem_top]

end FiniteAlgebra

variable {P : Type} [PartialOrder P] [LocallyFiniteOrder P] [Fintype P]

theorem incidenceIdealIntervals_subset_iff (I J : TwoSidedIdeal (IncidenceAlgebra 𝕜 P)) :
    (incidenceIdealIntervals I).val ⊆ (incidenceIdealIntervals J).val ↔ I ≤ J := by
  constructor
  · intro h
    rw [← intervalUpsetIdeal_intervals I, ← intervalUpsetIdeal_intervals J]
    intro f hf
    rw [mem_intervalUpsetIdeal] at hf ⊢
    intro i hi
    exact hf i (fun hmem => hi (h hmem))
  · intro h i hi
    exact h hi

theorem incidenceIdealIntervals_eq_univ_iff (I : TwoSidedIdeal (IncidenceAlgebra 𝕜 P)) :
    (incidenceIdealIntervals I).val = Set.univ ↔ I = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro f _
    rw [← intervalUpsetIdeal_intervals I, mem_intervalUpsetIdeal]
    intro i hi
    exact False.elim (hi (by rw [h]; trivial))
  · rintro rfl
    apply Set.eq_univ_of_forall
    intro i
    change incidenceUnit (𝕜 := 𝕜) i ∈ (⊤ : TwoSidedIdeal (IncidenceAlgebra 𝕜 P))
    exact TwoSidedIdeal.mem_top (IncidenceAlgebra 𝕜 P)

theorem finiteIncidenceClosedIdeal_subset_iff
    (I J : ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) :
    (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P) I).val ⊆ (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P) J).val ↔
      I.val ⊆ J.val := by
  change (incidenceIdealIntervals _).val ⊆ (incidenceIdealIntervals _).val ↔ _
  rw [incidenceIdealIntervals_subset_iff]
  let e : TwoSidedIdeal (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) ≃o
      TwoSidedIdeal (IncidenceAlgebra 𝕜 P) :=
    (finiteIncidenceAlgebraEquiv (𝕜 := 𝕜) (P := P)).symm.toRingEquiv.mapTwoSidedIdeal
  change e (finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) I) ≤
    e (finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) J) ↔ _
  rw [e.le_iff_le]
  exact finiteClosedIdealEquivTwoSided_le_iff I J

theorem finiteIncidenceClosedIdeal_eq_univ_iff
    (I : ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) :
    (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P) I).val = Set.univ ↔ I.val = Set.univ := by
  change (incidenceIdealIntervals _).val = Set.univ ↔ _
  rw [incidenceIdealIntervals_eq_univ_iff]
  let e : TwoSidedIdeal (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) ≃o
      TwoSidedIdeal (IncidenceAlgebra 𝕜 P) :=
    (finiteIncidenceAlgebraEquiv (𝕜 := 𝕜) (P := P)).symm.toRingEquiv.mapTwoSidedIdeal
  change e (finiteClosedIdealEquivTwoSided (𝕜 := 𝕜) I) = ⊤ ↔ _
  rw [← e.map_top, e.injective.eq_iff]
  exact finiteClosedIdealEquivTwoSided_eq_top_iff I

theorem finiteIncidenceClosedIdeal_maximal_iff
    (I : ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) :
    ThesisCommon.IsMaximalClosedIdeal 𝕜 I.val ↔
      IsMaximalIntervalUpset (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P) I) := by
  let e := finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P)
  constructor
  · intro hI
    refine ⟨fun h => hI.2.1 ((finiteIncidenceClosedIdeal_eq_univ_iff I).mp h), ?_⟩
    intro V hV
    let J := e.symm V
    have hIJ : I.val ⊆ J.val := (finiteIncidenceClosedIdeal_subset_iff I J).mp (by
      simpa only [J, e, Equiv.apply_symm_apply] using hV)
    rcases hI.2.2 J.val J.property hIJ with heq | htop
    · left
      have hJI : J = I := Subtype.ext heq
      calc
        V = e J := (e.apply_symm_apply V).symm
        _ = e I := congrArg e hJI
    · right
      have ht := (finiteIncidenceClosedIdeal_eq_univ_iff J).mpr htop
      simpa only [J, e, Equiv.apply_symm_apply] using ht
  · intro hI
    refine ⟨I.property, fun h => hI.1 ((finiteIncidenceClosedIdeal_eq_univ_iff I).mpr h), ?_⟩
    intro J hJ hIJ
    let J' : ThesisCommon.ClosedIdeal 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) := ⟨J, hJ⟩
    have hs := (finiteIncidenceClosedIdeal_subset_iff I J').mpr hIJ
    rcases hI.2 (e J') hs with heq | htop
    · left
      exact congrArg Subtype.val (e.injective heq)
    · right
      exact (finiteIncidenceClosedIdeal_eq_univ_iff J').mp htop

end Posets

