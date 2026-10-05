import PosetsCommon.MaximalIdeals
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.Analysis.Matrix

/-! Maximal closed ideals in Banach algebras and their finite matrix algebras. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
open ThesisCommon
variable {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

def algebraIdealToTwoSided {I : Set A} (hI : IsAlgebraIdeal 𝕜 I) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' I hI.1 (fun ha hb => hI.2.1 _ ha _ hb)
    (fun {a} ha => by simpa only [neg_one_smul] using hI.2.2.1 (-1) a ha)
    (fun {a b} hb => (hI.2.2.2 a b hb).1)
    (fun {a b} ha => (hI.2.2.2 b a ha).2)

@[simp] theorem algebraIdealToTwoSided_coe {I : Set A} (hI : IsAlgebraIdeal 𝕜 I) :
    (algebraIdealToTwoSided hI : Set A) = I := TwoSidedIdeal.coe_mk' _ _ _ _ _ _

theorem twoSidedIdeal_isAlgebraIdeal (I : TwoSidedIdeal A) :
    IsAlgebraIdeal 𝕜 (I : Set A) := by
  refine ⟨I.zero_mem, fun _ ha _ hb => I.add_mem ha hb, ?_, ?_⟩
  · intro c a ha
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ ha
  · intro a b hb
    exact ⟨I.mul_mem_left _ _ hb, I.mul_mem_right _ _ hb⟩

theorem twoSidedIdeal_maximal_iff_isCoatom (I : TwoSidedIdeal A) :
    IsMaximalAlgebraIdeal 𝕜 (I : Set A) ↔ IsCoatom I := by
  rw [isCoatom_iff_ge_of_le]
  constructor
  · rintro ⟨hI, hp, hm⟩
    refine ⟨fun h => hp (by simpa only [h, TwoSidedIdeal.coe_top]), ?_⟩
    intro J hJ hIJ
    rcases hm (J : Set A) (twoSidedIdeal_isAlgebraIdeal J) hIJ with he | he
    · exact le_of_eq (SetLike.coe_injective he)
    · exact (hJ (SetLike.coe_injective (by simpa only [TwoSidedIdeal.coe_top] using he))).elim
  · rintro ⟨hp, hm⟩
    refine ⟨twoSidedIdeal_isAlgebraIdeal I,
      fun h => hp (SetLike.coe_injective (by simpa only [TwoSidedIdeal.coe_top] using h)), ?_⟩
    intro J hJ hIJ
    by_cases ht : J = Set.univ
    · exact Or.inr ht
    · left
      have hproper : algebraIdealToTwoSided hJ ≠ ⊤ := by
        intro he
        apply ht
        simpa only [algebraIdealToTwoSided_coe, TwoSidedIdeal.coe_top] using congrArg SetLike.coe he
      have hle : I ≤ algebraIdealToTwoSided hJ := by
        change (I : Set A) ⊆ (algebraIdealToTwoSided hJ : Set A)
        simpa only [algebraIdealToTwoSided_coe] using hIJ
      have hback := hm (algebraIdealToTwoSided hJ) hproper hle
      change (algebraIdealToTwoSided hJ : Set A) ⊆ (I : Set A) at hback
      exact Set.Subset.antisymm (by simpa only [algebraIdealToTwoSided_coe] using hback) hIJ

theorem uniqueMaximalAlgebra_iff_uniqueTwoSidedCoatom :
    (∃! I : Set A, IsMaximalAlgebraIdeal 𝕜 I) ↔ ∃! I : TwoSidedIdeal A, IsCoatom I := by
  constructor
  · rintro ⟨I, hI, hu⟩
    let J := algebraIdealToTwoSided hI.1
    have hc : (J : Set A) = I := algebraIdealToTwoSided_coe _
    refine ⟨J, (twoSidedIdeal_maximal_iff_isCoatom J).mp (hc.symm ▸ hI), ?_⟩
    intro K hK
    apply SetLike.coe_injective
    exact (hu (K : Set A) ((twoSidedIdeal_maximal_iff_isCoatom K).mpr hK)).trans hc.symm
  · rintro ⟨I, hI, hu⟩
    refine ⟨(I : Set A), (twoSidedIdeal_maximal_iff_isCoatom I).mpr hI, ?_⟩
    intro J hJ
    have hc : (algebraIdealToTwoSided hJ.1 : Set A) = J := algebraIdealToTwoSided_coe _
    have he := hu (algebraIdealToTwoSided hJ.1)
      ((twoSidedIdeal_maximal_iff_isCoatom _).mp (hc.symm ▸ hJ))
    exact hc.symm.trans (congrArg SetLike.coe he)

theorem uniqueMaximalClosed_iff_uniqueTwoSidedCoatom [CompleteSpace A] :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ ∃! I : TwoSidedIdeal A, IsCoatom I :=
  uniqueMaximalAlgebraIdeal_iff_uniqueMaximalClosedIdeal.symm.trans
    uniqueMaximalAlgebra_iff_uniqueTwoSidedCoatom

theorem uniqueMaximalClosed_ringEquiv {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B]
    [CompleteSpace A] [CompleteSpace B] (e : A ≃+* B) :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ HasUniqueMaximalClosedIdeal 𝕜 B := by
  rw [uniqueMaximalClosed_iff_uniqueTwoSidedCoatom, uniqueMaximalClosed_iff_uniqueTwoSidedCoatom]
  exact e.mapTwoSidedIdeal.toEquiv.existsUnique_congr
    (fun I => (e.mapTwoSidedIdeal.isCoatom_iff I).symm)

open scoped Matrix.Norms.Operator

/-- The index set is explicitly nonempty, so no empty-matrix exception is hidden. -/
theorem uniqueMaximalClosed_matrix_equiv [CompleteSpace A]
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    HasUniqueMaximalClosedIdeal 𝕜 A ↔ HasUniqueMaximalClosedIdeal 𝕜 (Matrix ι ι A) := by
  letI : CompleteSpace (Matrix ι ι A) :=
    inferInstanceAs (CompleteSpace (ι → PiLp 1 (fun _ : ι => A)))
  rw [uniqueMaximalClosed_iff_uniqueTwoSidedCoatom, uniqueMaximalClosed_iff_uniqueTwoSidedCoatom]
  let e := TwoSidedIdeal.orderIsoMatrix (R := A) (n := ι)
  exact e.toEquiv.existsUnique_congr (fun I => (e.isCoatom_iff I).symm)

end Posets

