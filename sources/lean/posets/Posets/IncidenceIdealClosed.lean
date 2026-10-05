import Posets.IncidenceIdealClassification
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! The interval count is the count of actual closed ideals in the finite
incidence operator algebra with its original operator norm. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option synthInstance.maxHeartbeats 200000
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

section FiniteAlgebra
variable {A : Type} [NormedRing A] [NormedAlgebra 𝕜 A] [FiniteDimensional 𝕜 A]

def twoSidedIdealToSubmodule (I : TwoSidedIdeal A) : Submodule 𝕜 A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c a ha := by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ ha

include 𝕜 in
theorem finiteDimensional_twoSidedIdeal_isClosed (I : TwoSidedIdeal A) :
    IsClosed (I : Set A) := (twoSidedIdealToSubmodule (𝕜 := 𝕜) I).closed_of_finiteDimensional

def finiteTwoSidedIdealClosed (I : TwoSidedIdeal A) : ThesisCommon.ClosedIdeal 𝕜 A :=
  ⟨I, finiteDimensional_twoSidedIdeal_isClosed (𝕜 := 𝕜) I, I.zero_mem,
    fun _ ha _ hb => I.add_mem ha hb,
    fun c _ ha => (twoSidedIdealToSubmodule (𝕜 := 𝕜) I).smul_mem c ha,
    fun a b hb => ⟨I.mul_mem_left a b hb, I.mul_mem_right b a hb⟩⟩

def closedIdealToTwoSided (I : ThesisCommon.ClosedIdeal 𝕜 A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' I.val I.property.2.1
    (fun ha hb => I.property.2.2.1 _ ha _ hb)
    (fun {a} ha => by simpa only [neg_one_smul] using I.property.2.2.2.1 (-1) a ha)
    (fun {a b} hb => (I.property.2.2.2.2 a b hb).1)
    (fun {a b} ha => (I.property.2.2.2.2 b a ha).2)

/-- Every two-sided ideal in a finite-dimensional unital normed algebra is
scalar-linear and closed, so the two vocabularies have exactly the same ideals. -/
def finiteClosedIdealEquivTwoSided : ThesisCommon.ClosedIdeal 𝕜 A ≃ TwoSidedIdeal A where
  toFun := closedIdealToTwoSided
  invFun := finiteTwoSidedIdealClosed
  left_inv I := by
    apply Subtype.ext
    ext a
    exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a
  right_inv I := by
    ext a
    exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

end FiniteAlgebra

variable {P : Type} [PartialOrder P] [LocallyFiniteOrder P] [Fintype P]

def finiteIncidenceClosedIdealEquiv :
    ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) ≃ IntervalUpsets P :=
  (finiteClosedIdealEquivTwoSided (𝕜 := 𝕜)).trans
    (((finiteIncidenceAlgebraEquiv (𝕜 := 𝕜) (P := P)).symm.toRingEquiv.mapTwoSidedIdeal).toEquiv.trans
      incidenceIdealEquiv)

theorem finiteIncidenceClosedIdeal_card :
    Nat.card (ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) =
      idealCount P := Nat.card_congr (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P))

end Posets
