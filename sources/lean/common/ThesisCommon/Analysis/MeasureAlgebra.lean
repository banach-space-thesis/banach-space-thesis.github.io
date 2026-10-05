import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-! The measure algebra used in PEMS Section 3: actual measurable subsets
modulo equality almost everywhere. Countable unions/intersections are defined
on quotient classes, with representative-independence proved below. -/
noncomputable section
open Set MeasureTheory Filter
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X]

def measurableSetAE (μ : Measure X) : Setoid {A : Set X // MeasurableSet A} where
  r A B := A.val =ᵐ[μ] B.val
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl, fun h => h.symm, fun h g => h.trans g⟩

/-- Equivalence classes of measurable sets modulo null symmetric difference. -/
def MeasureAlgebra (μ : Measure X) := Quotient (measurableSetAE μ)

namespace MeasureAlgebra
variable {μ : Measure X}

def mk (μ : Measure X) (A : Set X) (hA : MeasurableSet A) : MeasureAlgebra μ :=
  Quotient.mk _ ⟨A, hA⟩

theorem mk_eq_mk {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    mk μ A hA = mk μ B hB ↔ A =ᵐ[μ] B := Quotient.eq

def representative (a : MeasureAlgebra μ) : {A : Set X // MeasurableSet A} :=
  Quotient.out a

@[simp] theorem mk_representative (a : MeasureAlgebra μ) :
    mk μ a.representative.val a.representative.property = a := Quotient.out_eq a

theorem representative_mk_ae (A : Set X) (hA : MeasurableSet A) :
    (mk μ A hA).representative.val =ᵐ[μ] A :=
  (mk_eq_mk _ _).mp (mk_representative _)

/-- The measure of a class is independent of its representative. -/
def measure (a : MeasureAlgebra μ) : ENNReal :=
  Quotient.lift (fun A : {A : Set X // MeasurableSet A} => μ A.val)
    (fun _ _ h => measure_congr h) a

@[simp] theorem measure_mk (A : Set X) (hA : MeasurableSet A) :
    (mk μ A hA).measure = μ A := rfl

def compl (a : MeasureAlgebra μ) : MeasureAlgebra μ :=
  mk μ a.representative.valᶜ a.representative.property.compl

@[simp] theorem compl_mk (A : Set X) (hA : MeasurableSet A) :
    compl (mk μ A hA) = mk μ Aᶜ hA.compl := by
  apply (mk_eq_mk _ _).mpr
  filter_upwards [representative_mk_ae (μ := μ) A hA] with x hx
  exact congrArg Not hx

def iUnion {ι : Type*} [Countable ι] (a : ι → MeasureAlgebra μ) : MeasureAlgebra μ :=
  mk μ (⋃ i, (a i).representative.val)
    (MeasurableSet.iUnion fun i => (a i).representative.property)

@[simp] theorem iUnion_mk {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    iUnion (fun i => mk μ (A i) (hA i)) = mk μ (⋃ i, A i) (MeasurableSet.iUnion hA) := by
  apply (mk_eq_mk _ _).mpr
  exact EventuallyEq.countable_iUnion fun i => representative_mk_ae (A i) (hA i)

def iInter {ι : Type*} [Countable ι] (a : ι → MeasureAlgebra μ) : MeasureAlgebra μ :=
  mk μ (⋂ i, (a i).representative.val)
    (MeasurableSet.iInter fun i => (a i).representative.property)

@[simp] theorem iInter_mk {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    iInter (fun i => mk μ (A i) (hA i)) = mk μ (⋂ i, A i) (MeasurableSet.iInter hA) := by
  apply (mk_eq_mk _ _).mpr
  exact EventuallyEq.countable_iInter fun i => representative_mk_ae (A i) (hA i)

theorem iInter_eq_compl_iUnion_compl {ι : Type*} [Countable ι]
    (a : ι → MeasureAlgebra μ) : iInter a = compl (iUnion (fun i => compl (a i))) := by
  have ha : a = fun i => mk μ (a i).representative.val (a i).representative.property := by
    funext i
    exact (mk_representative _).symm
  rw [ha]
  simp only [iInter_mk, compl_mk, iUnion_mk]
  congr 1
  simp

end MeasureAlgebra

/-- A measure-algebra isomorphism in the paper's sense. This is an equivalence
of the actual quotient classes, preserving complements, countable unions and
measure. It does not assert the existence of any representation isomorphism. -/
structure MeasureAlgebraIso {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) where
  toEquiv : MeasureAlgebra μ ≃ MeasureAlgebra ν
  map_compl : ∀ a, toEquiv (MeasureAlgebra.compl a) = MeasureAlgebra.compl (toEquiv a)
  map_iUnion : ∀ (ι : Type) [Countable ι] (a : ι → MeasureAlgebra μ),
    toEquiv (MeasureAlgebra.iUnion a) = MeasureAlgebra.iUnion (fun i => toEquiv (a i))
  measure_eq : ∀ a, (toEquiv a).measure = a.measure

namespace MeasureAlgebraIso
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem map_iInter (Φ : MeasureAlgebraIso μ ν) {ι : Type} [Countable ι]
    (a : ι → MeasureAlgebra μ) :
    Φ.toEquiv (MeasureAlgebra.iInter a) =
      MeasureAlgebra.iInter (fun i => Φ.toEquiv (a i)) := by
  rw [MeasureAlgebra.iInter_eq_compl_iUnion_compl, Φ.map_compl, Φ.map_iUnion]
  simp only [Φ.map_compl]
  exact (MeasureAlgebra.iInter_eq_compl_iUnion_compl _).symm

end MeasureAlgebraIso
end ThesisCommon
