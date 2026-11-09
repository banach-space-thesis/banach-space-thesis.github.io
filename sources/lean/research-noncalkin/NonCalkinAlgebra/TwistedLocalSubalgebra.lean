import NonCalkinAlgebra.TwistedFiniteSpan
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Field.ZMod

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G] [Module (ZMod 2) G]

def localSpan (c : Cocycle G) (P : Submodule (ZMod 2) G) :
    Submodule ℂ (closedSubalgebra c) :=
  Submodule.span ℂ (Set.range (fun g : P => shiftInAlgebra c (g : G)))

theorem localShift_mem (c : Cocycle G) (P : Submodule (ZMod 2) G)
    (g : G) (hg : g ∈ P) : shiftInAlgebra c g ∈ localSpan c P :=
  Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩

theorem localSpan_mono (c : Cocycle G) {P Q : Submodule (ZMod 2) G} (h : P ≤ Q) :
    localSpan c P ≤ localSpan c Q := by
  apply Submodule.span_mono
  rintro a ⟨g, rfl⟩
  exact ⟨⟨(g : G), h g.property⟩, rfl⟩

theorem localSpan_mul (c : Cocycle G) (P : Submodule (ZMod 2) G)
    {a b : closedSubalgebra c} (ha : a ∈ localSpan c P) (hb : b ∈ localSpan c P) :
    a * b ∈ localSpan c P := by
  change a ∈ Submodule.span ℂ _ at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    change b ∈ Submodule.span ℂ _ at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, rfl⟩ := hb
      rw [shiftInAlgebra_mul]
      exact (localSpan c P).smul_mem _
        (localShift_mem c P _ (P.add_mem g.property k.property))
    | zero => simpa only [mul_zero] using (localSpan c P).zero_mem
    | add b d hb hd ihb ihd =>
      simpa only [mul_add] using (localSpan c P).add_mem ihb ihd
    | smul r b hb ih =>
      simpa only [mul_smul_comm] using (localSpan c P).smul_mem r ih
  | zero => simpa only [zero_mul] using (localSpan c P).zero_mem
  | add a d ha hd iha ihd =>
    simpa only [add_mul] using (localSpan c P).add_mem iha ihd
  | smul r a ha ih =>
    simpa only [smul_mul_assoc] using (localSpan c P).smul_mem r ih

theorem localSpan_star (c : Cocycle G) (P : Submodule (ZMod 2) G)
    {a : closedSubalgebra c} (ha : a ∈ localSpan c P) : star a ∈ localSpan c P := by
  change a ∈ Submodule.span ℂ _ at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    rw [star_shiftInAlgebra]
    exact (localSpan c P).smul_mem _ (localShift_mem c P _ (P.neg_mem g.property))
  | zero => simpa only [star_zero] using (localSpan c P).zero_mem
  | add a b ha hb iha ihb =>
    simpa only [star_add] using (localSpan c P).add_mem iha ihb
  | smul r a ha ih =>
    simpa only [star_smul] using (localSpan c P).smul_mem (star r) ih

def localStarSubalgebra (c : Cocycle G) (P : Submodule (ZMod 2) G) :
    StarSubalgebra ℂ (closedSubalgebra c) where
  carrier := localSpan c P
  zero_mem' := (localSpan c P).zero_mem
  add_mem' := (localSpan c P).add_mem
  one_mem' := shiftInAlgebra_zero c ▸ localShift_mem c P 0 P.zero_mem
  mul_mem' := localSpan_mul c P
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (localSpan c P).smul_mem r (shiftInAlgebra_zero c ▸ localShift_mem c P 0 P.zero_mem)
  star_mem' := localSpan_star c P

instance localStarSubalgebra_normedAlgebra (c : Cocycle G) (P : Submodule (ZMod 2) G) :
    NormedAlgebra ℂ (localStarSubalgebra c P) :=
  StarSubalgebra.toNormedAlgebra (localStarSubalgebra c P)

instance localStarSubalgebra_module (c : Cocycle G) (P : Submodule (ZMod 2) G) :
    Module ℂ (localStarSubalgebra c P) :=
  @Algebra.toModule ℂ (localStarSubalgebra c P) _ _
    (StarSubalgebra.algebra (localStarSubalgebra c P))

theorem localStarSubalgebra_mono (c : Cocycle G) {P Q : Submodule (ZMod 2) G} (h : P ≤ Q) :
    localStarSubalgebra c P ≤ localStarSubalgebra c Q := localSpan_mono c h

theorem localStarSubalgebra_finiteDimensional (c : Cocycle G) (P : Submodule (ZMod 2) G)
    [FiniteDimensional (ZMod 2) P] : FiniteDimensional ℂ (localStarSubalgebra c P) := by
  letI : Finite P := Module.finite_of_finite (R := ZMod 2)
  change FiniteDimensional ℂ (localSpan c P)
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun g : P => shiftInAlgebra c (g : G)))

end NonCalkinAlgebra.TwistedRegular
