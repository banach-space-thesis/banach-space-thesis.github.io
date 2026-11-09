import NonCalkinAlgebra.ClosedTwistedAlgebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TwistedRegular
open BinaryPhase
universe u
variable {G : Type u} [AddCommGroup G]

/-- Literal finite complex linear combinations of the signed shifts. -/
def finiteSpan (c : Cocycle G) :
    Submodule ℂ (SquareSummable G →L[ℂ] SquareSummable G) :=
  Submodule.span ℂ (Set.range (shift c))

theorem shift_mem_finiteSpan (c : Cocycle G) (g : G) : shift c g ∈ finiteSpan c :=
  Submodule.subset_span ⟨g, rfl⟩

theorem finiteSpan_mul (c : Cocycle G)
    {a b : SquareSummable G →L[ℂ] SquareSummable G}
    (ha : a ∈ finiteSpan c) (hb : b ∈ finiteSpan c) : a * b ∈ finiteSpan c := by
  change a ∈ Submodule.span ℂ (Set.range (shift c)) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    change b ∈ Submodule.span ℂ (Set.range (shift c)) at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, rfl⟩ := hb
      rw [shift_mul]
      exact (finiteSpan c).smul_mem _ (shift_mem_finiteSpan c _)
    | zero => simpa only [mul_zero] using (finiteSpan c).zero_mem
    | add b d hb hd ihb ihd =>
      simpa only [mul_add] using (finiteSpan c).add_mem ihb ihd
    | smul r b hb ih =>
      simpa only [mul_smul_comm] using (finiteSpan c).smul_mem r ih
  | zero => simpa only [zero_mul] using (finiteSpan c).zero_mem
  | add a d ha hd iha ihd =>
    simpa only [add_mul] using (finiteSpan c).add_mem iha ihd
  | smul r a ha ih =>
    simpa only [smul_mul_assoc] using (finiteSpan c).smul_mem r ih

theorem finiteSpan_star (c : Cocycle G)
    {a : SquareSummable G →L[ℂ] SquareSummable G} (ha : a ∈ finiteSpan c) :
    star a ∈ finiteSpan c := by
  change a ∈ Submodule.span ℂ (Set.range (shift c)) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    rw [star_shift]
    exact (finiteSpan c).smul_mem _ (shift_mem_finiteSpan c _)
  | zero => simpa only [star_zero] using (finiteSpan c).zero_mem
  | add a b ha hb iha ihb =>
    simpa only [star_add] using (finiteSpan c).add_mem iha ihb
  | smul r a ha ih =>
    simpa only [star_smul] using (finiteSpan c).smul_mem (star r) ih

def finiteStarSubalgebra (c : Cocycle G) :
    StarSubalgebra ℂ (SquareSummable G →L[ℂ] SquareSummable G) where
  carrier := finiteSpan c
  zero_mem' := (finiteSpan c).zero_mem
  add_mem' := (finiteSpan c).add_mem
  one_mem' := shift_zero c ▸ shift_mem_finiteSpan c 0
  mul_mem' := finiteSpan_mul c
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (finiteSpan c).smul_mem r (shift_zero c ▸ shift_mem_finiteSpan c 0)
  star_mem' := finiteSpan_star c

theorem polynomialSubalgebra_eq (c : Cocycle G) :
    polynomialSubalgebra c = finiteStarSubalgebra c := by
  apply le_antisymm
  · exact StarAlgebra.adjoin_le (fun _ h => Submodule.subset_span h)
  · intro a ha
    exact (Submodule.span_le.mpr
      (StarAlgebra.subset_adjoin ℂ (Set.range (shift c))) :
      finiteSpan c ≤ (polynomialSubalgebra c).toSubalgebra.toSubmodule) ha

/-- Every element of the closed algebra is a norm limit of finite sums of
shifts, rather than an unspecified word in a universal presentation. -/
theorem coe_closedSubalgebra_eq_closure (c : Cocycle G) :
    (closedSubalgebra c : Set (SquareSummable G →L[ℂ] SquareSummable G)) =
      closure (finiteSpan c : Set (SquareSummable G →L[ℂ] SquareSummable G)) := by
  simp only [closedSubalgebra, StarSubalgebra.topologicalClosure_coe,
    polynomialSubalgebra_eq]
  rfl

end NonCalkinAlgebra.TwistedRegular
