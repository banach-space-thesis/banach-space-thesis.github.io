import Sigma.JLDual
import ThesisCommon.Analysis.UltrafilterCharge
import ThesisCommon.Analysis.ChargeSeries

/-! Full-power-set representatives of all compactum atoms, including infinity.
The infinity ultrafilter is free and avoids the almost-disjoint family. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity
attribute [local instance] Classical.propDecidable

def atomCharge {B : Set (Set Point)} (hB : AlmostDisjoint B) (Uinf : Ultrafilter Point) :
    AUCompactum B → UnitCharge Point := fun p =>
  OnePoint.rec (ultrafilterCharge Uinf)
    (fun q => match q with
      | .inl n => diracCharge n
      | .inr b => ultrafilterCharge (freeUltrafilterOn b.val (hB.1 b.val b.property))) p

@[simp] theorem atomCharge_infty {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) : atomCharge hB Uinf OnePoint.infty = ultrafilterCharge Uinf := rfl

@[simp] theorem atomCharge_base {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (n : Point) :
    atomCharge hB Uinf (↑(Sum.inl n : MrowkaBase B)) = diracCharge n := rfl

@[simp] theorem atomCharge_family {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (b : B) :
    atomCharge hB Uinf (↑(Sum.inr b : MrowkaBase B)) =
      ultrafilterCharge (freeUltrafilterOn b.val (hB.1 b.val b.property)) := rfl

theorem atomCharge_univ {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (p : AUCompactum B) : atomCharge hB Uinf p Set.univ = 1 := by
  induction p using OnePoint.rec with
  | infty => exact ultrafilterCharge_univ _
  | coe q => cases q with
    | inl n => exact ultrafilterCharge_univ (pure n)
    | inr b => exact ultrafilterCharge_univ _

theorem atomCharge_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (hUinf : (Uinf : Filter Point) ≤ Filter.cofinite)
    (n : Point) (p : AUCompactum B) :
    atomCharge hB Uinf p {n} = singletonFunction hB n p := by
  induction p using OnePoint.rec with
  | infty =>
    rw [atomCharge_infty, ultrafilterCharge_finite Uinf hUinf (Set.finite_singleton n)]
    simp
  | coe q =>
    cases q with
    | inl m => simp
    | inr b =>
      rw [atomCharge_family, ultrafilterCharge_finite _ (freeUltrafilterOn_le_cofinite _ _)
        (Set.finite_singleton n)]
      simp

theorem atomCharge_family_set {B : Set (Set Point)} (hB : AlmostDisjoint B)
    (Uinf : Ultrafilter Point) (havoid : ∀ b ∈ B, b ∉ Uinf)
    (b : B) (p : AUCompactum B) : atomCharge hB Uinf p b.val = tailFunction hB b p := by
  induction p using OnePoint.rec with
  | infty => simp [havoid b.val b.property]
  | coe q =>
    cases q with
    | inl n =>
      have h := congrArg (fun f : Ambient => f n) (restrict_tailFunction hB b)
      simpa only [restrictToBase_apply, characteristic_apply, atomCharge_base, diracCharge_apply] using h.symm
    | inr c =>
      rw [atomCharge_family, tailFunction_inr]
      by_cases hcb : c = b
      · subst c
        simp [mem_freeUltrafilterOn]
      · rw [if_neg hcb]
        exact ultrafilterCharge_eq_zero_of_finite_inter _ (freeUltrafilterOn_le_cofinite _ _)
          (mem_freeUltrafilterOn _ _) (hB.2 c.val c.property b.val b.property
            (fun h => hcb (Subtype.ext h)))

end SigmaNonprimarity
