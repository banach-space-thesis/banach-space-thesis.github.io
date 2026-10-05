import Sigma.FunctionSpaces
import ThesisCommon.Analysis.AlmostDisjointFamily
import Mathlib.Logic.Equiv.Nat

/-! Explicit relabelling of ℕ × Bool for the two-base Boolean-measure lemmas. -/
noncomputable section
open Set Cardinal
namespace SigmaNonprimarity

def pointCode : Point ≃ ℕ := (Equiv.prodComm ℕ Bool).trans Equiv.boolProdNatEquivNat

def codedSet (A : Set Point) : Set ℕ := pointCode '' A

theorem codedSet_injective : Function.Injective codedSet :=
  Set.image_injective.mpr pointCode.injective

theorem codedSet_mono {A B : Set Point} (h : A ⊆ B) : codedSet A ⊆ codedSet B :=
  Set.image_mono h

theorem codedSet_inter (A B : Set Point) : codedSet (A ∩ B) = codedSet A ∩ codedSet B :=
  Set.image_inter pointCode.injective

theorem codedSet_diff (A B : Set Point) : codedSet (A \ B) = codedSet A \ codedSet B :=
  Set.image_diff pointCode.injective A B

theorem cylinder_injective : Function.Injective cylinder := by
  intro A B h
  ext n
  exact Set.ext_iff.mp h (n, false)

theorem cylinder_infinite {A : Set ℕ} (hA : A.Infinite) : (cylinder A).Infinite := by
  apply (hA.image (f := fun n => (n, false)) (by intro n _ m _ h; exact congrArg Prod.fst h)).mono
  rintro _ ⟨n, hn, rfl⟩
  exact hn

theorem cylinder_finite {A : Set ℕ} (hA : A.Finite) : (cylinder A).Finite := by
  have heq : cylinder A = A ×ˢ (Set.univ : Set Bool) := by ext p; simp [cylinder]
  rw [heq]
  exact hA.prod (Set.finite_univ)

theorem codedCylinder_infinite {A : Set ℕ} (hA : A.Infinite) : (codedSet (cylinder A)).Infinite :=
  (cylinder_infinite hA).image pointCode.injective.injOn

theorem codedCylinder_inter_finite {A B : Set ℕ} (h : (A ∩ B).Finite) :
    (codedSet (cylinder A) ∩ codedSet (cylinder B)).Finite := by
  rw [← codedSet_inter]
  have heq : cylinder A ∩ cylinder B = cylinder (A ∩ B) := rfl
  rw [heq]
  exact (cylinder_finite h).image pointCode

end SigmaNonprimarity
