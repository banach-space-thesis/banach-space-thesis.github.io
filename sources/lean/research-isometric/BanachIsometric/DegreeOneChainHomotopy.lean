import Mathlib.Algebra.Homology.Homotopy

/-! Construct a genuine categorical chain homotopy from degree-one maps
and their boundary equations, treating degree zero explicitly. -/

noncomputable section
namespace BanachIsometric

open CategoryTheory HomologicalComplex

variable {V : Type*} [Category V] [Preadditive V]
variable {C D : ChainComplex V ℕ} {f g : C ⟶ D}

def degreeOneHomotopyComponents (h : ∀ n, C.X n ⟶ D.X (n + 1))
    (i j : ℕ) : C.X i ⟶ D.X j :=
  if w : i + 1 = j then h i ≫ eqToHom (congrArg D.X w) else 0

theorem degreeOneHomotopyComponents_succ (h : ∀ n, C.X n ⟶ D.X (n + 1)) (n : ℕ) :
    degreeOneHomotopyComponents h n (n + 1) = h n := by
  simp [degreeOneHomotopyComponents]

def chainHomotopyOfDegreeOne (h : ∀ n, C.X n ⟶ D.X (n + 1))
    (hzero : f.f 0 = h 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n + 1) = C.d (n + 1) n ≫ h n +
      h (n + 1) ≫ D.d (n + 2) (n + 1) + g.f (n + 1)) : Homotopy f g where
  hom := degreeOneHomotopyComponents h
  zero i j hij := by
    have hw : i + 1 ≠ j := by simpa only [ComplexShape.down_Rel] using hij
    simp only [degreeOneHomotopyComponents, dif_neg hw]
  comm i := by
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
      degreeOneHomotopyComponents_succ]
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp [ChainComplex.next_nat_zero, ComplexShape.down_Rel]),
        zero_add]
      exact hzero
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
        degreeOneHomotopyComponents_succ]
      exact hsucc n

end BanachIsometric
