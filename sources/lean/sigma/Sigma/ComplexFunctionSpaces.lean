import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Sigma.FunctionSpaces
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! Concrete sup-norm spaces from Sections 3.1 and 3.3. False/true encode 0/1.
The definitions retain the constant function (and hence the compactification point).
-/
noncomputable section
namespace SigmaNonprimarity
open scoped BoundedContinuousFunction

abbrev ComplexAmbient := Point →ᵇ ℂ

def complexCharacteristic (s : Set Point) : ComplexAmbient := by
  classical
  exact BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => if p ∈ s then 1 else 0) 1 (by intro p; dsimp; split_ifs <;> norm_num)

@[simp] theorem complexCharacteristic_apply (s : Set Point) (p : Point) :
    complexCharacteristic s p = @ite ℂ (p ∈ s) (Classical.propDecidable _) 1 0 := rfl

/-- ComplexJL(B) is the closed span inside the actual bounded function space. -/
def ComplexJL (B : Set (Set Point)) : Submodule ℂ ComplexAmbient :=
  (Submodule.span ℂ
    ({f | ∃ p : Point, f = complexCharacteristic {p}} ∪
      complexCharacteristic '' B ∪ {complexCharacteristic Set.univ})).topologicalClosure

/-- The cylinder copy ComplexJL(A) uses whole finite fibres, as specified in Section 3.3. -/
def ComplexCylinderJL (A : Set (Set Point)) : Submodule ℂ ComplexAmbient :=
  (Submodule.span ℂ
    ({f | ∃ n : ℕ, f = complexCharacteristic (cylinder {n})} ∪
      complexCharacteristic '' A ∪ {complexCharacteristic Set.univ})).topologicalClosure

instance (B : Set (Set Point)) : CompleteSpace (ComplexJL B) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance (A : Set (Set Point)) : CompleteSpace (ComplexCylinderJL A) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Interchange the two coordinates of each cylinder. -/
def complexFlip : ComplexAmbient →L[ℂ] ComplexAmbient :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        (fun p => f (p.1, !p.2)) ‖f‖ (fun p => f.norm_coe_le_norm _)
      map_add' := by intros; ext p; rfl
      map_smul' := by intros; ext p; rfl }
    1 (by
      intro f
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
        (fun p => f.norm_coe_le_norm (p.1, !p.2)))

@[simp] theorem complexFlip_apply (f : ComplexAmbient) (p : Point) : complexFlip f p = f (p.1, !p.2) := rfl

theorem complexFlip_complexFlip (f : ComplexAmbient) : complexFlip (complexFlip f) = f := by
  ext p
  simp

/-- The averaging projection of Section 3.3, defined on the ambient sup-norm space. -/
def complexAverage : ComplexAmbient →L[ℂ] ComplexAmbient :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ ComplexAmbient + complexFlip)

@[simp] theorem complexAverage_apply (f : ComplexAmbient) (p : Point) :
    complexAverage f p = (f p + f (p.1, !p.2)) / 2 := by
  change (1 / 2 : ℂ) * (f p + f (p.1, !p.2)) = _
  ring

theorem complexAverage_idempotent (f : ComplexAmbient) : complexAverage (complexAverage f) = complexAverage f := by
  ext ⟨n, b⟩
  simp only [complexAverage_apply, Bool.not_not]
  ring

theorem complexAverage_norm_le (f : ComplexAmbient) : ‖complexAverage f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro p
  rw [complexAverage_apply, norm_div, Complex.norm_ofNat]
  have h := norm_add_le (f p) (f (p.1, !p.2))
  have h₁ := f.norm_coe_le_norm p
  have h₂ := f.norm_coe_le_norm (p.1, !p.2)
  linarith

/-- The kernel condition is exactly the antisymmetry condition in equation (2). -/
theorem complexAverage_eq_zero_iff (f : ComplexAmbient) :
    complexAverage f = 0 ↔ ∀ n, f (n, false) = -f (n, true) := by
  constructor
  · intro h n
    have hn := congrArg (fun g : ComplexAmbient => g (n, false)) h
    simp only [complexAverage_apply, Bool.not_false] at hn
    change (f (n, false) + f (n, true)) / 2 = 0 at hn
    have hsum : f (n, false) + f (n, true) = 0 :=
      (div_eq_zero_iff.mp hn).resolve_right (by norm_num)
    exact eq_neg_of_add_eq_zero_left hsum
  · intro h
    ext ⟨n, b⟩
    cases b <;> simp [h n]

/-- Fixed points are exactly the functions constant on each cylinder. -/
theorem complexAverage_eq_self_iff (f : ComplexAmbient) :
    complexAverage f = f ↔ ∀ n, f (n, false) = f (n, true) := by
  constructor
  · intro h n
    have hn := congrArg (fun g : ComplexAmbient => g (n, false)) h
    simp only [complexAverage_apply, Bool.not_false] at hn
    linear_combination -2 * hn
  · intro h
    ext ⟨n, b⟩
    cases b <;> simp [h n]

def complexAntisymmetricJL (B : Set (Set Point)) : Submodule ℂ ComplexAmbient :=
  ComplexJL B ⊓ LinearMap.ker complexAverage.toLinearMap

instance (B : Set (Set Point)) : CompleteSpace (complexAntisymmetricJL B) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (isClosed_eq complexAverage.continuous continuous_const)).completeSpace_coe

/-- The paper's two candidate summands, before the transfinite choice of families. -/
abbrev ComplexCandidateX (B Atilde : Set (Set Point)) := ComplexCylinderJL Atilde × complexAntisymmetricJL B

end SigmaNonprimarity


