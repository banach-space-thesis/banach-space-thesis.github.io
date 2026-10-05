import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Concrete sup-norm spaces from Sections 3.1 and 3.3. False/true encode 0/1.
The definitions retain the constant function (and hence the compactification point).
-/
noncomputable section
namespace SigmaNonprimarity
open scoped BoundedContinuousFunction

abbrev Point := ℕ × Bool
abbrev Ambient := Point →ᵇ ℝ

def characteristic (s : Set Point) : Ambient := by
  classical
  exact BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun p => if p ∈ s then 1 else 0) 1 (by intro p; dsimp; split_ifs <;> norm_num)

@[simp] theorem characteristic_apply (s : Set Point) (p : Point) :
    characteristic s p = @ite ℝ (p ∈ s) (Classical.propDecidable _) 1 0 := rfl

def AlmostDisjoint (B : Set (Set Point)) : Prop :=
  (∀ b ∈ B, b.Infinite) ∧ ∀ b ∈ B, ∀ c ∈ B, b ≠ c → (b ∩ c).Finite

def cylinder (s : Set ℕ) : Set Point := {p | p.1 ∈ s}

/-- A subset picks exactly one of the two points in each specified fibre. -/
def Splits (s : Set ℕ) (b : Set Point) : Prop :=
  b ⊆ cylinder s ∧ ∀ n ∈ s, ((n, false) ∈ b ↔ (n, true) ∉ b)

/-- JL(B) is the closed span inside the actual bounded function space. -/
def JL (B : Set (Set Point)) : Submodule ℝ Ambient :=
  (Submodule.span ℝ
    ({f | ∃ p : Point, f = characteristic {p}} ∪
      characteristic '' B ∪ {characteristic Set.univ})).topologicalClosure

/-- The cylinder copy JL(A) uses whole finite fibres, as specified in Section 3.3. -/
def CylinderJL (A : Set (Set Point)) : Submodule ℝ Ambient :=
  (Submodule.span ℝ
    ({f | ∃ n : ℕ, f = characteristic (cylinder {n})} ∪
      characteristic '' A ∪ {characteristic Set.univ})).topologicalClosure

instance (B : Set (Set Point)) : CompleteSpace (JL B) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance (A : Set (Set Point)) : CompleteSpace (CylinderJL A) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Interchange the two coordinates of each cylinder. -/
def flip : Ambient →L[ℝ] Ambient :=
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

@[simp] theorem flip_apply (f : Ambient) (p : Point) : flip f p = f (p.1, !p.2) := rfl

theorem flip_flip (f : Ambient) : flip (flip f) = f := by
  ext p
  simp

/-- The averaging projection of Section 3.3, defined on the ambient sup-norm space. -/
def average : Ambient →L[ℝ] Ambient :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Ambient + flip)

@[simp] theorem average_apply (f : Ambient) (p : Point) :
    average f p = (f p + f (p.1, !p.2)) / 2 := by
  change (1 / 2 : ℝ) * (f p + f (p.1, !p.2)) = _
  ring

theorem average_idempotent (f : Ambient) : average (average f) = average f := by
  ext ⟨n, b⟩
  simp only [average_apply, Bool.not_not]
  ring

theorem average_norm_le (f : Ambient) : ‖average f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro p
  rw [average_apply, norm_div, Real.norm_ofNat]
  have h := norm_add_le (f p) (f (p.1, !p.2))
  have h₁ := f.norm_coe_le_norm p
  have h₂ := f.norm_coe_le_norm (p.1, !p.2)
  linarith

/-- The kernel condition is exactly the antisymmetry condition in equation (2). -/
theorem average_eq_zero_iff (f : Ambient) :
    average f = 0 ↔ ∀ n, f (n, false) = -f (n, true) := by
  constructor
  · intro h n
    have hn := congrArg (fun g : Ambient => g (n, false)) h
    simp only [average_apply, Bool.not_false] at hn
    change (f (n, false) + f (n, true)) / 2 = 0 at hn
    linarith
  · intro h
    ext ⟨n, b⟩
    cases b <;> simp [h n]

/-- Fixed points are exactly the functions constant on each cylinder. -/
theorem average_eq_self_iff (f : Ambient) :
    average f = f ↔ ∀ n, f (n, false) = f (n, true) := by
  constructor
  · intro h n
    have hn := congrArg (fun g : Ambient => g (n, false)) h
    simp only [average_apply, Bool.not_false] at hn
    linarith
  · intro h
    ext ⟨n, b⟩
    cases b <;> simp [h n]

def antisymmetricJL (B : Set (Set Point)) : Submodule ℝ Ambient :=
  JL B ⊓ LinearMap.ker average.toLinearMap

instance (B : Set (Set Point)) : CompleteSpace (antisymmetricJL B) :=
  ((Submodule.isClosed_topologicalClosure _).inter
    (isClosed_eq average.continuous continuous_const)).completeSpace_coe

/-- The paper's two candidate summands, before the transfinite choice of families. -/
abbrev CandidateX (B Atilde : Set (Set Point)) := CylinderJL Atilde × antisymmetricJL B

end SigmaNonprimarity
