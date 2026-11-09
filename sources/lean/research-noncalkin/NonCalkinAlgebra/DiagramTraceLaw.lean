import NonCalkinAlgebra.ProductTraceWeights

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
open Refinement
universe u

section Universal
variable {C D E : Type u} {P : C → Type u} {Q : D → Type u} {R : E → Type u}

/-- Trace compatibility is independent of the enumerations of the finite sets. -/
def UniversalWeightLaw (f : Refinement P Q) (w : C → ℝ) (v : D → ℝ) : Prop :=
  ∀ (FD : Fintype D) (FK : ∀ d, Fintype (f.Copies d)),
    @Refinement.WeightLaw C D P Q FD f FK w v

theorem UniversalWeightLaw.of_law (f : Refinement P Q) [FD : Fintype D]
    [FK : ∀ d, Fintype (f.Copies d)] (w : C → ℝ) (v : D → ℝ)
    (h : f.WeightLaw w v) : UniversalWeightLaw f w v := by
  intro fd fk
  have hd : fd = FD := Subsingleton.elim _ _
  have hk : fk = FK := Subsingleton.elim _ _
  subst fd
  subst fk
  exact h

theorem UniversalWeightLaw.law (f : Refinement P Q) [FD : Fintype D]
    [FK : ∀ d, Fintype (f.Copies d)] (w : C → ℝ) (v : D → ℝ)
    (h : UniversalWeightLaw f w v) : f.WeightLaw w v :=
  h FD FK

theorem UniversalWeightLaw.identity [Fintype C] (w : C → ℝ) :
    UniversalWeightLaw (identity P) w w := by
  apply UniversalWeightLaw.of_law
  classical
  intro c
  change (∑ d : C, ∑ _ : PUnit.{u+1}, if d = c then w d else 0) = w c
  simp [Fintype.sum_ite_eq', Fintype.sum_unique]

theorem UniversalWeightLaw.trans
    [Fintype C] [Fintype D] [Fintype E]
    [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)] [∀ c, Nonempty (P c)]
    [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
    [∀ e, Fintype (R e)] [∀ e, DecidableEq (R e)]
    (f : Refinement P Q) (g : Refinement Q R)
    [∀ d, Fintype (f.Copies d)] [∀ e, Fintype (g.Copies e)]
    (w : C → ℝ) (v : D → ℝ) (z : E → ℝ)
    (hf : UniversalWeightLaw f w v) (hg : UniversalWeightLaw g v z) :
    UniversalWeightLaw (f.trans g) w z := by
  apply UniversalWeightLaw.of_law
  apply weightLaw_of_weightedBlockTrace_map
  intro x
  rw [then_hom]
  exact (weightedBlockTrace_map g v z (hg.law g v z) (f.hom x)).trans
    (weightedBlockTrace_map f w v (hf.law f w v) x)

end Universal

namespace RootedBlockDiagram
variable (D : RootedBlockDiagram.{u}) (w : ∀ n, D.Color n → ℝ)

theorem universalWeightLaw_path
    (hw : ∀ n, UniversalWeightLaw (D.step n) (w n) (w (n + 1)))
    (a b : ℕ) (h : a ≤ b) :
    UniversalWeightLaw (D.path a b h) (w a) (w b) := by
  induction b, h using Nat.le_induction with
  | base =>
    rw [path_self]
    exact UniversalWeightLaw.identity (w a)
  | succ b h ih =>
    classical
    rw [D.path_succ a b h]
    letI (n : ℕ) (c : D.Color n) : Fintype (D.Row n c) := Fintype.ofFinite _
    letI (c : D.Color (b+1)) : Fintype ((D.step b).Copies c) := by
      letI := finite_copies (D.step b) c
      exact Fintype.ofFinite _
    exact UniversalWeightLaw.trans (D.path a b h) (D.step b) (w a) (w b) (w (b+1))
      ih (hw b)

end RootedBlockDiagram
end NonCalkinAlgebra.FiniteBlockRefinement
