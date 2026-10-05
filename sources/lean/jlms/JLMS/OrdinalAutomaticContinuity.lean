import JLMS.OrdinalSpaceReduction
import JLMS.OgdenInitialAutomaticContinuity

/-!
# The final ordinal-space reduction in Section 9

Ogden's initial-ordinal theorem, the finite-dimensional case, Johnson's
square-space theorem and finite-power transfer are all proved. The sole
remaining input here is the stated ordinal-space classification consequence.
It remains explicit until its construction is completed.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]

theorem theorem_1_3_of_classification (α : Ordinal.{u})
    (hα : OrdinalSpaceReduction 𝕜 α) : Theorem_1_3.{u, v, w} 𝕜 α :=
  theorem_1_3_of_ordinalSpaceReduction α hα
    (fun _ hc hu => theorem_1_3_initialOrdinal hc hu)

theorem theorem_1_3_initialOrdinal_finiteMultiple {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (n : ℕ) :
    Theorem_1_3.{u, v, w} 𝕜 (c.ord * ((n + 1 : ℕ) : Ordinal)) := by
  apply theorem_1_3_of_classification
  exact Or.inr (Or.inr ⟨c, hc, hu, n, ⟨ContinuousLinearEquiv.refl 𝕜 _⟩⟩)

end JLMS
