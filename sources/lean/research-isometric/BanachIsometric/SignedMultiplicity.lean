import BanachIsometric.SignedJacobian
import BanachIsometric.RegularBranches
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Summing the actual signed inverse branches

The absolute-integral bound is derived from source integrability and disjointness
of the constructed measurable partition. The interchange of infinite sum and
integral is therefore justified, rather than assumed as degree data.
-/

namespace BanachIsometric

open MeasureTheory Set Function
open scoped Topology NNReal Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def signedBranchSum (f : E → E) (D : E → E →L[ℝ] E)
    (t : ℕ → Set E) (g : E → ℝ) (y : E) : ℝ :=
  ∑' n, signedBranchWeight f D (t n) g y

/-- The signed many-branch integral identity. Analytic hypotheses are only
within-differentiability and integrability on the source; countable branch
summability is a conclusion of the proof. -/
theorem integral_signedBranchSum (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (t : ℕ → Set E)
    (ht : ∀ n, MeasurableSet (t n)) (hdisj : Pairwise (Disjoint on t))
    (hcover : (⋃ n, t n) = s) (hinj : ∀ n, InjOn f (t n))
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x)
    (g : E → ℝ) (hint : IntegrableOn (fun x => (D x).det * g (f x)) s μ) :
    (∫ y, signedBranchSum f D t g y ∂μ) = ∫ x in s, (D x).det * g (f x) ∂μ := by
  have hsub (n : ℕ) : t n ⊆ s := by
    rw [← hcover]
    exact subset_iUnion t n
  have hDn (n : ℕ) : ∀ x ∈ t n, HasFDerivWithinAt f (D x) (t n) x :=
    fun x hx => (hD x (hsub n hx)).mono (hsub n)
  have hbranch (n : ℕ) : Integrable (signedBranchWeight f D (t n) g) μ :=
    (integrable_signedBranchWeight_iff μ (ht n) (hDn n) (hinj n) g).mpr
      (hint.mono_set (hsub n))
  have hnorm : Summable (fun n => ∫ y, ‖signedBranchWeight f D (t n) g y‖ ∂μ) := by
    have hh : IntegrableOn (fun x => ‖(D x).det * g (f x)‖) (⋃ n, t n) μ := by
      rw [hcover]
      exact hint.norm
    have hsum := (hasSum_integral_iUnion ht hdisj hh).summable
    simpa only [integral_norm_signedBranchWeight μ (ht _) (hDn _) (hinj _) g] using hsum
  unfold signedBranchSum
  rw [← integral_tsum_of_summable_integral_norm hbranch hnorm]
  calc
    (∑' n, ∫ y, signedBranchWeight f D (t n) g y ∂μ) =
        ∑' n, ∫ x in t n, (D x).det * g (f x) ∂μ := by
      apply tsum_congr
      intro n
      exact integral_signedBranchWeight μ (ht n) (hDn n) (hinj n) g
    _ = ∫ x in s, (D x).det * g (f x) ∂μ := by
      rw [← hcover]
      exact (integral_iUnion ht hdisj (by simpa only [hcover] using hint)).symm

/-- The branch partition and the signed integral identity are obtained from
the actual derivative field with nonzero determinant, rather than assumed as
premises. This applies to measurable regular sets of Lipschitz maps as well.
-/
theorem exists_signed_branch_integral [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {D : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hdet : ∀ x ∈ s, (D x).det ≠ 0) :
    ∃ t : ℕ → Set E,
      Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧
        (⋃ n, t n) = s ∧ (∀ n, InjOn f (t n)) ∧
        ∀ g : E → ℝ, IntegrableOn (fun x => (D x).det * g (f x)) s μ →
          (∫ y, signedBranchSum f D t g y ∂μ) =
            ∫ x in s, (D x).det * g (f x) ∂μ := by
  obtain ⟨t, hdisj, ht, hcover, hinj⟩ :=
    exists_disjoint_measurable_injective_branches μ hs hD hdet
  exact ⟨t, hdisj, ht, hcover, hinj,
    fun g hint => integral_signedBranchSum μ t ht hdisj hcover hinj hD g hint⟩

end BanachIsometric
