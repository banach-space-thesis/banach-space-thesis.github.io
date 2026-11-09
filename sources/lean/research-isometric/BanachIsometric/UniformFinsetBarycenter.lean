import Mathlib.Analysis.Convex.StdSimplex

/-! The uniform barycenter on a nonempty finite set has actual simplex
coordinates. These are the centers for the finite-star contractions. -/

noncomputable section
namespace BanachIsometric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def uniformFinsetBarycenter (s : Finset ι) : ι → ℝ :=
  fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0

theorem uniformFinsetBarycenter_mem_stdSimplex {s : Finset ι} (hs : s.Nonempty) :
    uniformFinsetBarycenter s ∈ stdSimplex ℝ ι := by
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  constructor
  · intro i
    by_cases hi : i ∈ s
    · simpa only [uniformFinsetBarycenter, if_pos hi] using (inv_pos.mpr hcard).le
    · simp [uniformFinsetBarycenter, hi]
  · calc
      ∑ i, uniformFinsetBarycenter s i = ∑ i ∈ s, uniformFinsetBarycenter s i :=
        (Finset.sum_subset (Finset.subset_univ s)
          (fun i _ hi => by simp [uniformFinsetBarycenter, hi])).symm
      _ = ∑ _i ∈ s, (s.card : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun i hi => if_pos hi)
      _ = 1 := by simp [nsmul_eq_mul, hcard.ne']

end BanachIsometric
