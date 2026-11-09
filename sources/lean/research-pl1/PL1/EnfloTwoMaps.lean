import PL1.EnfloSum

/-!
# Two actual L1-valued maps cannot jointly be bounded below

Both maps have the same genuine interval L1 domain. Their two coordinates are
placed in the genuine ell1 sum, so the existing coordinatewise dyadic maximum
criterion applies without a direct-sum permanence assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace PL1.EnfloBush
open IntervalModel

section PairMap
variable {F Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def pairMap (A B : F →L[ℝ] Y) : F →L[ℝ] L1Sum Y :=
  (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => Y) 1 0).comp A +
    (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => Y) 1 1).comp B

@[simp] theorem pairMap_apply_zero (A B : F →L[ℝ] Y) (f : F) :
    pairMap A B f 0 = A f := by
  simp [pairMap]

@[simp] theorem pairMap_apply_one (A B : F →L[ℝ] Y) (f : F) :
    pairMap A B f 1 = B f := by
  simp [pairMap]

theorem pairMap_apply_other (A B : F →L[ℝ] Y) (f : F) (i : ℕ)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) : pairMap A B f i = 0 := by
  simp [pairMap, hi0, hi1]

/-- The codomain norm is the sum of the two original norms. -/
theorem norm_pairMap (A B : F →L[ℝ] Y) (f : F) :
    ‖pairMap A B f‖ = ‖A f‖ + ‖B f‖ := by
  classical
  apply le_antisymm
  · change ‖(lp.single 1 (0 : ℕ) (A f) : L1Sum Y) + lp.single 1 (1 : ℕ) (B f)‖ ≤ _
    exact (norm_add_le _ _).trans_eq (by rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num)])
  · have h := (L1Sum.summable_norm (pairMap A B f)).sum_le_tsum ({0,1} : Finset ℕ)
      (fun i _ => norm_nonneg _)
    simpa only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)),
      Finset.sum_singleton, pairMap_apply_zero, pairMap_apply_one, ← L1Sum.norm_eq_tsum] using h
end PairMap

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma dyadicVanishing_zero : DyadicVanishing (0 : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) := by
  have hz (m : ℕ) : dyadicMaxMass (0 : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) m = 0 :=
    le_antisymm (by simpa using dyadicMaxMass_le (0 : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) m)
      (dyadicMaxMass_nonneg _ _)
  change Tendsto (fun m => dyadicMaxMass (0 : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) m) atTop (𝓝 0)
  simp only [hz]
  exact tendsto_const_nhds

/-- The real and imaginary parts of a hypothetical embedding may be tested
jointly, even when neither part alone is bounded below. -/
theorem not_boundedBelow_two_maps [SFinite μ]
    (A B : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ)
    (hA : DyadicVanishing A) (hB : DyadicVanishing B)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ f, c*‖f‖ ≤ ‖A f‖ + ‖B f‖) : False := by
  apply not_boundedBelow_sum_of_coordinates μ (pairMap A B) ?_ hc
    (fun f => by rw [norm_pairMap]; exact hlower f)
  intro i
  by_cases hi0 : i = 0
  · subst i
    have he : sumCoordinate μ (pairMap A B) 0 = A := by apply ContinuousLinearMap.ext; intro f; exact pairMap_apply_zero A B f
    rwa [he]
  by_cases hi1 : i = 1
  · subst i
    have he : sumCoordinate μ (pairMap A B) 1 = B := by apply ContinuousLinearMap.ext; intro f; exact pairMap_apply_one A B f
    rwa [he]
  have he : sumCoordinate μ (pairMap A B) i = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact pairMap_apply_other A B f i hi0 hi1
  rw [he]
  exact dyadicVanishing_zero μ

end PL1.EnfloBush

