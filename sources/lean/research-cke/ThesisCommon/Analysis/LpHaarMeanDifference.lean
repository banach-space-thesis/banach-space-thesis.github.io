import ThesisCommon.Analysis.LpHaarCoefficientFormula
import ThesisCommon.Analysis.LpHaarConvergence

/-! Exact identification of successive dyadic averages with Haar coefficients. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace ThesisCommon

theorem lpHaarCell_integral_split (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n k : ℕ) (f : IntervalLp 𝕜 p) :
    (∫ x in lpHaarCell n k, f x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
      (∫ x in lpHaarCell (n + 1) (2 * k), f x ∂(volume.restrict (Icc (0 : ℝ) 1))) +
        ∫ x in lpHaarCell (n + 1) (2 * k + 1), f x ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [← lpHaarCell_children]
  exact setIntegral_union (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)) measurableSet_Ioc
    ((Lp.memLp f).integrable p.property).integrableOn ((Lp.memLp f).integrable p.property).integrableOn

theorem lpHaarDyadicMean_difference (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp (n + 1) f - lpHaarDyadicMean 𝕜 p hp n f =
      lpHaarLevelProjection 𝕜 p n f := by
  apply Lp.ext
  have hq : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ k : Fin (2 ^ n),
      x ∈ lpHaarCell n k → lpHaarDyadicMean 𝕜 p hp n f x =
        (intervalLpDyadicRadius n : 𝕜)⁻¹ *
          ∫ y in lpHaarCell n k, f y ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
    ae_all_iff.mpr (fun k => lpHaarDyadicMean_coe 𝕜 p hp n f k)
  have hq' : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ k : Fin (2 ^ (n + 1)),
      x ∈ lpHaarCell (n + 1) k → lpHaarDyadicMean 𝕜 p hp (n + 1) f x =
        (intervalLpDyadicRadius (n + 1) : 𝕜)⁻¹ *
          ∫ y in lpHaarCell (n + 1) k, f y ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
    ae_all_iff.mpr (fun k => lpHaarDyadicMean_coe 𝕜 p hp (n + 1) f k)
  have hP : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ k : Fin (2 ^ n),
      x ∈ lpHaarCell n k → lpHaarLevelProjection 𝕜 p n f x =
        lpHaarDyadicCoefficient 𝕜 p n k f * lpHaarFunction 𝕜
          (lpHaarCell (n + 1) (2 * k)) (lpHaarCell (n + 1) (2 * k + 1)) x :=
    ae_all_iff.mpr (fun k => lpHaarLevelProjection_coe_parent 𝕜 p n k f)
  filter_upwards [hq, hq', hP, lpHaarLevelCells_cover n,
    Lp.coeFn_sub (lpHaarDyadicMean 𝕜 p hp (n + 1) f) (lpHaarDyadicMean 𝕜 p hp n f)]
    with x hx hx' hPx hcover hsub
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hcover
  let kl : Fin (2 ^ (n + 1)) := ⟨2 * k.val, by have := k.isLt; rw [pow_succ]; omega⟩
  let kr : Fin (2 ^ (n + 1)) := ⟨2 * k.val + 1, by have := k.isLt; rw [pow_succ]; omega⟩
  have hchild : x ∈ lpHaarCell (n + 1) (2 * k) ∪ lpHaarCell (n + 1) (2 * k + 1) := by
    rw [lpHaarCell_children]
    exact hxk
  have hr : (intervalLpDyadicRadius n : 𝕜) ≠ 0 := by
    exact_mod_cast (intervalLpDyadicRadius_pos n).ne'
  have hr' : (intervalLpDyadicRadius (n + 1) : 𝕜) = (intervalLpDyadicRadius n : 𝕜) / 2 := by
    rw [lpHaarRadius_succ]
    push_cast
    rfl
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hx k hxk, hPx k hxk, lpHaarDyadicCoefficient_apply_integrals 𝕜 p n k k.isLt,
    lpHaarCell_integral_split 𝕜 p n k]
  rcases hchild with hleft | hright
  · have hnot : x ∉ lpHaarCell (n + 1) (2 * k + 1) := fun h =>
      Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)) hleft h
    rw [hx' kl hleft]
    simp only [kl, hr', lpHaarFunction, Pi.sub_apply, indicator_of_mem hleft,
      indicator_of_notMem hnot, sub_zero, mul_one]
    field_simp
    <;> ring
  · have hnot : x ∉ lpHaarCell (n + 1) (2 * k) := fun h =>
      Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel (n + 1) (by omega)) h hright
    rw [hx' kr hright]
    simp only [kr, hr', lpHaarFunction, Pi.sub_apply, indicator_of_notMem hnot,
      indicator_of_mem hright, zero_sub, mul_neg, mul_one]
    field_simp
    <;> ring

theorem lpHaarDyadicMean_difference_operator (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) :
    lpHaarDyadicMean 𝕜 p hp (n + 1) - lpHaarDyadicMean 𝕜 p hp n = lpHaarLevelProjection 𝕜 p n := by
  apply ContinuousLinearMap.ext
  intro f
  exact lpHaarDyadicMean_difference 𝕜 p hp n f

theorem lpHaarDyadicMean_eq_partialSum (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (N : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp N f = lpHaarDyadicMean 𝕜 p hp 0 f +
      ∑ n ∈ Finset.range N, lpHaarLevelProjection 𝕜 p n f := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih,
        ← lpHaarDyadicMean_difference 𝕜 p hp N f]
      abel

theorem lpHaar_levelPartialSum_tendsto (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (f : IntervalLp 𝕜 p) :
    Tendsto (fun N => lpHaarDyadicMean 𝕜 p hp 0 f +
      ∑ n ∈ Finset.range N, ∑ k : Fin (2 ^ n),
        lpHaarDyadicCoefficient 𝕜 p n k f • lpHaarDyadic 𝕜 p n k) atTop (𝓝 f) := by
  simp_rw [← lpHaarLevelProjection_apply, ← lpHaarDyadicMean_eq_partialSum 𝕜 p hp]
  exact lpHaarDyadicMean_tendsto 𝕜 p hp f

end ThesisCommon
