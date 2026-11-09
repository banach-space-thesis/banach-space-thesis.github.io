import SurveyStatements.P5RademacherL2

/-! Actual scalar Rademacher vectors at every Lp exponent have pointwise
norm at most one. The proof uses disjoint dyadic cells, not an assumed
probabilistic representation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Classical

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem scalarLp_sum_ae {ι : Type*} (F : Finset ι)
    (f : ι → Lp 𝕜 p unitIntervalMeasure) :
    ⇑(∑ i ∈ F, f i) =ᵐ[unitIntervalMeasure] fun x => ∑ i ∈ F, f i x := by
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero 𝕜 p unitIntervalMeasure
  | @insert i F hi ih =>
      simpa only [Finset.sum_insert hi, Pi.add_apply] using
        (Lp.coeFn_add (f i) (∑ j ∈ F, f j)).trans
          ((EventuallyEq.refl (ae unitIntervalMeasure) (f i) :
            (f i : ℝ → 𝕜) =ᵐ[unitIntervalMeasure] f i).add ih)

def dyadicRademacherLp (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) : Lp 𝕜 p unitIntervalMeasure :=
  ∑ k : Fin (2 ^ n), dyadicHaar 𝕜 p ⟨n, k⟩

def dyadicRademacherFunction (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) (x : ℝ) : 𝕜 :=
  ∑ k : Fin (2 ^ n), P5Support.lpHaarFunction 𝕜
    (P5Support.lpHaarCell (n + 1) (2 * k.val))
    (P5Support.lpHaarCell (n + 1) (2 * k.val + 1)) x

theorem dyadicRademacherLp_ae (n : ℕ) :
    dyadicRademacherLp 𝕜 p n =ᵐ[unitIntervalMeasure]
      dyadicRademacherFunction 𝕜 n := by
  have hhaar (k : Fin (2 ^ n)) : dyadicHaar 𝕜 p ⟨n, k⟩ =ᵐ[unitIntervalMeasure]
      P5Support.lpHaarFunction 𝕜 (P5Support.lpHaarCell (n + 1) (2 * k.val))
        (P5Support.lpHaarCell (n + 1) (2 * k.val + 1)) := by
    rw [dyadicHaar_eq_support]
    exact P5Support.lpHaarVector_coe _ _ measurableSet_Ioc measurableSet_Ioc
  filter_upwards [scalarLp_sum_ae Finset.univ
    (fun k : Fin (2 ^ n) => dyadicHaar 𝕜 p ⟨n, k⟩), ae_all_iff.mpr hhaar]
      with x hx hh
  exact hx.trans (Finset.sum_congr rfl (fun k _ => hh k))

theorem norm_dyadicRademacherFunction_le (n : ℕ) (x : ℝ) :
    ‖dyadicRademacherFunction 𝕜 n x‖ ≤ 1 := by
  let v (k : Fin (2 ^ n)) := P5Support.lpHaarFunction 𝕜
    (P5Support.lpHaarCell (n + 1) (2 * k.val))
    (P5Support.lpHaarCell (n + 1) (2 * k.val + 1)) x
  have hzero (k : Fin (2 ^ n)) (hx : x ∉ P5Support.lpHaarCell n k.val) : v k = 0 := by
    have hc := P5Support.lpHaarCell_children n k.val
    have hl : x ∉ P5Support.lpHaarCell (n + 1) (2 * k.val) := by
      intro h
      exact hx (hc ▸ Or.inl h)
    have hr : x ∉ P5Support.lpHaarCell (n + 1) (2 * k.val + 1) := by
      intro h
      exact hx (hc ▸ Or.inr h)
    simp [v, P5Support.lpHaarFunction, hl, hr]
  by_cases hx : ∃ k : Fin (2 ^ n), x ∈ P5Support.lpHaarCell n k.val
  · obtain ⟨k, hk⟩ := hx
    have hs : (∑ j : Fin (2 ^ n), v j) = v k := by
      apply Finset.sum_eq_single k
      · intro j _ hj
        apply hzero
        intro hmem
        exact Set.disjoint_left.mp
          (P5Support.lpHaarCell_disjoint_sameLevel n
            (fun h => hj (Fin.ext h))) hmem hk
      · simp
    change ‖∑ j : Fin (2 ^ n), v j‖ ≤ 1
    rw [hs]
    change ‖P5Support.lpHaarFunction 𝕜
      (P5Support.lpHaarCell (n + 1) (2 * k.val))
      (P5Support.lpHaarCell (n + 1) (2 * k.val + 1)) x‖ ≤ 1
    rw [P5Support.lpHaarFunction_norm _ _
      (P5Support.lpHaarCell_disjoint_sameLevel (n + 1) (by omega)),
      P5Support.lpHaarCell_children]
    simp [hk]
  · have hz : (∑ j : Fin (2 ^ n), v j) = 0 :=
      Finset.sum_eq_zero (fun j _ => hzero j (fun h => hx ⟨j, h⟩))
    change ‖∑ j : Fin (2 ^ n), v j‖ ≤ 1
    rw [hz, norm_zero]
    exact zero_le_one

theorem dyadicRademacherLp_bound (n : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖dyadicRademacherLp 𝕜 p n x‖ ≤ 1 := by
  filter_upwards [dyadicRademacherLp_ae (𝕜 := 𝕜) (p := p) n] with x hx
  rw [hx]
  exact norm_dyadicRademacherFunction_le n x

theorem norm_dyadicRademacherLp_le (n : ℕ) :
    ‖dyadicRademacherLp 𝕜 p n‖ ≤ 1 := by
  simpa [measureUnivNNReal, measure_univ] using
    Lp.norm_le_of_ae_bound zero_le_one (dyadicRademacherLp_bound (𝕜 := 𝕜) (p := p) n)

end SurveyStatements.P5
