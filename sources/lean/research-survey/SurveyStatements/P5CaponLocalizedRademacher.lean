import SurveyStatements.P5RademacherReaders
import SurveyStatements.P5RademacherDecay
import SurveyStatements.P5Support.LpHaarDyadicRefinement

/-! Genuine Rademacher levels localized to an arbitrary dyadic root cell.
The finite dyadic refinements retain the root's measure exactly. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace Classical

namespace SurveyStatements.P5
open P5Support
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def caponLocalCells (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) : Finset (Fin (2 ^ (m + n))) :=
  lpHaarRefine m {root} n

def caponLocalRademacher (m : ℕ) (root : Fin (2 ^ m))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) : Lp ℝ p unitIntervalMeasure :=
  ∑ k ∈ caponLocalCells m root n, dyadicHaar ℝ p ⟨m + n, k⟩

def caponLocalRademacherFunction (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ caponLocalCells m root n, lpHaarFunction ℝ
    (lpHaarCell (m + n + 1) (2 * k.val))
    (lpHaarCell (m + n + 1) (2 * k.val + 1)) x

theorem caponLocalCells_union (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    lpHaarBlockParent (m + n) (caponLocalCells m root n) = lpHaarCell m root := by
  rw [caponLocalCells, lpHaarBlockParent_refine]
  simp only [lpHaarBlockParent, Finset.mem_singleton, iUnion_iUnion_eq_left]

theorem caponLocalCells_contained (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ)
    (k : Fin (2 ^ (m + n))) (hk : k ∈ caponLocalCells m root n) :
    lpHaarCell (m + n) k ⊆ lpHaarCell m root := by
  rw [← caponLocalCells_union m root n]
  intro x hx
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hx⟩⟩

theorem caponLocalCells_mass (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    ∑ k ∈ caponLocalCells m root n, unitIntervalMeasure.real (dyadicInterval ⟨m + n, k⟩) =
      intervalLpDyadicRadius m := by
  simp only [dyadicInterval_real_measure, Finset.sum_const, nsmul_eq_mul]
  simpa only [caponLocalCells, Finset.card_singleton, Nat.cast_one, one_mul,
    intervalLpDyadicRadius, one_div, inv_pow] using lpHaarRefine_mass m {root} n

theorem caponLocalRademacher_ae (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    caponLocalRademacher m root p n =ᵐ[unitIntervalMeasure]
      caponLocalRademacherFunction m root n := by
  have hhaar (k : Fin (2 ^ (m + n))) : dyadicHaar ℝ p ⟨m + n, k⟩ =ᵐ[unitIntervalMeasure]
      lpHaarFunction ℝ (lpHaarCell (m + n + 1) (2 * k.val))
        (lpHaarCell (m + n + 1) (2 * k.val + 1)) := by
    rw [dyadicHaar_eq_support]
    exact lpHaarVector_coe _ _ measurableSet_Ioc measurableSet_Ioc
  filter_upwards [scalarLp_sum_ae (caponLocalCells m root n)
    (fun k => dyadicHaar ℝ p ⟨m + n, k⟩), ae_all_iff.mpr hhaar] with x hx hh
  exact hx.trans (Finset.sum_congr rfl (fun k _ => hh k))

theorem norm_caponLocalRademacherFunction_le (m : ℕ) (root : Fin (2 ^ m))
    (n : ℕ) (x : ℝ) : ‖caponLocalRademacherFunction m root n x‖ ≤ 1 := by
  let v (k : Fin (2 ^ (m + n))) := lpHaarFunction ℝ
    (lpHaarCell (m + n + 1) (2 * k.val))
    (lpHaarCell (m + n + 1) (2 * k.val + 1)) x
  have hzero (k : Fin (2 ^ (m + n))) (hx : x ∉ lpHaarCell (m + n) k.val) : v k = 0 := by
    have hc := lpHaarCell_children (m + n) k.val
    have hl : x ∉ lpHaarCell (m + n + 1) (2 * k.val) :=
      fun h => hx (hc ▸ Or.inl h)
    have hr : x ∉ lpHaarCell (m + n + 1) (2 * k.val + 1) :=
      fun h => hx (hc ▸ Or.inr h)
    simp [v, lpHaarFunction, hl, hr]
  by_cases hx : ∃ k ∈ caponLocalCells m root n, x ∈ lpHaarCell (m + n) k.val
  · obtain ⟨k, hk, hxk⟩ := hx
    have hs : (∑ j ∈ caponLocalCells m root n, v j) = v k := by
      apply Finset.sum_eq_single k
      · intro j _ hj
        apply hzero
        intro hmem
        exact Set.disjoint_left.mp (lpHaarCell_disjoint_sameLevel (m + n)
          (fun h => hj (Fin.ext h))) hmem hxk
      · exact fun h => (h hk).elim
    change ‖∑ j ∈ caponLocalCells m root n, v j‖ ≤ 1
    rw [hs]
    change ‖lpHaarFunction ℝ (lpHaarCell (m + n + 1) (2 * k.val))
      (lpHaarCell (m + n + 1) (2 * k.val + 1)) x‖ ≤ 1
    rw [lpHaarFunction_norm _ _ (lpHaarCell_disjoint_sameLevel (m + n + 1) (by omega)),
      lpHaarCell_children]
    simp [hxk]
  · have hz : (∑ j ∈ caponLocalCells m root n, v j) = 0 :=
      Finset.sum_eq_zero (fun j hj => hzero j (fun h => hx ⟨j, hj, h⟩))
    change ‖∑ j ∈ caponLocalCells m root n, v j‖ ≤ 1
    rw [hz, norm_zero]
    exact zero_le_one

theorem caponLocalRademacher_bound (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖caponLocalRademacher m root p n x‖ ≤ 1 := by
  filter_upwards [caponLocalRademacher_ae (p := p) m root n] with x hx
  rw [hx]
  exact norm_caponLocalRademacherFunction_le m root n x

theorem caponLocalRademacher_mean_zero (m : ℕ) (root : Fin (2 ^ m)) (n : ℕ) :
    probabilityLpMean (𝕜 := ℝ) (caponLocalRademacher m root p n) = 0 := by
  simp only [caponLocalRademacher, map_sum, dyadicHaar_mean_zero, Finset.sum_const_zero]

theorem rademacherReader_caponLocalRademacher (m : ℕ) (root : Fin (2 ^ m)) (i n : ℕ) :
    rademacherReader p (m + i) (caponLocalRademacher m root p n) =
      if i = n then intervalLpDyadicRadius m else 0 := by
  rw [caponLocalRademacher, map_sum]
  simp_rw [rademacherReader_dyadicHaar]
  by_cases hin : i = n
  · subst n
    simp only [if_pos rfl]
    exact caponLocalCells_mass m root i
  · rw [if_neg hin]
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (fun h => hin (Nat.add_left_cancel h))

theorem caponLocalRademacher_L2_inner (m : ℕ) (root : Fin (2 ^ m)) (n j : ℕ) :
    ⟪caponLocalRademacher m root 2 n, caponLocalRademacher m root 2 j⟫ =
      if n = j then intervalLpDyadicRadius m else 0 := by
  rw [caponLocalRademacher, caponLocalRademacher, sum_inner]
  simp_rw [inner_sum, realDyadicHaar_inner]
  by_cases hnj : n = j
  · subst j
    rw [if_pos rfl]
    have hsum : ∀ k ∈ caponLocalCells m root n,
        (∑ l ∈ caponLocalCells m root n,
          if (⟨m + n, k⟩ : DyadicIndex) = ⟨m + n, l⟩ then
            unitIntervalMeasure.real (dyadicInterval ⟨m + n, k⟩) else 0) =
          unitIntervalMeasure.real (dyadicInterval ⟨m + n, k⟩) := by
      intro k hk
      simp only [Sigma.mk.inj_iff, true_and, heq_eq_eq]
      simp [hk]
    rw [Finset.sum_congr rfl hsum]
    exact caponLocalCells_mass m root n
  · rw [if_neg hnj]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    exact if_neg (fun h => hnj (Nat.add_left_cancel (congrArg Sigma.fst h)))

end SurveyStatements.P5
