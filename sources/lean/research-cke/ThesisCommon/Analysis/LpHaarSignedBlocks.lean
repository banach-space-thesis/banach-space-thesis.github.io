import ThesisCommon.Analysis.LpHaarSignedPartitions
import ThesisCommon.Analysis.SignAveraging

/-! A signed sum of disjoint dyadic Haar vectors is exactly the Haar
vector of its two selected measurable children. Its norm and cancellation
are properties of the actual Lp equivalence class. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace ThesisCommon

theorem lpHaarIndicator_biUnion_sum {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (f : ι → Set α) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j => Disjoint (f i) (f j))) (S : Finset ι) :
    indicatorConstLp p (S.measurableSet_biUnion (fun i _ => hf i))
      (measure_ne_top μ _) (1 : 𝕜) =
        ∑ i ∈ S, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : 𝕜) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hU : (⋃ j ∈ insert i S, f j) = f i ∪ ⋃ j ∈ S, f j := by
      ext x
      simp
    have hdis : Disjoint (f i) (⋃ j ∈ S, f j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hd (fun hij => hi (hij.symm ▸ hj))
    simp only [hU, Finset.sum_insert hi, ← ih]
    exact indicatorConstLp_disjoint_union (hf i)
      (S.measurableSet_biUnion (fun j _ => hf j))
      (measure_ne_top μ _) (measure_ne_top μ _) hdis 1

def lpHaarSignedBlock (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) : IntervalLp 𝕜 p :=
  ∑ k ∈ S, signedValue (θ k) (lpHaarDyadic 𝕜 p n k)

theorem lpHaarSignedBlock_eq_vector (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    lpHaarSignedBlock 𝕜 p n S θ =
      lpHaarVector 𝕜 p.val (lpHaarSignedPart n S θ)
        (lpHaarSignedPart n S (fun k => !(θ k)))
        (lpHaarSignedPart_measurable n S θ)
        (lpHaarSignedPart_measurable n S (fun k => !(θ k))) := by
  unfold lpHaarVector
  have hpos := lpHaarIndicator_biUnion_sum (p := p.val)
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (𝕜 := 𝕜)
    (fun k : Fin (2 ^ n) => lpHaarSignedChild n k (θ k))
    (fun k => lpHaarSignedChild_measurable n k (θ k))
    (fun i j hij => lpHaarSignedChild_disjoint_other n
      (fun h => hij (Fin.ext h)) (θ i) (θ j)) S
  have hneg := lpHaarIndicator_biUnion_sum (p := p.val)
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (𝕜 := 𝕜)
    (fun k : Fin (2 ^ n) => lpHaarSignedChild n k (!(θ k)))
    (fun k => lpHaarSignedChild_measurable n k (!(θ k)))
    (fun i j hij => lpHaarSignedChild_disjoint_other n
      (fun h => hij (Fin.ext h)) (!(θ i)) (!(θ j))) S
  rw [hpos, hneg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  cases θ k <;> simp only [signedValue, Bool.false_eq_true, if_false, if_true,
    lpHaarSignedChild, Bool.not_false, Bool.not_true, Nat.add_zero,
    lpHaarDyadic, lpHaarVector] <;> abel

theorem lpHaarSignedBlock_norm (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    ‖lpHaarSignedBlock 𝕜 p n S θ‖ =
      (volume.restrict (Icc (0 : ℝ) 1)).real (lpHaarBlockParent n S) ^ (1 / p.val.toReal) := by
  rw [lpHaarSignedBlock_eq_vector, lpHaarVector_norm hp _ _
    (lpHaarSignedPart_measurable n S θ)
    (lpHaarSignedPart_measurable n S (fun k => !(θ k))) (lpHaarSignedPart_disjoint n S θ),
    lpHaarSignedPart_union]

theorem lpHaarSignedBlock_integral_zero (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (n : ℕ) (S : Finset (Fin (2 ^ n))) (θ : Fin (2 ^ n) → Bool) :
    ∫ x, lpHaarSignedBlock 𝕜 p n S θ x ∂(volume.restrict (Icc (0 : ℝ) 1)) = 0 := by
  rw [lpHaarSignedBlock_eq_vector]
  exact lpHaarVector_integral_zero _ _ _ _ (lpHaarSignedPart_equal_measure n S θ)

end ThesisCommon
