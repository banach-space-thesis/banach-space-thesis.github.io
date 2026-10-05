import ThesisCommon.Analysis.GowersMaureyLaurentApproximateEigenvectors
import ThesisCommon.Analysis.GowersMaureyBlockEigenObstruction
import ThesisCommon.Analysis.WienerFourierSeries

/-! Every nonzero complex Laurent operator preserves an actual
infinite-dimensional subspace. A nonzero Fourier value supplies the scalar;
successive geometric blocks have summable eigenvector errors, which control
all vectors of their scalar span by the proved block coefficient estimates. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey

theorem exists_laurent_eigen_block_sequence (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (z : Circle) (η : ℕ → ℝ)
    (hη : ∀ i, 0 < η i) (hanti : Antitone η) :
    ∃ u : ℕ → C00 ℂ, (∀ i j, i < j → Before (u i) (u j)) ∧
      (∀ i, implicitNorm D (u i) = 1) ∧
      ∀ i, ‖laurentOperator D a (denseEmbedding D (u i))-
        wienerEvaluate z a • denseEmbedding D (u i)‖ < η i := by
  classical
  let P (b : ℕ × C00 ℂ) := implicitNorm D b.2 = 1 ∧
    ‖laurentOperator D a (denseEmbedding D b.2)-wienerEvaluate z a • denseEmbedding D b.2‖ < η b.1
  let R (b c : ℕ × C00 ℂ) := b.1 < c.1 ∧ Before b.2 c.2
  have hselect : ∀ s : Finset (ℕ × C00 ℂ), (∀ b ∈ s, P b) →
      ∃ c, P c ∧ ∀ b ∈ s, R b c := by
    intro s _
    let n := s.sup Prod.fst+1
    let B := s.sup (fun b => b.2.support.sup id)
    obtain ⟨x,hxB,hxn,hxerr⟩ := exists_unit_tail_laurent_approximate_eigenvector D a z B (hη n)
    refine ⟨(n,x),⟨hxn,hxerr⟩,?_⟩
    intro b hb
    refine ⟨(Finset.le_sup (f := Prod.fst) hb).trans_lt (Nat.lt_succ_self _),?_⟩
    apply before_of_mem_afterCutoff (K := B) _ hxB
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      (Finset.le_sup (f := fun b : ℕ × C00 ℂ => b.2.support.sup id) hb)
  obtain ⟨w,hw,hwr⟩ := exists_seq_of_forall_finset_exists P R hselect
  have hindex : ∀ i : ℕ, i ≤ (w i).1 := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have hh := (hwr i (i+1) (Nat.lt_succ_self i)).1; omega
  exact ⟨fun i => (w i).2, fun i j hij => (hwr i j hij).2,
    fun i => (hw i).1, fun i => (hw i).2.trans_le (hanti (hindex i))⟩

theorem not_strictlySingular_laurent_of_evaluation_ne_zero (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (z : Circle) (ha : wienerEvaluate z a ≠ 0) :
    ¬ IsStrictlySingularOperator (laurentOperator D a) := by
  let η : ℕ → ℝ := fun i => (‖wienerEvaluate z a‖/8)*((1 : ℝ)/2)^i
  have hη : ∀ i, 0 < η i := fun i =>
    mul_pos (div_pos (norm_pos_iff.mpr ha) (by norm_num)) (pow_pos (by norm_num) i)
  have hanti : Antitone η := by
    apply antitone_nat_of_succ_le
    intro i
    dsimp only [η]
    rw [pow_succ]
    have hh : 0 ≤ (‖wienerEvaluate z a‖/8)*((1 : ℝ)/2)^i := (hη i).le
    nlinarith
  obtain ⟨u,hu,hun,herr⟩ := exists_laurent_eigen_block_sequence D a z η hη hanti
  have hs : HasSum η (‖wienerEvaluate z a‖/4) := by
    convert hasSum_geometric_two.mul_left (‖wienerEvaluate z a‖/8) using 1
    ring
  exact not_strictlySingular_of_block_eigen_errors D (laurentOperator D a)
    (wienerEvaluate z a) ha u hu hun η (fun i => (hη i).le) (fun i => (herr i).le)
    (fun s => (hs.summable.sum_le_tsum s (fun i _ => (hη i).le)).trans_eq hs.tsum_eq)

theorem exists_wienerEvaluate_ne_zero {a : WienerSequences ℂ} (ha : a ≠ 0) :
    ∃ z : Circle, wienerEvaluate z a ≠ 0 := by
  by_contra h
  push_neg at h
  apply ha
  apply wienerFourierSeries_injective
  ext z
  rw [wienerFourierSeries_evaluate, map_zero]
  exact h (AddCircle.toCircle z)

theorem not_strictlySingular_laurent_of_ne_zero (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (ha : a ≠ 0) :
    ¬ IsStrictlySingularOperator (laurentOperator D a) := by
  obtain ⟨z,hz⟩ := exists_wienerEvaluate_ne_zero ha
  exact not_strictlySingular_laurent_of_evaluation_ne_zero D a z hz

end ThesisCommon.GowersMaurey
