import ThesisCommon.Analysis.RegularMeasureOpenStep

/-! Disjoint Borel mass witnesses yield disjoint open mass witnesses,
using an actual recurrent regular measure and arbitrarily small loss. -/
noncomputable section
open Set MeasureTheory Topology Filter
namespace ThesisCommon
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

private structure OpenSelectionState (ν : Measure K) (ε : ℝ) where
  nextIndex : ℕ
  D : Set K
  compact : IsCompact D
  q : C(K, ℝ)
  nonneg : 0 ≤ q
  majorizes : ∀ x ∈ D, 1 ≤ q x
  small : (∫ x, q x ∂ν) < ε / 2

theorem exists_disjoint_open_of_recurrent_regularMeasure
    (μ : ℕ → Measure K) [∀ n, IsFiniteMeasure (μ n)] [∀ n, (μ n).Regular]
    (ν : Measure K) [IsFiniteMeasure ν] [ν.Regular]
    (hrec : ∀ (f : C(K, ℝ)) (r : ℝ), (∫ x, f x ∂ν) < r →
      ∃ᶠ n in atTop, (∫ x, f x ∂μ n) < r)
    (A : ℕ → Set K) (hA : ∀ n, MeasurableSet (A n))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {c ε : ℝ} (hmass : ∀ n, c < (μ n).real (A n)) (hε : 0 < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ U : ℕ → Set K,
      (∀ n, IsOpen (U n)) ∧ Pairwise (fun i j => Disjoint (U i) (U j)) ∧
        ∀ n, c - ε < (μ (k n)).real (U n) := by
  classical
  let S := OpenSelectionState ν ε
  have hs (s : S) := exists_regularMeasure_open_step μ ν hrec A hA hAd hmass hε
    s.nextIndex s.D s.compact s.q s.nonneg s.majorizes s.small
  choose i hi U hU hd hm b hb hbU hsmall using hs
  let step : S → S := fun s =>
    { nextIndex := i s + 1
      D := s.D ∪ closure (U s)
      compact := s.compact.union isClosed_closure.isCompact
      q := s.q + b s
      nonneg := add_nonneg s.nonneg (hb s)
      majorizes := by
        intro x hx
        rcases hx with hx | hx
        · exact (s.majorizes x hx).trans (le_add_of_nonneg_right (hb s x))
        · exact (hbU s x hx).trans (le_add_of_nonneg_left (s.nonneg x))
      small := hsmall s }
  let initial : S :=
    { nextIndex := 0
      D := ∅
      compact := isCompact_empty
      q := 0
      nonneg := le_rfl
      majorizes := by simp
      small := by simpa using (half_pos hε) }
  let seq : ℕ → S := Nat.rec initial (fun _ s => step s)
  have hDmono : Monotone (fun n => (seq n).D) := by
    apply monotone_nat_of_le_succ
    intro n
    exact subset_union_left
  have hprior {m n : ℕ} (hmn : m < n) : U (seq m) ⊆ (seq n).D :=
    subset_closure.trans (subset_union_right.trans (hDmono (Nat.succ_le_of_lt hmn)))
  have hdis {m n : ℕ} (hmn : m < n) : Disjoint (U (seq m)) (U (seq n)) :=
    (hd (seq n)).symm.mono (hprior hmn) subset_closure
  refine ⟨fun n => i (seq n), strictMono_nat_of_lt_succ ?_, fun n => U (seq n),
    fun n => hU (seq n), ?_, fun n => hm (seq n)⟩
  · intro n
    exact (Nat.lt_succ_self (i (seq n))).trans_le (hi (seq (n + 1)))
  · intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hdis h
    · exact (hdis h).symm

end ThesisCommon
