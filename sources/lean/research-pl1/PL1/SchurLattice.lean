import PL1.SchurBoundedCompleteness
import BanLat.Disjoint
import BanLat.OrderComplete

/-!
# Order-bounded disjoint sequences in Schur lattices

This proves the first step of the paper's Schur-lattice lemma. It does not
assert the full structural Radon-Nikodym theorem for Schur Banach lattices.
-/

noncomputable section
open Filter Finset
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E]

/-- The lattice absolute value of every signed finite sum stays below the
common order bound of a pairwise disjoint sequence. -/
theorem abs_signed_sum_le (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u)
    (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    |∑ n ∈ Finset.range N, ε n • x n| ≤ u := by
  classical
  have hu : 0 ≤ u := (abs_nonneg (x 0)).trans (hbound 0)
  by_cases hN : N = 0
  · subst N
    simpa using hu
  have hd : Pairwise (fun i j : Fin N => IsVLDisjoint (x i) (x j)) := by
    intro i j hij
    exact hdisj (fun h => hij (Fin.ext h))
  have hdabs : Pairwise (fun i j : Fin N => IsVLDisjoint |x i| |x j|) := by
    intro i j hij
    simpa only [IsVLDisjoint, abs_abs] using hd hij
  have hsign (i : Fin N) : |ε i| = 1 := by
    rcases hε i with hi | hi <;> simp [hi]
  have hfin : |∑ i : Fin N, ε i • x i| ≤ u := by
    rw [abs_sum_of_pairwise_isVLDisjoint hd]
    simp only [hsign, one_smul]
    rw [sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg (Nat.pos_of_ne_zero hN)
      (fun i : Fin N => abs_nonneg (x i)) hdabs]
    exact Finset.sup'_le _ _ (fun i _ => hbound i)
  rw [← Fin.sum_univ_eq_sum_range (fun n => ε n • x n)]
  exact hfin

/-- Uniform norm bound for all signed partial sums, with no factor depending
on the number of terms. -/
theorem norm_signed_sum_le (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u)
    (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    ‖∑ n ∈ Finset.range N, ε n • x n‖ ≤ ‖u‖ :=
  norm_le_norm_of_abs_le_abs ((abs_signed_sum_le x hdisj u hbound N ε hε).trans (le_abs_self u))

/-- Every continuous real functional is absolutely summable on an order-bounded,
pairwise lattice-disjoint sequence. -/
theorem dual_summable_norm (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u) (φ : E →L[ℝ] ℝ) :
    Summable (fun n => ‖φ (x n)‖) :=
  SchurBoundedCompleteness.dual_summable_norm_of_signed_sums_bounded
    x ‖u‖ (norm_signed_sum_le x hdisj u hbound) φ

/-- An order-bounded disjoint sequence is weakly null, whether or not the
ambient normed lattice has the Schur property. -/
theorem weaklyConverges_zero (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u) : WeaklyConverges ℝ E x 0 :=
  SchurBoundedCompleteness.weaklyConverges_zero_of_signed_sums_bounded
    x ‖u‖ (norm_signed_sum_le x hdisj u hbound)

/-- Consequently every order-bounded disjoint sequence in a Schur normed
lattice tends to zero in norm. -/
theorem tendsto_zero (hS : HasSchurProperty ℝ E) (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u) : Tendsto x atTop (𝓝 0) :=
  hS x 0 (weaklyConverges_zero x hdisj u hbound)

theorem tendsto_norm_zero (hS : HasSchurProperty ℝ E) (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
  simpa only [norm_zero] using (tendsto_zero hS x hdisj u hbound).norm

/-- In the complete case the same sequence is unconditionally summable;
the conclusion uses all finite subsets, not just initial partial sums. -/
theorem summable [CompleteSpace E] (hS : HasSchurProperty ℝ E) (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (u : E) (hbound : ∀ n, |x n| ≤ u) : Summable x :=
  SchurBoundedCompleteness.summable_of_signed_sums_bounded hS x ‖u‖
    (norm_signed_sum_le x hdisj u hbound)

omit [NormedVectorLattice E] in
/-- An arbitrary common order interval supplies an absolute order bound. -/
theorem abs_le_of_mem_Icc {a b z : E} (hz : z ∈ Set.Icc a b) :
    |z| ≤ |a| ⊔ |b| := by
  rw [abs]
  exact sup_le (hz.2.trans ((le_abs_self b).trans le_sup_right))
    ((neg_le_neg hz.1).trans ((neg_le_abs a).trans le_sup_left))

theorem weaklyConverges_zero_of_mem_Icc (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (a b : E) (hbound : ∀ n, x n ∈ Set.Icc a b) : WeaklyConverges ℝ E x 0 :=
  weaklyConverges_zero x hdisj (|a| ⊔ |b|) (fun n => abs_le_of_mem_Icc (hbound n))

theorem tendsto_norm_zero_of_mem_Icc (hS : HasSchurProperty ℝ E) (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (a b : E) (hbound : ∀ n, x n ∈ Set.Icc a b) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) :=
  tendsto_norm_zero hS x hdisj (|a| ⊔ |b|) (fun n => abs_le_of_mem_Icc (hbound n))

/-- Disjoint expansions have an exact unconditional norm identity. -/
theorem norm_signed_sum_eq (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    ‖∑ n ∈ Finset.range N, ε n • x n‖ = ‖∑ n ∈ Finset.range N, x n‖ := by
  classical
  have hd : Pairwise (fun i j : Fin N => IsVLDisjoint (x i) (x j)) := by
    intro i j hij
    exact hdisj (fun h => hij (Fin.ext h))
  have hsign (i : Fin N) : |ε i| = 1 := by
    rcases hε i with hi | hi <;> simp [hi]
  have hsigned : |∑ i : Fin N, ε i • x i| = ∑ i : Fin N, |x i| := by
    rw [abs_sum_of_pairwise_isVLDisjoint hd]
    simp only [hsign, one_smul]
  have hplain : |∑ i : Fin N, x i| = ∑ i : Fin N, |x i| := by
    simpa only [one_smul, abs_one] using
      (abs_sum_of_pairwise_isVLDisjoint (α := fun _ => (1 : ℝ)) hd)
  rw [← Fin.sum_univ_eq_sum_range (fun n => ε n • x n),
    ← Fin.sum_univ_eq_sum_range x]
  rw [← norm_abs_eq_norm (∑ i : Fin N, ε i • x i),
    ← norm_abs_eq_norm (∑ i : Fin N, x i), hsigned, hplain]

/-- Every disjoint expansion with norm-bounded ordinary partial sums is
unconditionally summable in a Schur Banach lattice. -/
theorem summable_of_partialSums_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E)
    (hdisj : Pairwise (fun i j => IsVLDisjoint (x i) (x j)))
    (M : ℝ) (hM : ∀ N, ‖∑ n ∈ Finset.range N, x n‖ ≤ M) : Summable x := by
  apply SchurBoundedCompleteness.summable_of_signed_sums_bounded hS x M
  intro N ε hε
  rw [norm_signed_sum_eq x hdisj N ε hε]
  exact hM N

/-- Positive expansions also have uniformly bounded sign transformations. -/
theorem norm_signed_sum_le_of_nonneg (x : ℕ → E) (hx : ∀ n, 0 ≤ x n)
    (N : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    ‖∑ n ∈ Finset.range N, ε n • x n‖ ≤ ‖∑ n ∈ Finset.range N, x n‖ := by
  classical
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (Finset.sum_nonneg (fun n _ => hx n)), abs]
  apply sup_le
  · apply Finset.sum_le_sum
    intro n hn
    rcases hε n with he | he
    · simp only [he, one_smul, le_refl]
    · simpa only [he, neg_smul, one_smul] using (neg_nonpos.mpr (hx n)).trans (hx n)
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rcases hε n with he | he
    · simpa only [he, one_smul] using (neg_nonpos.mpr (hx n)).trans (hx n)
    · simp only [he, neg_smul, one_smul, neg_neg, le_refl]

/-- A positive series with bounded partial sums is unconditionally summable
in a Schur Banach lattice. -/
theorem summable_of_nonneg_partialSums_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (hx : ∀ n, 0 ≤ x n)
    (M : ℝ) (hM : ∀ N, ‖∑ n ∈ Finset.range N, x n‖ ≤ M) : Summable x := by
  apply SchurBoundedCompleteness.summable_of_signed_sums_bounded hS x M
  intro N ε hε
  exact (norm_signed_sum_le_of_nonneg x hx N ε hε).trans (hM N)

/-- Every norm-bounded increasing sequence in a Schur Banach lattice converges
in norm. This includes the usual KB property for positive increasing sequences. -/
theorem exists_tendsto_of_monotone_norm_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (hmono : Monotone x)
    (M : ℝ) (hM : ∀ n, ‖x n‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  let d : ℕ → E := fun n => x (n + 1) - x n
  have hd : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hmono (Nat.le_succ n))
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, d n) = x N - x 0 :=
    Finset.sum_range_sub x N
  have hb : ∀ N, ‖∑ n ∈ Finset.range N, d n‖ ≤ M + ‖x 0‖ := by
    intro N
    rw [hsum]
    exact (norm_sub_le _ _).trans (add_le_add (hM N) le_rfl)
  have hs := summable_of_nonneg_partialSums_bounded hS d hd (M + ‖x 0‖) hb
  refine ⟨(∑' n, d n) + x 0, ?_⟩
  simpa only [hsum, sub_add_cancel] using hs.hasSum.tendsto_sum_nat.add_const (x 0)

/-- The decreasing formulation of monotone convergence. -/
theorem exists_tendsto_of_antitone_norm_bounded [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (hanti : Antitone x)
    (M : ℝ) (hM : ∀ n, ‖x n‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_norm_bounded hS (fun n => -x n)
    (fun i j hij => neg_le_neg (hanti hij)) M (fun n => by simpa using hM n)
  exact ⟨-a, by simpa only [neg_neg] using ha.neg⟩

/-- Sequential order continuity: a decreasing positive sequence with greatest
lower bound zero is norm null in a Schur Banach lattice. -/
theorem tendsto_zero_of_antitone_isGLB [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) (x : ℕ → E) (hanti : Antitone x)
    (hglb : IsGLB (Set.range x) 0) : Tendsto x atTop (𝓝 0) := by
  have hx : ∀ n, 0 ≤ x n := fun n => hglb.1 (Set.mem_range_self n)
  obtain ⟨a, ha⟩ := exists_tendsto_of_antitone_norm_bounded hS x hanti ‖x 0‖ (by
    intro n
    apply norm_le_norm_of_abs_le_abs
    simpa only [abs_of_nonneg (hx n), abs_of_nonneg (hx 0)] using hanti (Nat.zero_le n))
  have heq : a = 0 := (isGLB_of_tendsto_atTop hanti ha).unique hglb
  exact heq ▸ ha

private theorem cauchy_map_atTop_of_near_base {ι Y : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [PseudoMetricSpace Y]
    (x : ι → Y)
    (h : ∀ ε : ℝ, 0 < ε → ∃ i, ∀ j, i ≤ j → dist (x j) (x i) < ε) :
    Cauchy (Filter.map x atTop) := by
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  obtain ⟨i, hi⟩ := h (ε / 2) (half_pos hε)
  refine ⟨x '' Set.Ici i, Filter.image_mem_map (Ici_mem_atTop i), ?_⟩
  rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
  have hj' := hi j hj
  have hk' := hi k hk
  have ht := dist_triangle (x j) (x i) (x k)
  rw [dist_comm (x i) (x k)] at ht
  linarith

/-- The KB convergence property holds for arbitrary directed nets as well as
sequences: a failure of the Cauchy condition would give a divergent monotone
sequence by recursive index selection. -/
theorem exists_tendsto_of_monotone_net_norm_bounded [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hS : HasSchurProperty ℝ E) (x : ι → E) (hmono : Monotone x)
    (M : ℝ) (hM : ∀ i, ‖x i‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  classical
  apply cauchy_map_iff_exists_tendsto.mp
  by_contra hbad
  have hfail : ¬ (∀ ε : ℝ, 0 < ε → ∃ i, ∀ j, i ≤ j → dist (x j) (x i) < ε) :=
    fun h => hbad (cauchy_map_atTop_of_near_base x h)
  push Not at hfail
  obtain ⟨ε, hε, hfail⟩ := hfail
  choose next hnext hdist using hfail
  let i : ℕ → ι := fun n => next^[n] (Classical.choice ‹Nonempty ι›)
  have hi (n : ℕ) : i (n + 1) = next (i n) := Function.iterate_succ_apply' _ _ _
  have hinc : Monotone i := monotone_nat_of_le_succ (fun n => by rw [hi]; exact hnext _)
  obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_norm_bounded hS (fun n => x (i n))
    (hmono.comp hinc) M (fun n => hM _)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq ε hε
  have hclose := hN (N + 1) (Nat.le_succ N) N le_rfl
  rw [hi] at hclose
  exact (not_lt_of_ge (hdist (i N))) hclose

theorem exists_tendsto_of_antitone_net_norm_bounded [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hS : HasSchurProperty ℝ E) (x : ι → E) (hanti : Antitone x)
    (M : ℝ) (hM : ∀ i, ‖x i‖ ≤ M) : ∃ a : E, Tendsto x atTop (𝓝 a) := by
  obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_net_norm_bounded hS (fun i => -x i)
    (fun i j hij => neg_le_neg (hanti hij)) M (fun i => by simpa using hM i)
  exact ⟨-a, by simpa only [neg_neg] using ha.neg⟩

/-- Full norm order continuity, stated explicitly for every decreasing net
whose greatest lower bound is zero. -/
theorem tendsto_zero_of_antitone_net_isGLB [CompleteSpace E]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (hS : HasSchurProperty ℝ E) (x : ι → E) (hanti : Antitone x)
    (hglb : IsGLB (Set.range x) 0) : Tendsto x atTop (𝓝 0) := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder (Set.Ici i₀) := ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge (i : ι) (j : ι)
    exact ⟨⟨k, i.prop.trans hik⟩, hik, hjk⟩⟩
  let y : Set.Ici i₀ → E := fun i => x i
  have hy : Antitone y := fun i j hij => hanti hij
  have hx : ∀ i, 0 ≤ x i := fun i => hglb.1 (Set.mem_range_self i)
  obtain ⟨a, ha⟩ := exists_tendsto_of_antitone_net_norm_bounded hS y hy ‖x i₀‖ (by
    intro i
    apply norm_le_norm_of_abs_le_abs
    simpa only [y, abs_of_nonneg (hx i), abs_of_nonneg (hx i₀)] using hanti i.prop)
  have htail : Tendsto x atTop (𝓝 a) := tendsto_comp_val_Ici_atTop.mp ha
  have heq : a = 0 := (isGLB_of_tendsto_atTop hanti htail).unique hglb
  exact heq ▸ htail

/-- A Schur Banach lattice is Dedekind complete. The construction extends the
given lattice structure; it does not replace its order or norm. -/
@[reducible]
def conditionallyCompleteLattice [CompleteSpace E] (hS : HasSchurProperty ℝ E) :
    ConditionallyCompleteLattice E :=
  conditionallyCompleteLatticeOfPosNet E (by
    intro ι _ _ _ x hmono hx hbdd
    obtain ⟨b, hb⟩ := hbdd
    obtain ⟨a, ha⟩ := exists_tendsto_of_monotone_net_norm_bounded hS x hmono ‖b‖ (by
      intro i
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (hx i)]
      exact (hb (Set.mem_range_self i)).trans (le_abs_self b))
    exact ⟨a, isLUB_of_tendsto_atTop hmono ha⟩)

/-- Explicit coherence with the pre-existing lattice instance. -/
theorem conditionallyCompleteLattice_toLattice [CompleteSpace E]
    (hS : HasSchurProperty ℝ E) :
    (conditionallyCompleteLattice hS).toLattice = (inferInstance : Lattice E) := rfl

theorem exists_isLUB [CompleteSpace E] (hS : HasSchurProperty ℝ E)
    (s : Set E) (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ a, IsLUB s a := by
  let := conditionallyCompleteLattice hS
  exact ⟨sSup s, isLUB_csSup hne hbdd⟩

end PL1.SchurLattice
