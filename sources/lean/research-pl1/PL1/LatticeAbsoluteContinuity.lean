import PL1.LatticeStrictPositive

/-!
# Uniform absolute continuity on order intervals

In a Schur Banach lattice, a strictly positive continuous functional controls
the norm uniformly on each fixed order interval. This uses actual monotone
norm convergence, rather than assuming compactness of the interval.
-/

noncomputable section
open Filter TopologicalSpace Finset
open scoped Topology

namespace PL1.SchurLattice

variable {E : Type*} [NormedAddCommGroup E] [Lattice E]
  [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E]

private def partialSup (x : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => partialSup x n ⊔ x n

omit [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E] in
private theorem partialSup_nonneg (x : ℕ → E) (n : ℕ) : 0 ≤ partialSup x n := by
  induction n with
  | zero => exact le_rfl
  | succ n hn => exact hn.trans le_sup_left

omit [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E] in
private theorem partialSup_le (x : ℕ → E) (u : E) (hu : 0 ≤ u)
    (hx : ∀ n, x n ≤ u) (n : ℕ) : partialSup x n ≤ u := by
  induction n with
  | zero => exact hu
  | succ n hn => exact sup_le hn (hx n)

omit [IsOrderedAddMonoid E] [NormedVectorLattice E] [CompleteSpace E] in
private theorem partialSup_monotone (x : ℕ → E) : Monotone (partialSup x) :=
  monotone_nat_of_le_succ (fun _ => le_sup_left)

/-- The supremum of a dominated positive sequence exists, and its value at
any positive functional is bounded by the sum of that functional's values. -/
theorem exists_isLUB_with_dual_bound (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (x : ℕ → E) (u : E) (hu : 0 ≤ u)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ u) (hsum : Summable (fun n => φ (x n))) :
    ∃ z : E, IsLUB (Set.range x) z ∧ 0 ≤ z ∧ z ≤ u ∧
      φ z ≤ ∑' n, φ (x n) := by
  have hpos := partialSup_nonneg x
  have hle := partialSup_le x u hu (fun n => (hx n).2)
  obtain ⟨z, hz⟩ := exists_tendsto_of_monotone_norm_bounded hS (partialSup x)
    (partialSup_monotone x) ‖u‖ (fun n => by
      apply norm_le_norm_of_abs_le_abs
      simpa only [abs_of_nonneg (hpos n), abs_of_nonneg hu] using hle n)
  have hz0 : 0 ≤ z := ge_of_tendsto' hz hpos
  have hzu : z ≤ u := le_of_tendsto' hz hle
  have hlub := isLUB_of_tendsto_atTop (partialSup_monotone x) hz
  have hzx (n : ℕ) : x n ≤ z :=
    le_sup_right.trans (hlub.1 (Set.mem_range_self (n + 1)))
  have hlubx : IsLUB (Set.range x) z := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact hzx n
    · intro b hb
      apply hlub.2
      rintro _ ⟨n, rfl⟩
      exact partialSup_le x b ((hx 0).1.trans (hb (Set.mem_range_self 0)))
        (fun n => hb (Set.mem_range_self n)) n
  have hfinite (N : ℕ) : φ (partialSup x N) ≤ ∑ n ∈ range N, φ (x n) := by
    induction N with
    | zero => simp [partialSup]
    | succ N ih =>
      have hsuple : partialSup x N ⊔ x N ≤ partialSup x N + x N :=
        sup_le (le_add_of_nonneg_right (hx N).1) (le_add_of_nonneg_left (hpos N))
      calc
        φ (partialSup x (N + 1)) ≤ φ (partialSup x N + x N) :=
          StrongDual.apply_le_apply_of_nonneg hφ hsuple
        _ = φ (partialSup x N) + φ (x N) := map_add _ _ _
        _ ≤ (∑ n ∈ range N, φ (x n)) + φ (x N) := add_le_add ih le_rfl
        _ = ∑ n ∈ range (N + 1), φ (x n) := (sum_range_succ _ _).symm
  refine ⟨z, hlubx, hz0, hzu, ?_⟩
  exact le_of_tendsto' ((φ.continuous.tendsto z).comp hz) (fun N =>
    (hfinite N).trans (hsum.sum_le_tsum (range N) (fun n _ =>
      StrongDual.apply_nonneg_of_nonneg hφ (hx n).1)))

/-- A dominated positive sequence whose values at a strictly positive
functional are summable converges to zero in the original norm. -/
theorem tendsto_zero_of_summable_strictlyPositive (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ)
    (x : ℕ → E) (u : E) (hu : 0 ≤ u)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ u) (hsum : Summable (fun n => φ (x n))) :
    Tendsto x atTop (𝓝 0) := by
  classical
  choose z hz using (fun N : ℕ =>
    exists_isLUB_with_dual_bound hS φ hφ.nonneg (fun n => x (n + N)) u hu
      (fun n => hx (n + N)) (hsum.comp_injective (add_left_injective N)))
  have hz0 (N : ℕ) : 0 ≤ z N := (hz N).2.1
  have hzu (N : ℕ) : z N ≤ u := (hz N).2.2.1
  have hanti : Antitone z := by
    intro N M hNM
    apply (hz M).1.2
    rintro _ ⟨n, rfl⟩
    exact (hz N).1.1 ⟨n + (M - N), by dsimp; rw [Nat.add_assoc, Nat.sub_add_cancel hNM]⟩
  obtain ⟨a, ha⟩ := exists_tendsto_of_antitone_norm_bounded hS z hanti ‖u‖ (by
    intro N
    apply norm_le_norm_of_abs_le_abs
    simpa only [abs_of_nonneg (hz0 N), abs_of_nonneg hu] using hzu N)
  have hφz : Tendsto (fun N => φ (z N)) atTop (𝓝 0) :=
    squeeze_zero (fun N => StrongDual.apply_nonneg_of_nonneg hφ.nonneg (hz0 N))
      (fun N => (hz N).2.2.2) (tendsto_sum_nat_add (fun n => φ (x n)))
  have hφa : φ a = 0 := tendsto_nhds_unique ((φ.continuous.tendsto a).comp ha) hφz
  have ha0 : a = 0 := hφ.eq_zero_of_nonneg (ge_of_tendsto' ha hz0) hφa
  subst a
  apply squeeze_zero_norm _ (by simpa only [norm_zero] using ha.norm)
  intro N
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (hx N).1, abs_of_nonneg (hz0 N)]
  exact (hz N).1.1 ⟨0, by simp⟩

/-- Uniform absolute continuity of the lattice norm on a fixed positive
order interval with respect to a strictly positive continuous functional. -/
theorem norm_lt_of_strictlyPositive_lt (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) (u : E) (hu : 0 ≤ u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, 0 ≤ x → x ≤ u → φ x < δ → ‖x‖ < ε := by
  classical
  by_contra hbad
  push Not at hbad
  choose x hx0 hxu hφx hnorm using fun n : ℕ =>
    hbad ((1 / 2 : ℝ) ^ n) (by positivity)
  have hs : Summable (fun n => φ (x n)) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).of_nonneg_of_le
      (fun n => StrongDual.apply_nonneg_of_nonneg hφ.nonneg (hx0 n))
        (fun n => (hφx n).le)
  have ht := (tendsto_zero_of_summable_strictlyPositive hS φ hφ x u hu
    (fun n => ⟨hx0 n, hxu n⟩) hs).norm
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const (by simpa using hε)).exists
  exact (not_lt_of_ge (hnorm n)) hn

/-- For dominated positive sequences, convergence to zero at one strictly
positive functional is equivalent to convergence in the original norm. -/
theorem tendsto_zero_iff_strictlyPositive (hS : HasSchurProperty ℝ E)
    (φ : E →L[ℝ] ℝ) (hφ : IsStrictlyPositive φ) (x : ℕ → E)
    (u : E) (hu : 0 ≤ u) (hx : ∀ n, 0 ≤ x n ∧ x n ≤ u) :
    Tendsto x atTop (𝓝 0) ↔ Tendsto (fun n => φ (x n)) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [← map_zero φ]
    exact (φ.continuous.tendsto 0).comp h
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := norm_lt_of_strictlyPositive_lt hS φ hφ u hu ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually_lt_const hδ)
    refine ⟨N, fun n hn => ?_⟩
    simpa only [dist_zero_right] using hcontrol (x n) (hx n).1 (hx n).2 (hN n hn)

end PL1.SchurLattice
