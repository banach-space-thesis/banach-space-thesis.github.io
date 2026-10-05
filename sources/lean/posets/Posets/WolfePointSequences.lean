import ThesisCommon.Analysis.CountableCompactShells

/-! Disjoint open neighborhoods for point sequences in Wolfe's recursion.
The sets of admissible points may vary with the stage. Countable metric spaces
provide clopen shells; no ordinal classification or operator theorem is used. -/

noncomputable section
open Set Filter Topology ThesisCommon
namespace Posets
variable {K : Type*} [MetricSpace K] [Countable K]

theorem accumulating_set_meets_arbitrarily_late_shells {x : K} {A U : Set K}
    (hx : x ∈ derivedSet A) (hU : IsOpen U) (hxU : x ∈ U) (N : ℕ) :
    ∃ j, N ≤ j ∧ (A ∩ U ∩ countableClopenShell x j).Nonempty := by
  have hV : U ∩ countableClopenNest x N ∈ 𝓝 x :=
    (hU.inter (countableClopenNest_isClopen x N).isOpen).mem_nhds
      ⟨hxU, countableClopenNest_mem x N⟩
  obtain ⟨y, ⟨hyV, hyA⟩, hyx⟩ := (accPt_iff_nhds.mp hx) _ hV
  obtain ⟨j, hj⟩ := countableClopenShell_covers x hyx
  refine ⟨j, ?_, y, ⟨hyA, hyV.1⟩, hj⟩
  by_contra hNj
  have hjN : j + 1 ≤ N := by omega
  exact hj.2 (countableClopenNest_antitone x hjN hyV.2)

theorem exists_disjoint_open_point_sequence {x : K} (A : ℕ → Set K)
    (hx : ∀ n, x ∈ derivedSet (A n)) {U : Set K} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y : ℕ → K, ∃ V : ℕ → Set K,
      (∀ n, y n ∈ A n ∧ y n ∈ V n ∧ IsOpen (V n) ∧ V n ⊆ U) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧ Tendsto y atTop (𝓝 x) := by
  classical
  have hex (n N : ℕ) := accumulating_set_meets_arbitrarily_late_shells (hx n) hU hxU N
  let chooseIndex (n N : ℕ) : ℕ := (hex n N).choose
  have hchoose (n N : ℕ) : N ≤ chooseIndex n N ∧
      (A n ∩ U ∩ countableClopenShell x (chooseIndex n N)).Nonempty :=
    (hex n N).choose_spec
  let j : ℕ → ℕ := Nat.rec (chooseIndex 0 1) (fun n prev => chooseIndex (n + 1) (prev + 1))
  have hj0 : 1 ≤ j 0 := (hchoose 0 1).1
  have hjstep (n : ℕ) : j n < j (n + 1) :=
    (hchoose (n + 1) (j n + 1)).1
  have hjmono : StrictMono j := strictMono_nat_of_lt_succ hjstep
  have hjge (n : ℕ) : n + 1 ≤ j n := by
    induction n with
    | zero => exact hj0
    | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hjstep n))
  have hjmem (n : ℕ) : (A n ∩ U ∩ countableClopenShell x (j n)).Nonempty := by
    cases n with
    | zero => exact (hchoose 0 1).2
    | succ n => exact (hchoose (n + 1) (j n + 1)).2
  let y : ℕ → K := fun n => (hjmem n).choose
  have hy (n : ℕ) : y n ∈ A n ∩ U ∩ countableClopenShell x (j n) := (hjmem n).choose_spec
  let V : ℕ → Set K := fun n => U ∩ countableClopenShell x (j n)
  refine ⟨y, V, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hy n).1.1, ⟨(hy n).1.2, (hy n).2⟩,
      hU.inter (countableClopenShell_isClopen x (j n)).isOpen, inter_subset_left⟩
  · intro n m hnm
    exact (countableClopenShell_disjoint x (hjmono.injective.ne hnm)).mono
      inter_subset_right inter_subset_right
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    have hn : y n ∈ countableClopenNest x (n + 1) :=
      countableClopenNest_antitone x (hjge n) (hy n).2.1
    exact (hn.2.trans (countableClopenRadius_spec x n).2.1).le

theorem exists_disjoint_open_point_sequence_closure {x : K} (A : ℕ → Set K)
    (hx : ∀ n, x ∈ derivedSet (A n)) {U : Set K} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y : ℕ → K, ∃ V : ℕ → Set K,
      (∀ n, y n ∈ A n ∧ y n ∈ V n ∧ IsOpen (V n) ∧ V n ⊆ U) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧ Tendsto y atTop (𝓝 x) ∧
        closure (⋃ n, V n) ⊆ U := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨ρ, hρ, hρr, hcl⟩ := countableMetric_exists_clopen_ball x hr
  have hsub : Metric.ball x ρ ⊆ U := (Metric.ball_subset_ball hρr.le).trans hball
  obtain ⟨y, V, hy, hd, ht⟩ := exists_disjoint_open_point_sequence A hx hcl.isOpen
    (Metric.mem_ball_self hρ)
  refine ⟨y, V, (fun n => ⟨(hy n).1, (hy n).2.1, (hy n).2.2.1,
    ((hy n).2.2.2).trans hsub⟩), hd, ht, ?_⟩
  exact (closure_minimal (iUnion_subset fun n => (hy n).2.2.2) hcl.isClosed).trans hsub

end Posets
