import Posets.WolfeMonotonicity

/-! Equivalence of nondecreasing and strictly increasing cofinal sequences
in Wolfe's limit clause. Thus the explicit strict convention imposes no extra
mathematical restriction on the source's notation αₙ ↑ α. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets

theorem monotone_cofinal_sequence_strict_refinement {α : Ordinal.{u}}
    (hα : IsSuccLimit α) (a : ℕ → Iio α) (ha : Monotone (fun n => (a n).val))
    (hcof : ∀ β < α, ∃ n, β ≤ (a n).val) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (fun n => (a (f n)).val) ∧
      ∀ β < α, ∃ n, β ≤ (a (f n)).val := by
  classical
  have hs (i : ℕ) : ∃ j, i < j ∧ (a i).val < (a j).val := by
    obtain ⟨j, hj⟩ := hcof (succ (a i).val) (hα.succ_lt (a i).property)
    have hij : (a i).val < (a j).val := (lt_succ _).trans_le hj
    refine ⟨j, ?_, hij⟩
    by_contra hji
    exact (not_lt_of_ge (ha (le_of_not_gt hji))) hij
  let f : ℕ → ℕ := Nat.rec 0 (fun _ prev => (hs prev).choose)
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun n => (hs (f n)).choose_spec.1
  have haf : StrictMono (fun n => (a (f n)).val) :=
    strictMono_nat_of_lt_succ fun n => (hs (f n)).choose_spec.2
  refine ⟨f, hf, haf, ?_⟩
  intro β hβ
  obtain ⟨n, hn⟩ := hcof β hβ
  exact ⟨n, hn.trans (ha (hf.id_le n))⟩

variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem WolfeChildren.subsequence {p : WolfeNode 𝕜 K} {c : ℕ → WolfeNode 𝕜 K}
    (hc : WolfeChildren p c) {f : ℕ → ℕ} (hf : StrictMono f) :
    WolfeChildren p (fun n => c (f n)) := by
  refine ⟨hc.1.comp hf.tendsto_atTop, ?_, ?_⟩
  · intro i j hij
    exact hc.2.1 (hf.injective.ne hij)
  · apply (closure_mono ?_).trans hc.2.2
    exact iUnion_subset fun n => subset_iUnion (fun n => (c n).2) (f n)

theorem mem_wolfeFamily_limit_monotone (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) {α : Ordinal.{u}} (hα : IsSuccLimit α)
    (p : WolfeNode 𝕜 K) : p ∈ wolfeFamily M ε B α ↔
      p ∈ wolfeBase M ε B ∧
      ∃ a : ℕ → Iio α, Monotone (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧
        ∃ c : ℕ → WolfeNode 𝕜 K,
          (∀ n, c n ∈ wolfeFamily M ε B (a n).val) ∧ WolfeChildren p c := by
  constructor
  · intro hp
    obtain ⟨hp, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα p).mp hp
    exact ⟨hp, a, ha.monotone, hcof, c, hc, hch⟩
  · rintro ⟨hp, a, ha, hcof, c, hc, hch⟩
    obtain ⟨f, hf, haf, hcf⟩ := monotone_cofinal_sequence_strict_refinement hα a ha hcof
    exact (mem_wolfeFamily_limit M ε B hα p).mpr
      ⟨hp, (fun n => a (f n)), haf, hcf, (fun n => c (f n)),
        (fun n => hc (f n)), hch.subsequence hf⟩

end Posets
