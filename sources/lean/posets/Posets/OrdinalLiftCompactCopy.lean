import Posets.OrdinalLiftGluing
import Posets.WolfeDirac

/-! Every countable relative derivative rank has a compact witness on which
the original map is injective. The source need not be countable. -/
noncomputable section
open Set Filter Topology Order ThesisCommon
namespace Posets
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Countable Y]

theorem ordinalLift_gluing_properties (f : X → Y) {x : X} {A U : Set X}
    (hxA : x ∈ A) (hxU : x ∈ U) (S V : ℕ → Set X) (W : ℕ → Set Y)
    (hS : ∀ n, IsCompact (S n) ∧ S n ⊆ A ∩ V n ∧ InjOn f (S n))
    (hV : ∀ n, V n ⊆ U ∧ V n ⊆ f ⁻¹' W n ∧
      V n ⊆ Metric.ball x (1 / ((n : ℝ) + 1)))
    (hW : ∀ n, f x ∉ W n) (hd : Pairwise fun n m => Disjoint (W n) (W m)) :
    IsCompact (insert x (⋃ n, S n)) ∧ (insert x (⋃ n, S n)) ⊆ A ∩ U ∧
      InjOn f (insert x (⋃ n, S n)) := by
  refine ⟨ordinalLift_isCompact_insert_iUnion x S (fun n => (hS n).1)
    (fun n y hy => (hV n).2.2 ((hS n).2.1 hy).2), ?_,
    ordinalLift_injOn_insert_iUnion f x S W
      (fun n y hy => (hV n).2.1 ((hS n).2.1 hy).2)
      (fun n => (hS n).2.2) hW hd⟩
  intro y hy
  rcases mem_insert_iff.mp hy with rfl | hy
  · exact ⟨hxA, hxU⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact ⟨((hS n).2.1 hn).1, (hV n).1 ((hS n).2.1 hn).2⟩

theorem ordinalLift_exists_compact_injective_rank (f : X → Y) (hf : Continuous f)
    (A : Set X) (α : Ordinal.{0}) (hc : α.card ≤ Cardinal.aleph0)
    {x : X} (hx : x ∈ ordinalLiftIterate f A α) {U : Set X}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ S : Set X, IsCompact S ∧ S ⊆ A ∩ U ∧ InjOn f S ∧ x ∈ ordinalDerived S α := by
  classical
  induction α using Ordinal.limitRecOn generalizing x U with
  | zero =>
    refine ⟨{x}, isCompact_singleton, ?_, injOn_singleton f x, ?_⟩
    · intro y hy
      rcases mem_singleton_iff.mp hy with rfl
      exact ⟨by simpa using hx, hxU⟩
    · simp
  | succ α ih =>
    have hαc : α.card ≤ Cardinal.aleph0 := (Ordinal.card_le_card (le_succ α)).trans hc
    obtain ⟨z, V, W, hz, hW, hd, ht⟩ := ordinalLiftDerivative_disjoint_sequence f hf
      (fun _ => ordinalLiftIterate f A α) (fun _ => by simpa using hx) hU hxU
    have hex (n : ℕ) := ih hαc (hz n).1 (hz n).2.2.1 (hz n).2.1
    choose S hSc hSsub hSi hSr using hex
    let C := insert x (⋃ n, S n)
    have hC := ordinalLift_gluing_properties f (ordinalLiftIterate_subset f A _ hx) hxU S V W
      (fun n => ⟨hSc n, hSsub n, hSi n⟩)
      (fun n => (hz n).2.2.2) (fun n => (hW n).2) hd
    refine ⟨C, hC.1, hC.2.1, hC.2.2, ?_⟩
    rw [ordinalDerived_succ]
    apply ordinalLift_mem_derivedSet_of_tendsto z ht
    · intro n he
      exact (hW n).2 (he ▸ (hz n).2.2.2.2.1 (hz n).2.1)
    · apply Eventually.of_forall
      intro n
      exact ordinalDerived_mono (fun y hy => mem_insert_of_mem x (mem_iUnion.mpr ⟨n, hy⟩)) α (hSr n)
  | limit α hα ih =>
    obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα hc
    have hx' (n : ℕ) : x ∈ ordinalLiftDerivative f (ordinalLiftIterate f A (a n).val) := by
      rw [← ordinalLiftIterate_succ]
      exact ordinalLiftIterate_antitone f A (hα.succ_lt (a n).property).le hx
    obtain ⟨z, V, W, hz, hW, hd, ht⟩ := ordinalLiftDerivative_disjoint_sequence f hf
      (fun n => ordinalLiftIterate f A (a n).val) hx' hU hxU
    have hex (n : ℕ) := ih (a n).val (a n).property
      ((Ordinal.card_le_card (a n).property.le).trans hc) (hz n).1 (hz n).2.2.1 (hz n).2.1
    choose S hSc hSsub hSi hSr using hex
    let C := insert x (⋃ n, S n)
    have hC := ordinalLift_gluing_properties f (ordinalLiftIterate_subset f A _ hx) hxU S V W
      (fun n => ⟨hSc n, hSsub n, hSi n⟩)
      (fun n => (hz n).2.2.2) (fun n => (hW n).2) hd
    refine ⟨C, hC.1, hC.2.1, hC.2.2, ?_⟩
    rw [ordinalDerived_limit C hα]
    apply mem_iInter₂.mpr
    intro β hβ
    obtain ⟨N, hN⟩ := hcof β hβ
    apply (isClosed_ordinalDerived hC.1.isClosed β).mem_of_tendsto ht
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    apply ordinalDerived_antitone hC.1.isClosed (hN.trans (ha.monotone hn))
    exact ordinalDerived_mono (fun y hy => mem_insert_of_mem x (mem_iUnion.mpr ⟨n, hy⟩))
      (a n).val (hSr n)

end Posets
