import Posets.WolfeRankedFamily

/-! Every row in a ranked family is approximated by rows from any prescribed
lower level whose cells are contained in its cell. This is the closure form
of the downward approximation used in Wolfe's tower-pruning argument. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K P : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem rankedWolfeFamily_closed_lower
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (β : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves β)
    {α : Ordinal.{u}} (hαβ : α ≤ β)
    (C : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (hC : IsClosed C)
    (hlower : ∀ q ∈ rankedWolfeFamily v height B Leaves α,
      (v q).2 ⊆ (v p).2 → (v q).1 ∈ C) : (v p).1 ∈ C := by
  induction β using Ordinal.limitRecOn generalizing p α with
  | zero =>
      have hα : α = 0 := le_antisymm hαβ (Ordinal.zero_le _)
      subst α
      exact hlower p hp Subset.rfl
  | succ β ih =>
      by_cases heq : α = succ β
      · subst α
        exact hlower p hp Subset.rfl
      have hα : α ≤ β := Order.lt_succ_iff.mp (lt_of_le_of_ne hαβ heq)
      obtain ⟨_, _, c, hc, hch⟩ := (mem_rankedWolfeFamily_succ v height B Leaves β p).mp hp
      apply hC.mem_of_tendsto hch.1
      apply Eventually.of_forall
      intro n
      exact ih (hc n) hα (fun q hq hqp => hlower q hq (hqp.trans (hch.child_subset n)))
  | limit β hβ ih =>
      by_cases heq : α = β
      · subst α
        exact hlower p hp Subset.rfl
      have hα : α < β := lt_of_le_of_ne hαβ heq
      obtain ⟨_, _, a, ha, hcof, c, hc, hch⟩ :=
        (mem_rankedWolfeFamily_limit v height B Leaves hβ p).mp hp
      obtain ⟨n₀, hn₀⟩ := hcof α hα
      apply hC.mem_of_tendsto hch.1
      filter_upwards [eventually_ge_atTop n₀] with n hn
      exact ih (a n).val (a n).property (hc n) (hn₀.trans (ha.monotone hn))
        (fun q hq hqp => hlower q hq (hqp.trans (hch.child_subset n)))

theorem rankedWolfeFamily_mem_closure_lower
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (β : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves β)
    {α : Ordinal.{u}} (hαβ : α ≤ β) :
    (v p).1 ∈ closure {μ | ∃ q ∈ rankedWolfeFamily v height B Leaves α,
      (v q).2 ⊆ (v p).2 ∧ (v q).1 = μ} := by
  apply rankedWolfeFamily_closed_lower v height B Leaves β hp hαβ _ isClosed_closure
  intro q hq hqp
  exact subset_closure ⟨q, hq, hqp, rfl⟩

theorem rankedWolfeFamily_exists_lower
    (v : P → WolfeNode 𝕜 K) (height : P → Ordinal.{u}) (B Leaves : Set P)
    (β : Ordinal.{u}) {p : P} (hp : p ∈ rankedWolfeFamily v height B Leaves β)
    {α : Ordinal.{u}} (hαβ : α ≤ β) :
    ∃ q ∈ rankedWolfeFamily v height B Leaves α, (v q).2 ⊆ (v p).2 := by
  by_contra hn
  have hempty : {μ | ∃ q ∈ rankedWolfeFamily v height B Leaves α,
      (v q).2 ⊆ (v p).2 ∧ (v q).1 = μ} = (∅ : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro μ ⟨q, hq, hqp, _⟩
    exact hn ⟨q, hq, hqp⟩
  have h := rankedWolfeFamily_mem_closure_lower v height B Leaves β hp hαβ
  simp only [hempty, closure_empty, mem_empty_iff_false] at h

end Posets
