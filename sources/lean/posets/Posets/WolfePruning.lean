import Posets.WolfeMassBounds
import Posets.WolfeMonotonicity

/-! Disjoint children can be pruned so that their entire union has arbitrarily
small mass for a prescribed functional. Finite atomic approximation controls
the union, not only the mass of each individual child. This is the pruning
estimate used at every node in Wolfe's construction. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
variable (M : JLMS.AtomicDualModel 𝕜 K)
local instance wolfePruningDualGroup : NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance wolfePruningDualSpace : NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

omit [TopologicalSpace K] in
theorem disjointSequence_eventually_avoids_finset (U : ℕ → Set K)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) (s : Finset K) :
    ∀ᶠ n in atTop, ∀ x ∈ s, x ∉ U n := by
  classical
  have hx (x : K) : ∀ᶠ n in atTop, x ∉ U n := by
    have hfinite : {n | x ∈ U n}.Finite := Set.Subsingleton.finite (by
      intro i hi j hj
      by_contra hij
      exact Set.disjoint_left.mp (hd hij) hi hj)
    simpa only [Nat.cofinite_eq_atTop, mem_setOf_eq] using hfinite.eventually_cofinite_notMem
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      filter_upwards [hx x, ih] with n hxn hsn
      simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hxn hsn

theorem wolfeMass_disjoint_tail_union_small
    (μ : WeakDual 𝕜 (JLMS.CZero 𝕜 K)) (U : ℕ → Set K)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, wolfeMass M μ (⋃ n, U (n + N)) < η := by
  obtain ⟨s, hs⟩ := JLMS.exists_finite_atomicRestriction_tail M (WeakDual.toStrongDual μ) hη
  rw [JLMS.atomicRestriction_compl] at hs
  have hs' : wolfeMass M μ (s : Set K)ᶜ < η := hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp (disjointSequence_eventually_avoids_finset U hd s)
  refine ⟨N, (wolfeMass_mono M μ ?_).trans_lt hs'⟩
  intro x hx hxmem
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact hN (n + N) (Nat.le_add_left N n) x hxmem hn

theorem wolfeFamily_successor_small_children {ε η : ℝ} (hη : 0 < η)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u})
    {p : WolfeNode 𝕜 K} (hp : p ∈ wolfeFamily M ε B (succ α)) :
    ∃ c : ℕ → WolfeNode 𝕜 K, (∀ n, c n ∈ wolfeFamily M ε B α) ∧
      WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η := by
  obtain ⟨_, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
  obtain ⟨N, hN⟩ := wolfeMass_disjoint_tail_union_small M p.1 (fun n => (c n).2) hch.2.1 hη
  exact ⟨(fun n => c (n + N)), (fun n => hc (n + N)), hch.tail N, hN⟩

theorem wolfeFamily_limit_small_children {ε η : ℝ} (hη : 0 < η)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) {α : Ordinal.{u}} (hα : IsSuccLimit α)
    {p : WolfeNode 𝕜 K} (hp : p ∈ wolfeFamily M ε B α) :
    ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
      (∀ β < α, ∃ n, β ≤ (a n).val) ∧
      ∃ c : ℕ → WolfeNode 𝕜 K, (∀ n, c n ∈ wolfeFamily M ε B (a n).val) ∧
        WolfeChildren p c ∧ wolfeMass M p.1 (⋃ n, (c n).2) < η := by
  obtain ⟨_, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα p).mp hp
  obtain ⟨N, hN⟩ := wolfeMass_disjoint_tail_union_small M p.1 (fun n => (c n).2) hch.2.1 hη
  refine ⟨(fun n => a (n + N)), ?_, ?_, (fun n => c (n + N)),
    (fun n => hc (n + N)), hch.tail N, hN⟩
  · intro i j hij
    exact ha (Nat.add_lt_add_right hij N)
  · intro β hβ
    obtain ⟨n, hn⟩ := hcof β hβ
    exact ⟨n, hn.trans (ha.monotone (Nat.le_add_right n N))⟩

end Posets
