import JLMS.ScatteredSequences

/-!
# Disjoint neighborhoods along a convergent point sequence

At each finite stage the used compact sets avoid the limit. Convergence
therefore supplies a later point outside them. Shrinking a compact clopen
neighborhood away from the old region and the limit preserves this invariant.
-/

noncomputable section

open Set Filter Topology

namespace JLMS

variable {K : Type*} [TopologicalSpace K] [LocallyCompactSpace K] [T2Space K]

structure PointNeighborhoodHistory (x : OnePoint K) where
  used : Set (OnePoint K)
  compact_used : IsCompact used
  avoid_limit : x ∉ used
  lower : ℕ

/-- One finite-history selection step. -/
theorem exists_pointNeighborhoodStep (hK : IsScattered K) (p : ℕ → K)
    (hp : Function.Injective p) (x : OnePoint K)
    (ht : Tendsto (fun n => (p n : OnePoint K)) atTop (𝓝 x))
    (S : PointNeighborhoodHistory x) :
    ∃ m : ℕ, ∃ U : Set K, S.lower < m ∧ IsClopen U ∧ IsCompact U ∧ p m ∈ U ∧
      Disjoint (OnePoint.some '' U) S.used ∧ x ∉ OnePoint.some '' U := by
  have hcoeinj : Function.Injective (fun n => (p n : OnePoint K)) :=
    OnePoint.coe_injective.comp hp
  have hneq : ∀ᶠ n in atTop, (p n : OnePoint K) ≠ x := by
    have h := hcoeinj.tendsto_cofinite (Set.finite_singleton x).compl_mem_cofinite
    simpa only [mem_compl_iff, mem_singleton_iff, Nat.cofinite_eq_atTop] using h
  have hout : ∀ᶠ n in atTop, (p n : OnePoint K) ∉ S.used :=
    ht.eventually (S.compact_used.isClosed.isOpen_compl.mem_nhds S.avoid_limit)
  obtain ⟨m, hm, hmx, hmout⟩ :=
    ((eventually_gt_atTop S.lower).and (hneq.and hout)).exists
  let O : Set (OnePoint K) := S.usedᶜ ∩ ({x} : Set (OnePoint K))ᶜ
  have hO : IsOpen O := S.compact_used.isClosed.isOpen_compl.inter isClosed_singleton.isOpen_compl
  have hpm : p m ∈ OnePoint.some ⁻¹' O := ⟨hmout, hmx⟩
  obtain ⟨U, hU, hcU, hpU, hUO⟩ := exists_compact_clopen_subset hK
    (hO.preimage OnePoint.continuous_coe) hpm
  refine ⟨m, U, hm, hU, hcU, hpU, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro z ⟨y, hy, rfl⟩ hz
    exact (hUO hy).1 hz
  · rintro ⟨y, hy, he⟩
    exact (hUO hy).2 he

/-- Select a subsequence with disjoint compact clopen neighborhoods,
all avoiding the limit in the one-point compactification. -/
theorem exists_disjoint_pointNeighborhoods (hK : IsScattered K) (p : ℕ → K)
    (hp : Function.Injective p) (x : OnePoint K)
    (ht : Tendsto (fun n => (p n : OnePoint K)) atTop (𝓝 x)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ U : ℕ → Set K,
      (∀ n, IsClopen (U n)) ∧ (∀ n, IsCompact (U n)) ∧
      (∀ n, p (s n) ∈ U n) ∧ (Pairwise fun i j => Disjoint (U i) (U j)) := by
  classical
  choose m U hm hU hcU hpU hdisjoint havoid using
    exists_pointNeighborhoodStep hK p hp x ht
  let advance (S : PointNeighborhoodHistory x) : PointNeighborhoodHistory x :=
    { used := S.used ∪ OnePoint.some '' U S
      compact_used := S.compact_used.union ((hcU S).image OnePoint.continuous_coe)
      avoid_limit := fun h => h.elim S.avoid_limit (havoid S)
      lower := m S }
  let S : ℕ → PointNeighborhoodHistory x := Nat.rec
    ⟨∅, isCompact_empty, notMem_empty x, 0⟩ (fun _ state => advance state)
  have hstep (n : ℕ) : (S (n + 1)).used = (S n).used ∪ OnePoint.some '' U (S n) := rfl
  have hmono : Monotone (fun n => (S n).used) := monotone_nat_of_le_succ (fun n => by
    rw [hstep]
    exact subset_union_left)
  have hin (n : ℕ) : OnePoint.some '' U (S n) ⊆ (S (n + 1)).used := by
    rw [hstep]
    exact subset_union_right
  refine ⟨fun n => m (S n), strictMono_nat_of_lt_succ (fun n => hm (S (n + 1))),
    fun n => U (S n), fun n => hU _, fun n => hcU _, fun n => hpU _, ?_⟩
  have hforward (i j : ℕ) (hij : i < j) : Disjoint (U (S i)) (U (S j)) := by
    apply disjoint_left.mpr
    intro y hyi hyj
    exact disjoint_left.mp (hdisjoint (S j)) ⟨y, hyj, rfl⟩
      (hmono (Nat.succ_le_of_lt hij) (hin i ⟨y, hyi, rfl⟩))
  intro i j hij
  obtain hlt | hgt := lt_or_gt_of_ne hij
  · exact hforward i j hlt
  · exact (hforward j i hgt).symm

end JLMS
