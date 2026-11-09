import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# A continuum-sized almost-disjoint family

An infinite binary sequence determines the natural-number codes of all its finite
prefixes. These sets are infinite, whereas two different sequences share only
finitely many prefixes. The construction is independent of the analytic part of
the operator-ideal theorem.
-/

noncomputable section

namespace PL1CD.AlmostDisjoint

abbrev BinarySequence := ℕ → Bool

/-- The first `n` entries of an infinite binary sequence. -/
def finitePrefix (ξ : BinarySequence) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => ξ i)

/-- A natural-number code for a finite binary prefix. -/
def prefixCode (ξ : BinarySequence) (n : ℕ) : ℕ :=
  Encodable.encode (finitePrefix ξ n)

/-- The infinite subset of natural numbers associated with a binary sequence. -/
def family (ξ : BinarySequence) : Set ℕ := Set.range (prefixCode ξ)

theorem prefixCode_eq_length {ξ η : BinarySequence} {n m : ℕ}
    (h : prefixCode ξ n = prefixCode η m) : n = m := by
  have hp : finitePrefix ξ n = finitePrefix η m := Encodable.encode_injective h
  simpa [finitePrefix] using congrArg List.length hp

theorem prefixCode_injective (ξ : BinarySequence) : Function.Injective (prefixCode ξ) :=
  fun _ _ h => prefixCode_eq_length h

theorem prefixCode_eq_apply {ξ η : BinarySequence} {n i : ℕ}
    (h : prefixCode ξ n = prefixCode η n) (hi : i < n) : ξ i = η i := by
  have hp : finitePrefix ξ n = finitePrefix η n := Encodable.encode_injective h
  exact congrFun (List.ofFn_injective hp) ⟨i, hi⟩

theorem family_infinite (ξ : BinarySequence) : (family ξ).Infinite :=
  Set.infinite_range_of_injective (prefixCode_injective ξ)

theorem family_inter_finite {ξ η : BinarySequence} (h : ξ ≠ η) :
    (family ξ ∩ family η).Finite := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, ξ k ≠ η k := Function.ne_iff.mp h
  apply ((Set.finite_lt_nat (k + 1)).image (prefixCode ξ)).subset
  intro z hz
  obtain ⟨n, rfl⟩ := hz.1
  obtain ⟨m, hm⟩ := hz.2
  have hmn : m = n := prefixCode_eq_length hm
  subst m
  refine ⟨n, ?_, rfl⟩
  apply Nat.lt_succ_of_le
  by_contra hnk
  exact hk (prefixCode_eq_apply hm.symm (Nat.lt_of_not_ge hnk))

theorem family_injective : Function.Injective family := by
  intro ξ η h
  by_contra hne
  apply family_infinite ξ
  simpa [← h] using family_inter_finite hne

/-- Thus the family is indexed injectively by a set of cardinality continuum. -/
def familyEmbedding : BinarySequence ↪ Set ℕ := ⟨family, family_injective⟩

theorem index_cardinality : Cardinal.mk BinarySequence = Cardinal.continuum := by
  simp [BinarySequence]

/-- A member retains infinitely many indices after deleting any finite collection
of other members. This is the set-theoretic input to operator separation. -/
theorem family_diff_biUnion_infinite (ξ : BinarySequence) (F : Finset BinarySequence)
    (hξ : ξ ∉ F) : (family ξ \ ⋃ η ∈ F, family η).Infinite := by
  classical
  have hfinite : (⋃ η ∈ F, family ξ ∩ family η).Finite :=
    F.finite_toSet.biUnion fun η hη => family_inter_finite (by
      intro heq
      exact hξ (heq ▸ hη))
  have hinfinite := (family_infinite ξ).sdiff hfinite
  convert hinfinite using 1
  ext n
  simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨hn, hnot⟩
    refine ⟨hn, ?_⟩
    rintro ⟨η, hη, _, hnη⟩
    exact hnot ⟨η, hη, hnη⟩
  · rintro ⟨hn, hnot⟩
    refine ⟨hn, ?_⟩
    rintro ⟨η, hη, hnη⟩
    exact hnot ⟨η, hη, hn, hnη⟩

end PL1CD.AlmostDisjoint
