import BanachIsometric.FiniteGoodCoverGeometry
import BanachIsometric.RawDegreeHomologyContractible

/-! Finite good-cover induction on actual rational singular homology.
The two open-union estimates are exposed as inputs to this induction lemma. -/

noncomputable section
namespace BanachIsometric.SingularPrism

universe u v

def RawDegreeHomologyBounded (X : Type*) [TopologicalSpace X] (bound : ℕ) : Prop :=
  (∀ n, FiniteDimensional ℚ (RawDegreeHomology X n)) ∧
    ∀ n, bound ≤ n → Subsingleton (RawDegreeHomology X n)

theorem rawDegreeHomologyBounded_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {m : ℕ}
    (h : RawDegreeHomologyBounded Y m) : RawDegreeHomologyBounded X m := by
  constructor
  · intro n
    letI := h.1 n
    exact FiniteDimensional.of_injective (rawDegreeHomologyHomeomorph e n).toLinearMap
      (rawDegreeHomologyHomeomorph e n).injective
  · intro n hn
    letI := h.2 n hn
    exact (rawDegreeHomologyHomeomorph e n).injective.subsingleton

theorem rawDegreeHomologyBounded_of_isEmpty (X : Type*) [TopologicalSpace X] [IsEmpty X]
    (m : ℕ) : RawDegreeHomologyBounded X m := by
  constructor
  · intro n
    letI := rawDegreeHomology_subsingleton_of_isEmpty X n
    infer_instance
  · intro n _
    exact rawDegreeHomology_subsingleton_of_isEmpty X n

theorem rawDegreeHomologyBounded_one_of_empty_or_contractible (X : Type*) [TopologicalSpace X]
    (h : IsEmpty X ∨ ContractibleSpace X) : RawDegreeHomologyBounded X 1 := by
  rcases h with h | h
  · letI := h
    exact rawDegreeHomologyBounded_of_isEmpty X 1
  · letI := h
    constructor
    · exact rawDegreeHomology_finiteDimensional_of_contractible X
    · intro n hn
      cases n with
      | zero => omega
      | succ n => exact rawDegreeHomology_subsingleton_succ_of_contractible X n

theorem rawDegreeHomologyBounded_finite_good_cover_of_union_estimates
    {X : Type u} [TopologicalSpace X] {ι : Type v}
    (hFiniteUnion : ∀ {Y : Type u} [TopologicalSpace Y] (A B : Set Y),
      IsOpen A → IsOpen B → A ∪ B = Set.univ → ∀ n : ℕ,
        FiniteDimensional ℚ (RawDegreeHomology A n) → FiniteDimensional ℚ (RawDegreeHomology B n) →
        (0 < n → FiniteDimensional ℚ (RawDegreeHomology (A ∩ B : Set Y) (n - 1))) →
        FiniteDimensional ℚ (RawDegreeHomology Y n))
    (hVanishingUnion : ∀ {Y : Type u} [TopologicalSpace Y] (A B : Set Y),
      IsOpen A → IsOpen B → A ∪ B = Set.univ → ∀ n : ℕ,
        Subsingleton (RawDegreeHomology A n) → Subsingleton (RawDegreeHomology B n) →
        (0 < n → Subsingleton (RawDegreeHomology (A ∩ B : Set Y) (n - 1))) →
        Subsingleton (RawDegreeHomology Y n))
    (U : ι → Set X) (s : Finset ι) (hU : ∀ i ∈ s, IsOpen (U i))
    (hGood : ∀ t : Finset ι, t ⊆ s → t.Nonempty →
      IsEmpty (finiteCoverIntersection U t) ∨ ContractibleSpace (finiteCoverIntersection U t)) :
    RawDegreeHomologyBounded (finiteCoverUnion U s) s.card := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    rw [finiteCoverUnion_empty]
    letI : IsEmpty (↑(∅ : Set X)) := ⟨fun x => x.property⟩
    exact rawDegreeHomologyBounded_of_isEmpty (↑(∅ : Set X)) _
  | @insert a s ha ih =>
    let A := U a
    let B := finiteCoverUnion U s
    let W := finiteCoverUnion U (insert a s)
    have hW : W = A ∪ B := finiteCoverUnion_insert U a s
    have hA : A ⊆ W := by rw [hW]; exact Set.subset_union_left
    have hB : B ⊆ W := by rw [hW]; exact Set.subset_union_right
    have hoA : IsOpen A := hU a (Finset.mem_insert_self _ _)
    have hoB : IsOpen B := isOpen_finiteCoverUnion U s fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have hAContract : IsEmpty A ∨ ContractibleSpace A := by
      have h := hGood {a} (by
        intro i hi
        have hia := Finset.mem_singleton.mp hi
        subst i
        exact Finset.mem_insert_self _ _) ⟨a, Finset.mem_singleton_self a⟩
      rw [finiteCoverIntersection_singleton] at h
      exact h
    have hAGroup : RawDegreeHomologyBounded A 1 :=
      rawDegreeHomologyBounded_one_of_empty_or_contractible A hAContract
    have hBGroup : RawDegreeHomologyBounded B s.card :=
      ih U (fun i hi => hU i (Finset.mem_insert_of_mem hi))
        (fun t ht hne => hGood t (fun i hi => Finset.mem_insert_of_mem (ht hi)) hne)
    have hIGroup : RawDegreeHomologyBounded (A ∩ B : Set X) s.card := by
      change RawDegreeHomologyBounded (U a ∩ finiteCoverUnion U s : Set X) s.card
      rw [← finiteCoverUnion_inter]
      apply ih (fun i => U a ∩ U i)
      · intro i hi
        exact hoA.inter (hU i (Finset.mem_insert_of_mem hi))
      · intro t ht hne
        rw [finiteCoverIntersection_inter U a hne]
        apply hGood (insert a t)
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (ht hi)
        · exact ⟨a, Finset.mem_insert_self _ _⟩
    let A' : Set W := Subtype.val ⁻¹' A
    let B' : Set W := Subtype.val ⁻¹' B
    have hoA' : IsOpen A' := hoA.preimage continuous_subtype_val
    have hoB' : IsOpen B' := hoB.preimage continuous_subtype_val
    have hcover : A' ∪ B' = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      change x.val ∈ A ∪ B
      rw [← hW]
      exact x.property
    let eA : A' ≃ₜ A := nestedCoverSubtypeHomeomorph hA
    let eB : B' ≃ₜ B := nestedCoverSubtypeHomeomorph hB
    have hI : (A ∩ B : Set X) ⊆ W := fun _ hx => hA hx.1
    let eI : (A' ∩ B' : Set W) ≃ₜ (A ∩ B : Set X) :=
      nestedCoverSubtypeHomeomorph hI
    have hA'Group := rawDegreeHomologyBounded_homeomorph eA hAGroup
    have hB'Group := rawDegreeHomologyBounded_homeomorph eB hBGroup
    have hI'Group := rawDegreeHomologyBounded_homeomorph eI hIGroup
    constructor
    · intro n
      exact hFiniteUnion A' B' hoA' hoB' hcover n (hA'Group.1 n) (hB'Group.1 n)
        (fun _ => hI'Group.1 (n - 1))
    · intro n hn
      have hn' : s.card + 1 ≤ n := by rwa [Finset.card_insert_of_notMem ha] at hn
      exact hVanishingUnion A' B' hoA' hoB' hcover n
        (hA'Group.2 n (by omega)) (hB'Group.2 n (by omega))
        (fun _ => hI'Group.2 (n - 1) (by omega))

end BanachIsometric.SingularPrism
