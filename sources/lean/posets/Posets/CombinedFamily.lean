import Posets.MrowkaTopology
import Mathlib.Data.Nat.Pairing

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets

def codedSet (n : ℕ) (A : Set ℕ) : Set ℕ := Nat.pair n '' A

theorem pair_left_injective (n : ℕ) : Function.Injective (Nat.pair n) :=
  fun _ _ h => (Nat.pair_eq_pair.mp h).2

@[simp] theorem mem_codedSet (n m k : ℕ) (A : Set ℕ) :
    Nat.pair n k ∈ codedSet m A ↔ n = m ∧ k ∈ A := by
  simp only [codedSet, Set.mem_image, Nat.pair_eq_pair]
  constructor
  · rintro ⟨j, hj, hmn, hjk⟩
    exact ⟨hmn.symm, hjk ▸ hj⟩
  · rintro ⟨rfl, hk⟩
    exact ⟨k, hk, rfl, rfl⟩

theorem codedSet_infinite (n : ℕ) {A : Set ℕ} (hA : A.Infinite) :
    (codedSet n A).Infinite := hA.image (pair_left_injective n).injOn

variable (𝒜 : ℕ → Set (Set ℕ))

def combinedFamily : Set (Set ℕ) := Set.range (fun p : Σ n, 𝒜 n => codedSet p.1 p.2.val)

def combinedMember (n : ℕ) (A : 𝒜 n) : combinedFamily 𝒜 :=
  ⟨codedSet n A.val, ⟨⟨n, A⟩, rfl⟩⟩

variable (h𝒜 : ∀ n, IsAlmostDisjoint (𝒜 n))

include h𝒜 in
theorem combinedMember_injective : Function.Injective
    (fun p : Σ n, 𝒜 n => combinedMember 𝒜 p.1 p.2) := by
  rintro ⟨n, A⟩ ⟨m, B⟩ h
  have he : codedSet n A.val = codedSet m B.val := congrArg Subtype.val h
  obtain ⟨k, hk⟩ := (h𝒜 n).1 A.val A.property |>.nonempty
  have hm : Nat.pair n k ∈ codedSet m B.val := he ▸ ⟨k, hk, rfl⟩
  have hnm := (mem_codedSet n m k B.val).mp hm |>.1
  subst m
  have hAB : A = B := Subtype.ext ((Set.image_injective.mpr (pair_left_injective n)) he)
  subst B
  rfl

include h𝒜 in
theorem combinedFamily_almostDisjoint : IsAlmostDisjoint (combinedFamily 𝒜) := by
  constructor
  · rintro _ ⟨⟨n, A⟩, rfl⟩
    exact codedSet_infinite n ((h𝒜 n).1 A.val A.property)
  · rintro _ ⟨⟨n, A⟩, rfl⟩ _ ⟨⟨m, B⟩, rfl⟩ hne
    by_cases hnm : n = m
    · subst m
      have hAB : A.val ≠ B.val := fun h => hne (congrArg (codedSet n) h)
      have he : codedSet n A.val ∩ codedSet n B.val = Nat.pair n '' (A.val ∩ B.val) :=
        (Set.image_inter (pair_left_injective n)).symm
      rw [he]
      exact ((h𝒜 n).2 A.val A.property B.val B.property hAB).image _
    · have he : codedSet n A.val ∩ codedSet m B.val = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨k, _, rfl⟩, hx⟩
        exact hnm ((mem_codedSet n m k B.val).mp hx).1
      rw [he]
      exact Set.finite_empty

def combinePoint : (Σ n, Mrowka (𝒜 n)) → Mrowka (combinedFamily 𝒜)
  | ⟨n, Sum.inl k⟩ => Sum.inl (Nat.pair n k)
  | ⟨n, Sum.inr A⟩ => Sum.inr (combinedMember 𝒜 n A)

include h𝒜 in
theorem combinePoint_injective : Function.Injective (combinePoint 𝒜) := by
  rintro ⟨n, p⟩ ⟨m, q⟩ h
  cases p with
  | inl k =>
    cases q with
    | inl l =>
      have he := Nat.pair_eq_pair.mp (Sum.inl.inj h)
      rcases he with ⟨rfl, rfl⟩
      rfl
    | inr B => cases h
  | inr A =>
    cases q with
    | inl l => cases h
    | inr B =>
      have he := @combinedMember_injective 𝒜 h𝒜 ⟨n, A⟩ ⟨m, B⟩ (Sum.inr.inj h)
      exact congrArg (fun p : Σ n, 𝒜 n => (⟨p.1, Sum.inr p.2⟩ : Σ n, Mrowka (𝒜 n))) he

theorem combinePoint_surjective : Function.Surjective (combinePoint 𝒜) := by
  intro p
  cases p with
  | inl k => exact ⟨⟨(Nat.unpair k).1, Sum.inl (Nat.unpair k).2⟩,
      congrArg Sum.inl (Nat.pair_unpair k)⟩
  | inr A =>
    obtain ⟨⟨n, B⟩, h⟩ := A.property
    exact ⟨⟨n, Sum.inr B⟩, congrArg Sum.inr (Subtype.ext h)⟩

end Posets
