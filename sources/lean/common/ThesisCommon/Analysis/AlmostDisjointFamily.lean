import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-! A continuum-sized almost-disjoint family inside every infinite subset of ℕ. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

def branchCode (f : ℕ → Bool) (n : ℕ) : ℕ :=
  Encodable.encode (List.ofFn (fun i : Fin n => f i.val))

def branchSet (f : ℕ → Bool) : Set ℕ := Set.range (branchCode f)

theorem branchCode_injective (f : ℕ → Bool) : Function.Injective (branchCode f) := by
  intro n m h
  have hl := congrArg List.length (Encodable.encode_injective h)
  simpa only [List.length_ofFn] using hl

theorem branchSet_infinite (f : ℕ → Bool) : (branchSet f).Infinite :=
  Set.infinite_range_of_injective (branchCode_injective f)

theorem branchSet_inter_finite {f g : ℕ → Bool} (hfg : f ≠ g) :
    (branchSet f ∩ branchSet g).Finite := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := Function.ne_iff.mp hfg
  apply ((Finset.range (k+1)).finite_toSet.image (branchCode f)).subset
  rintro x ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
  have heq : List.ofFn (fun i : Fin n => f i.val) = List.ofFn (fun i : Fin m => g i.val) :=
    Encodable.encode_injective (hn.trans hm.symm)
  have hnm : n = m := by simpa only [List.length_ofFn] using congrArg List.length heq
  subst m
  have hnle : n ≤ k := by
    by_contra h
    have hkn : k < n := lt_of_not_ge h
    exact hk (congrFun (List.ofFn_injective heq) ⟨k, hkn⟩)
  exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hnle), hn⟩

theorem continuum_almostDisjoint_subsets (C : Set ℕ) (hC : C.Infinite) :
    ∃ S : Set (Set ℕ), #S = 𝔠 ∧
      (∀ A ∈ S, A ⊆ C ∧ A.Infinite) ∧
      S.Pairwise (fun A B => (A ∩ B).Finite) := by
  classical
  let q : ℕ → ℕ := fun n => (hC.natEmbedding C n).val
  have hq : Function.Injective q := Subtype.val_injective.comp (hC.natEmbedding C).injective
  let R : (ℕ → Bool) → Set ℕ := fun f => q '' branchSet f
  have hRinf (f : ℕ → Bool) : (R f).Infinite := (branchSet_infinite f).image hq.injOn
  have hRsub (f : ℕ → Bool) : R f ⊆ C := by
    rintro _ ⟨n, _, rfl⟩
    exact (hC.natEmbedding C n).property
  have hRint (f g : ℕ → Bool) (hfg : f ≠ g) : (R f ∩ R g).Finite := by
    change (q '' branchSet f ∩ q '' branchSet g).Finite
    rw [← Set.image_inter hq]
    exact (branchSet_inter_finite hfg).image q
  have hRinj : Function.Injective R := by
    intro f g heq
    by_contra hfg
    have hfin := hRint f g hfg
    rw [← heq, Set.inter_self] at hfin
    exact hRinf f hfin
  refine ⟨Set.range R, ?_, ?_, ?_⟩
  · rw [Cardinal.mk_range_eq R hRinj]
    simp only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id]
    rfl
  · rintro _ ⟨f, rfl⟩
    exact ⟨hRsub f, hRinf f⟩
  · rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ hfg
    exact hRint f g (fun h => hfg (congrArg R h))

/-- Choosing an infinite subset of each member preserves the cardinality and
almost-disjointness of the family. -/
theorem almostDisjoint_thinning {α : Type*} (S : Set (Set α))
    (hS : S.Pairwise (fun A B => (A ∩ B).Finite))
    (K : S → Set α) (hsub : ∀ A, K A ⊆ A.val) (hinf : ∀ A, (K A).Infinite) :
    Function.Injective K ∧ #(Set.range K) = #S ∧
      (Set.range K).Pairwise (fun A B => (A ∩ B).Finite) := by
  have hfinite (A B : S) (hne : A ≠ B) : (K A ∩ K B).Finite :=
    (hS A.property B.property (fun h => hne (Subtype.ext h))).subset
      (Set.inter_subset_inter (hsub A) (hsub B))
  have hi : Function.Injective K := by
    intro A B heq
    by_contra hne
    have hf := hfinite A B hne
    rw [← heq, Set.inter_self] at hf
    exact hinf A hf
  refine ⟨hi, Cardinal.mk_range_eq K hi, ?_⟩
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ hne
  exact hfinite A B (fun h => hne (congrArg K h))

end ThesisCommon
