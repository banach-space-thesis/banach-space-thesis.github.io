import NonCalkinAlgebra.Statements
import Mathlib.Tactic.NormNum

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.CommutationChains
universe u v w

/-- The discrete weak skeleton condition from Farah--Shelah: outside a
countable set of indices, a closed interval has constant relation types
in both argument positions. The chain condition is recorded separately. -/
def WeaklySkeletonLike {V : Type u} {Λ : Type v} [Preorder Λ]
    (R : V → V → Prop) (f : Λ → V) : Prop :=
  ∀ a : V, ∃ S : Set Λ, S.Countable ∧
    ∀ i j : Λ, i ≤ j → Disjoint (Set.Icc i j) S →
      (R a (f i) ↔ R a (f j)) ∧ (R (f i) a ↔ R (f j) a)

def IsRelationChain {V : Type u} {Λ : Type v} [Preorder Λ]
    (R : V → V → Prop) (f : Λ → V) : Prop :=
  ∀ i j : Λ, i < j ↔ R (f i) (f j) ∧ ¬ R (f j) (f i)

def Across {A : Type u} [Mul A] (a b : A × A) : Prop :=
  a.1 * b.2 = b.2 * a.1

def Value {A : Type u} [NormedRing A] (a b : A × A) : ℝ :=
  (1 / 2 : ℝ) * ‖a.1 * b.2 - b.2 * a.1‖

theorem across_iff_value_eq_zero {A : Type u} [NormedRing A] (a b : A × A) :
    Across a b ↔ Value a b = 0 := by
  simp only [Across, Value, mul_eq_zero, norm_eq_zero, sub_eq_zero]
  norm_num

def pairEquiv {A : Type u} {B : Type w} [Ring A] [Ring B]
    (e : A ≃+* B) : A × A ≃ B × B := Equiv.prodCongr e.toEquiv e.toEquiv

/-- Pure algebra is enough to preserve the discrete commutation relation;
neither boundedness nor preservation of the involution is assumed. -/
theorem across_pairEquiv_iff {A : Type u} {B : Type w} [Ring A] [Ring B]
    (e : A ≃+* B) (a b : A × A) :
    Across (pairEquiv e a) (pairEquiv e b) ↔ Across a b := by
  change e a.1 * e b.2 = e b.2 * e a.1 ↔ a.1 * b.2 = b.2 * a.1
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff

theorem weaklySkeletonLike_map {A : Type u} {B : Type w} {Λ : Type v}
    [Ring A] [Ring B] [Preorder Λ] (e : A ≃+* B) (f : Λ → A × A)
    (h : WeaklySkeletonLike Across f) :
    WeaklySkeletonLike Across (pairEquiv e ∘ f) := by
  intro a'
  obtain ⟨a, rfl⟩ := (pairEquiv e).surjective a'
  obtain ⟨S, hS, htypes⟩ := h a
  refine ⟨S, hS, ?_⟩
  intro i j hij hgap
  simpa only [Function.comp_apply, across_pairEquiv_iff] using htypes i j hij hgap

theorem relationChain_map {A : Type u} {B : Type w} {Λ : Type v}
    [Ring A] [Ring B] [Preorder Λ] (e : A ≃+* B) (f : Λ → A × A)
    (h : IsRelationChain Across f) :
    IsRelationChain Across (pairEquiv e ∘ f) := by
  intro i j
  simpa only [Function.comp_apply, across_pairEquiv_iff] using h i j

/-- Equality of the metric commutator values on support-free intervals
implies the discrete skeleton condition with the same countable supports. -/
theorem weaklySkeletonLike_of_value_supports {A : Type u} {Λ : Type v}
    [NormedRing A] [Preorder Λ] (f : Λ → A × A)
    (h : ∀ a : A × A, ∃ S : Set Λ, S.Countable ∧
      ∀ i j : Λ, i ≤ j → Disjoint (Set.Icc i j) S →
        Value a (f i) = Value a (f j) ∧ Value (f i) a = Value (f j) a) :
    WeaklySkeletonLike Across f := by
  intro a
  obtain ⟨S, hS, htypes⟩ := h a
  refine ⟨S, hS, ?_⟩
  intro i j hij hgap
  obtain ⟨hleft, hright⟩ := htypes i j hij hgap
  simp only [across_iff_value_eq_zero, hleft, hright, iff_self, and_self]

/-- The 0/1 commutator table in the AM construction gives the exact
discrete relation chain, including the noncommuting diagonal. -/
theorem relationChain_of_value_table {A : Type u} {Λ : Type v}
    [NormedRing A] [LinearOrder Λ] (f : Λ → A × A)
    (h : ∀ i j : Λ, Value (f i) (f j) = if i < j then 0 else 1) :
    IsRelationChain Across f := by
  have hc : ∀ i j : Λ, Across (f i) (f j) ↔ i < j := by
    intro i j
    rw [across_iff_value_eq_zero, h]
    by_cases hij : i < j <;> simp [hij]
  intro i j
  rw [hc i j, hc j i]
  exact ⟨fun hij => ⟨hij, not_lt_of_ge hij.le⟩, And.left⟩

end NonCalkinAlgebra.CommutationChains
