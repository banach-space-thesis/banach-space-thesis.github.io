import ThesisCommon.Combinatorics.FiniteRamseyThinning

/-! Finite Ramsey selection for strictly ordered tuples. This form avoids
choosing an ordering when applying homogeneous colors to concrete patterns. -/
noncomputable section
namespace ThesisCommon

def OrderedHomogeneous {C : Type*} {k : ℕ} (c : (Fin k ↪o ℕ) → C)
    (S : Set ℕ) (γ : C) : Prop :=
  ∀ e : Fin k ↪o ℕ, Set.range e ⊆ S → c e = γ

theorem OrderedHomogeneous.mono {C : Type*} {k : ℕ}
    {c : (Fin k ↪o ℕ) → C} {S T : Set ℕ} {γ : C}
    (h : OrderedHomogeneous c S γ) (hTS : T ⊆ S) : OrderedHomogeneous c T γ :=
  fun e he => h e (he.trans hTS)

theorem finite_ordered_ramsey_in_finset (C : Type*) [Finite C] [Nonempty C] (k n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ A : Finset ℕ, N ≤ A.card → ∀ c : (Fin k ↪o ℕ) → C,
      ∃ s : Finset ℕ, s ⊆ A ∧ s.card = n ∧ ∃ γ : C, OrderedHomogeneous c (s : Set ℕ) γ := by
  classical
  obtain ⟨N, hN, hRamsey⟩ := finite_ramsey_in_finset C k n
  refine ⟨N, hN, ?_⟩
  intro A hA c
  let color (u : Finset ℕ) : C := if h : u.card = k then c (u.orderEmbOfFin h) else Classical.arbitrary C
  obtain ⟨s, hs, hscard, γ, hγ⟩ := hRamsey A hA color
  refine ⟨s, hs, hscard, γ, ?_⟩
  intro e he
  let u := Finset.univ.image e
  have hucard : u.card = k := by
    rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]
  have hus : (u : Set ℕ) ⊆ s := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact he ⟨i, rfl⟩
  have heq : e = u.orderEmbOfFin hucard := Finset.orderEmbOfFin_unique' hucard
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hh := hγ u hus hucard
  change (if h : u.card = k then c (u.orderEmbOfFin h) else Classical.arbitrary C) = γ at hh
  rw [dif_pos hucard, ← heq] at hh
  exact hh

end ThesisCommon
