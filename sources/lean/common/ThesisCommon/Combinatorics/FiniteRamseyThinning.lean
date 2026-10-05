import ThesisCommon.Combinatorics.FiniteRamsey
import Mathlib.Data.Finset.Sort

/-! Ramsey selection inside any sufficiently large finite set. The size is
chosen before both the ambient set and coloring, allowing repeated thinning. -/
noncomputable section
namespace ThesisCommon

theorem FinsetHomogeneous.mono {C : Type*} {c : Finset ℕ → C} {k : ℕ}
    {S T : Set ℕ} {γ : C} (h : FinsetHomogeneous c k S γ) (hTS : T ⊆ S) :
    FinsetHomogeneous c k T γ :=
  fun u hu hcard => h u (hu.trans hTS) hcard

theorem finite_ramsey_in_finset (C : Type*) [Finite C] (k n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ A : Finset ℕ, N ≤ A.card → ∀ c : Finset ℕ → C,
      ∃ s : Finset ℕ, s ⊆ A ∧ s.card = n ∧
        ∃ γ : C, FinsetHomogeneous c k (s : Set ℕ) γ := by
  classical
  obtain ⟨N, hN, hRamsey⟩ := finite_ramsey C k n
  refine ⟨N, hN, ?_⟩
  intro A hA c
  let f : ℕ → ℕ := fun i => if hi : i < A.card then A.orderEmbOfFin rfl ⟨i, hi⟩ else 0
  have hf (i : ℕ) (hi : i < N) : f i ∈ A := by
    have hiA := lt_of_lt_of_le hi hA
    simpa only [f, dif_pos hiA] using A.orderEmbOfFin_mem rfl ⟨i, hiA⟩
  have hinj : Set.InjOn f (Finset.range N : Set ℕ) := by
    intro i hi j hj hij
    have hiA : i < A.card := lt_of_lt_of_le (Finset.mem_range.mp hi) hA
    have hjA : j < A.card := lt_of_lt_of_le (Finset.mem_range.mp hj) hA
    simp only [f, dif_pos hiA, dif_pos hjA] at hij
    exact congrArg Fin.val ((A.orderEmbOfFin rfl).injective hij)
  obtain ⟨s, hs, hscard, γ, hγ⟩ := hRamsey (fun u => c (u.image f))
  have hsinj : Set.InjOn f (s : Set ℕ) := hinj.mono hs
  refine ⟨s.image f, ?_, (Finset.card_image_of_injOn hsinj).trans hscard, γ, ?_⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hf i (Finset.mem_range.mp (hs hi))
  · intro v hv hvcard
    obtain ⟨u, hus, huv⟩ := Finset.subset_image_iff.mp hv
    have hucard : u.card = k := by
      rw [← Finset.card_image_of_injOn (hsinj.mono hus), huv, hvcard]
    simpa only [huv] using hγ u hus hucard

end ThesisCommon
