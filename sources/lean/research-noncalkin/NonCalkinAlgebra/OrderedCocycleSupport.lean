import NonCalkinAlgebra.OrderedCocycleNondegenerate

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.OrderedCocycle
open FiniteSupportCocycle
universe u
variable (Λ : Type u) [LinearOrder Λ]

def orderSupport (x : Group Λ) : Finset Λ := by
  classical
  exact x.1.1.support.image Prod.fst ∪ x.1.2.support ∪ x.2.support.image Prod.fst

theorem first_mem_orderSupport (x : Group Λ) (i : Λ × ℕ) (hi : x.1.1 i ≠ 0) :
    i.1 ∈ orderSupport Λ x := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩))

theorem middle_mem_orderSupport (x : Group Λ) (i : Λ) (hi : x.1.2 i ≠ 0) :
    i ∈ orderSupport Λ x := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hi))

theorem last_mem_orderSupport (x : Group Λ) (i : Λ × ℕ) (hi : x.2 i ≠ 0) :
    i.1 ∈ orderSupport Λ x := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩)

@[simp] theorem alternating_u (x : Group Λ) (ξ : Λ) :
    alternating Λ x (u Λ ξ) =
      x.2.sum (fun j b => b * (if j.1 ≤ ξ then 1 else 0)) := by
  simpa [alternating, cocycle, u, crossPairing, orderEntry] using
    pairing_left_single (orderEntry Λ) ξ x.2

theorem le_tests_constant {i j η : Λ} (hij : i ≤ j) (hη : η ∉ Set.Icc i j) :
    (i ≤ η ↔ j ≤ η) ∧ (η ≤ i ↔ η ≤ j) := by
  constructor
  · constructor
    · intro hi
      by_contra hj
      exact hη ⟨hi, (lt_of_not_ge hj).le⟩
    · exact fun hj => hij.trans hj
  · constructor
    · exact fun hi => hi.trans hij
    · intro hj
      by_contra hi
      exact hη ⟨(lt_of_not_ge hi).le, hj⟩

/-- A gap avoiding the finite order support has the same alternating
character against either kind of chain generator at its two endpoints. -/
theorem alternating_constant_on_gap (x : Group Λ) {i j : Λ} (hij : i ≤ j)
    (hgap : ∀ η ∈ orderSupport Λ x, η ∉ Set.Icc i j) :
    alternating Λ x (w Λ i 0) = alternating Λ x (w Λ j 0) ∧
      alternating Λ x (u Λ i) = alternating Λ x (u Λ j) := by
  classical
  have hfirst_i : x.1.1 (i, 0) = 0 := by
    by_contra hi
    exact hgap i (first_mem_orderSupport Λ x (i, 0) hi) ⟨le_rfl, hij⟩
  have hfirst_j : x.1.1 (j, 0) = 0 := by
    by_contra hj
    exact hgap j (first_mem_orderSupport Λ x (j, 0) hj) ⟨hij, le_rfl⟩
  constructor
  · rw [alternating_w, alternating_w, hfirst_i, hfirst_j]
    congr 1
    apply Finset.sum_congr rfl
    intro η hη
    have ht := (le_tests_constant Λ hij (hgap η
      (middle_mem_orderSupport Λ x η (Finsupp.mem_support_iff.mp hη)))).1
    simp only [ht]
  · rw [alternating_u, alternating_u]
    apply Finset.sum_congr rfl
    intro η hη
    have ht := (le_tests_constant Λ hij (hgap η.1
      (last_mem_orderSupport Λ x η (Finsupp.mem_support_iff.mp hη)))).2
    simp only [ht]

end NonCalkinAlgebra.OrderedCocycle
