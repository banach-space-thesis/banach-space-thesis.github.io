import ThesisCommon.Analysis.SetMappingDefinitions
import Mathlib.Order.Zorn

/-! Maximal free subsets, used in the cofinality case of Hajnal's theorem.
The existence proof is Zorn's lemma on the actual family of free subsets;
no free-set cardinality conclusion is assumed. -/
noncomputable section
namespace ThesisCommon
universe u
variable {Γ : Type u} {F : Γ → Set Γ} {S H : Set Γ}

theorem IsSetMappingFree.mono (hH : IsSetMappingFree F H)
    {K : Set Γ} (hKH : K ⊆ H) : IsSetMappingFree F K := by
  intro a ha b hb hab
  exact hH a (hKH ha) b (hKH hb) hab

theorem IsSetMappingFree.insert (hH : IsSetMappingFree F H) (x : Γ)
    (hx : ∀ y ∈ H, x ∉ F y ∧ y ∉ F x) : IsSetMappingFree F (insert x H) := by
  rintro a (rfl | ha) b (rfl | hb) hab
  · exact (hab rfl).elim
  · exact hx b hb
  · exact (hx a ha).symm
  · exact hH a ha b hb hab

theorem isSetMappingFree_sUnion (C : Set (Set Γ))
    (hC : ∀ A ∈ C, IsSetMappingFree F A)
    (hchain : IsChain (· ⊆ ·) C) : IsSetMappingFree F (⋃₀ C) := by
  rintro a ⟨A, hAC, ha⟩ b ⟨B, hBC, hb⟩ hab
  rcases eq_or_ne A B with rfl | hAB
  · exact hC A hAC a ha b hb hab
  · rcases hchain hAC hBC hAB with hsub | hsub
    · exact hC B hBC a (hsub ha) b hb hab
    · exact hC A hAC a ha b (hsub hb) hab

theorem exists_maximal_setMappingFree (F : Γ → Set Γ) (S : Set Γ) :
    ∃ H : Set Γ, Maximal (fun H => H ⊆ S ∧ IsSetMappingFree F H) H := by
  apply zorn_subset {H : Set Γ | H ⊆ S ∧ IsSetMappingFree F H}
  intro C hC hchain
  refine ⟨⋃₀ C, ⟨?_, isSetMappingFree_sUnion C (fun A hA => (hC hA).2) hchain⟩,
    fun A hA => Set.subset_sUnion_of_mem hA⟩
  rintro x ⟨A, hAC, hx⟩
  exact (hC hAC).1 hx

/-- Maximality forces an interaction with every point of S outside H. -/
theorem maximal_setMappingFree_interaction
    (hH : Maximal (fun H => H ⊆ S ∧ IsSetMappingFree F H) H)
    {x : Γ} (hxS : x ∈ S) (hxH : x ∉ H) :
    ∃ y ∈ H, x ∈ F y ∨ y ∈ F x := by
  classical
  by_contra hn
  apply hxH
  apply hH.mem_of_prop_insert
  refine ⟨Set.insert_subset hxS hH.prop.1, hH.prop.2.insert x ?_⟩
  intro y hy
  exact ⟨fun hxy => hn ⟨y, hy, Or.inl hxy⟩,
    fun hyx => hn ⟨y, hy, Or.inr hyx⟩⟩

theorem maximal_setMappingFree_hits
    (hH : Maximal (fun H => H ⊆ S ∧ IsSetMappingFree F H) H)
    {x : Γ} (hxS : x ∈ S) (hxH : x ∉ H)
    (hout : ∀ y ∈ H, x ∉ F y) : ∃ y ∈ H, y ∈ F x := by
  obtain ⟨y, hy, hxy | hyx⟩ := maximal_setMappingFree_interaction hH hxS hxH
  · exact (hout y hy hxy).elim
  · exact ⟨y, hy, hyx⟩

end ThesisCommon
