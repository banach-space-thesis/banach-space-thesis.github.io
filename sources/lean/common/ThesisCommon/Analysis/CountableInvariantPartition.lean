import ThesisCommon.Analysis.CountableTriangularPartition

/-! Closing the first-unused blocks under a symmetric countable relation
makes every block invariant. No cardinality restriction is necessary. -/
noncomputable section
namespace ThesisCommon
universe u
variable {Γ : Type u}

theorem countable_invariant_partition (F : Γ → Set Γ)
    (hF : ∀ x, (F x).Countable) (hsymm : ∀ x y, y ∈ F x → x ∈ F y) :
    ∃ B : (Cardinal.mk Γ).ord.toType → Set Γ,
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i, (B i).Countable) ∧ (⋃ i, B i) = Set.univ ∧
      ∀ i x, x ∈ B i → F x ⊆ B i := by
  obtain ⟨B, hdisj, hcount, hcover, htri⟩ := countable_triangular_partition F hF
  refine ⟨B, hdisj, hcount, hcover, ?_⟩
  intro i x hxi y hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (htri i x hxi hy)
  obtain ⟨hji, hyj⟩ := Set.mem_iUnion.mp hj
  rcases lt_or_eq_of_le hji with hji | rfl
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (htri j y hyj (hsymm x y hy))
    obtain ⟨hkj, hxk⟩ := Set.mem_iUnion.mp hk
    exact (Set.disjoint_left.mp (hdisj (hkj.trans_lt hji).ne) hxk hxi).elim
  · exact hyj

end ThesisCommon
