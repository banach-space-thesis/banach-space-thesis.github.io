import BanachIsometric.FiniteGoodCoverInduction
import BanachIsometric.FiniteNerveStarIntersections
import BanachIsometric.RawUnionHomologyFiniteness

/-! Actual rational singular homology of a finite coordinate polyhedron is
finite-dimensional and vanishes in degrees at least its vertex count. -/

noncomputable section
namespace BanachIsometric.FiniteNerve.Complex

open SingularPrism

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rawDegreeHomologyBounded_vertexOpenStar (K : Complex ι) :
    RawDegreeHomologyBounded K.space (Fintype.card ι) := by
  have hGood (t : Finset ι) (hne : t.Nonempty) :
      IsEmpty (finiteCoverIntersection K.vertexOpenStar t) ∨
        ContractibleSpace (finiteCoverIntersection K.vertexOpenStar t) := by
    change IsEmpty (⋂ i ∈ t, K.vertexOpenStar i) ∨ ContractibleSpace (⋂ i ∈ t, K.vertexOpenStar i)
    rw [← K.vertexStarIntersection_eq_iInter t]
    by_cases ht : (K.vertexStarIntersection t).Nonempty
    · exact Or.inr (K.vertexStarIntersection_contractibleSpace t hne ht)
    · exact Or.inl ⟨fun x => ht ⟨x.val, x.property⟩⟩
  have hBound := rawDegreeHomologyBounded_finite_good_cover_of_union_estimates
    rawDegreeHomology_finiteDimensional_union rawDegreeHomology_subsingleton_union
    K.vertexOpenStar Finset.univ (fun i _ => K.isOpen_vertexOpenStar i)
      (fun t _ hne => hGood t hne)
  have hCover : finiteCoverUnion K.vertexOpenStar Finset.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := K.exists_mem_vertexOpenStar x
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let e : finiteCoverUnion K.vertexOpenStar Finset.univ ≃ₜ K.space :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hCover.symm ▸ Set.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  simpa only [Finset.card_univ] using rawDegreeHomologyBounded_homeomorph e.symm hBound

end BanachIsometric.FiniteNerve.Complex
