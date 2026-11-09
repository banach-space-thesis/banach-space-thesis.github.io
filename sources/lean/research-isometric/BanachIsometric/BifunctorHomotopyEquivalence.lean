import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! An additive total bifunctor preserves genuine chain homotopy equivalences
in its first argument. This uses the actual total-complex homotopy constructor. -/

noncomputable section
namespace BanachIsometric
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*}
  [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

theorem mapBifunctor_first_map_comp
    {A B E : HomologicalComplex C₁ c₁} (Q : HomologicalComplex C₂ c₂)
    [HasMapBifunctor A Q F c] [HasMapBifunctor B Q F c] [HasMapBifunctor E Q F c]
    (f : A ⟶ B) (g : B ⟶ E) :
    mapBifunctorMap (f ≫ g) (𝟙 Q) F c =
      mapBifunctorMap f (𝟙 Q) F c ≫ mapBifunctorMap g (𝟙 Q) F c := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.assoc,
    ι_mapBifunctorMap, ι_mapBifunctorMap_assoc, Functor.map_comp, NatTrans.comp_app]
  rw [(F.obj (E.X i₁)).map_id (Q.X i₂), (F.obj (B.X i₁)).map_id (Q.X i₂)]
  simp only [Category.id_comp]

theorem mapBifunctor_first_map_id
    (A : HomologicalComplex C₁ c₁) (Q : HomologicalComplex C₂ c₂)
    [HasMapBifunctor A Q F c] :
    mapBifunctorMap (𝟙 A) (𝟙 Q) F c = 𝟙 (mapBifunctor A Q F c) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [HomologicalComplex.id_f, ι_mapBifunctorMap, Category.comp_id]
  rw [F.map_id (A.X i₁), (F.obj (A.X i₁)).map_id (Q.X i₂)]
  simp only [NatTrans.id_app, Category.id_comp]

def mapBifunctorHomotopyEquivFirst
    {A B : HomologicalComplex C₁ c₁} (e : HomotopyEquiv A B)
    (Q : HomologicalComplex C₂ c₂)
    [HasMapBifunctor A Q F c] [HasMapBifunctor B Q F c] :
    HomotopyEquiv (mapBifunctor A Q F c) (mapBifunctor B Q F c) where
  hom := mapBifunctorMap e.hom (𝟙 Q) F c
  inv := mapBifunctorMap e.inv (𝟙 Q) F c
  homotopyHomInvId := by
    simpa only [mapBifunctor_first_map_comp, mapBifunctor_first_map_id] using
      mapBifunctorMapHomotopy₁ e.homotopyHomInvId (𝟙 Q) F c
  homotopyInvHomId := by
    simpa only [mapBifunctor_first_map_comp, mapBifunctor_first_map_id] using
      mapBifunctorMapHomotopy₁ e.homotopyInvHomId (𝟙 Q) F c

end BanachIsometric
