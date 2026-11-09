import BanachIsometric.BoundarySimplexFacets
import BanachIsometric.FiniteComplexInclusion

/-! The actual full finite standard simplex, its boundary inclusion, and its
unique top-dimensional strict ordered simplex. No homological comparison or
acyclicity is assumed here. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve

def fullSimplexComplex (n : ℕ) : Complex (Fin (n + 3)) where
  faces := Finset.univ.filter Finset.Nonempty
  nonempty _ hs := (Finset.mem_filter.mp hs).2
  downward _ _ _ _ ht := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩

theorem boundarySimplex_faces_subset_full (n : ℕ) :
    (boundarySimplexComplex n).faces ⊆ (fullSimplexComplex n).faces := by
  intro s hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2.1⟩

theorem fullSimplex_closed_under_bottom (n : ℕ) :
    ∀ s ∈ (fullSimplexComplex n).faces,
      insert (⊥ : Fin (n + 3)) s ∈ (fullSimplexComplex n).faces := by
  intro s _
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.insert_nonempty _ _⟩

def fullSimplexTopSimplex (n : ℕ) : StrictOrderedSimplex (fullSimplexComplex n) (n + 2) :=
  ⟨⟨OrderHom.id, by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.image_nonempty.mpr Finset.univ_nonempty⟩⟩, strictMono_id⟩

@[simp] theorem fullSimplexTopSimplex_apply (n : ℕ) (j : Fin (n + 3)) :
    (fullSimplexTopSimplex n).val.val j = j := rfl

theorem fullSimplexTopSimplex_unique (n : ℕ)
    (v : StrictOrderedSimplex (fullSimplexComplex n) (n + 2)) :
    v = fullSimplexTopSimplex n := by
  let e : Fin (n + 3) ≃o Fin (n + 3) :=
    { toEquiv := Equiv.ofBijective v.val.val
        ⟨v.property.injective, Finite.surjective_of_injective v.property.injective⟩
      map_rel_iff' := v.property.le_iff_le }
  apply Subtype.ext
  apply Subtype.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  exact Fin.coe_orderIso_apply e j

@[simp] theorem fullSimplexTop_face (n : ℕ) (i : Fin (n + 3)) :
    strictOrderedFace (fullSimplexComplex n) i (fullSimplexTopSimplex n) =
      strictComplexInclusion (boundarySimplex_faces_subset_full n) (n + 1)
        (boundarySimplexFacet n i) := rfl

theorem fullSimplexTopChain_single (n : ℕ)
    (c : FiniteRationalChains (fullSimplexComplex n) (n + 2)) :
    c = c (fullSimplexTopSimplex n) • Finsupp.single (fullSimplexTopSimplex n) (1 : ℚ) := by
  classical
  ext v
  rw [fullSimplexTopSimplex_unique n v]
  simp

end BanachIsometric.SingularPrism
