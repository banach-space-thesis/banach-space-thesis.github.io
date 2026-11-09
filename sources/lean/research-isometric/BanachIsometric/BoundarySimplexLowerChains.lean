import BanachIsometric.FullSimplexComplex

/-! Below its unique full-dimensional simplex, every strict ordered simplex
of the full simplex already belongs to its boundary. These are actual inverse
maps on the finite face bases and actual chain-space linear equivalences. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve

def fullSimplexLowerFace (n q : ℕ) (hq : q + 1 < n + 3)
    (v : StrictOrderedSimplex (fullSimplexComplex n) q) :
    StrictOrderedSimplex (boundarySimplexComplex n) q := by
  refine ⟨⟨v.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp v.val.property).2, ?_⟩⟩, v.property⟩
  intro him
  have hc := Finset.card_image_of_injective (s := Finset.univ) v.property.injective
  rw [him] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

@[simp] theorem fullSimplexLowerFace_apply (n q : ℕ) (hq : q + 1 < n + 3)
    (v : StrictOrderedSimplex (fullSimplexComplex n) q) (i : Fin (q + 1)) :
    (fullSimplexLowerFace n q hq v).val.val i = v.val.val i := rfl

@[simp] theorem fullSimplexLowerFace_inclusion (n q : ℕ) (hq : q + 1 < n + 3)
    (v : StrictOrderedSimplex (boundarySimplexComplex n) q) :
    fullSimplexLowerFace n q hq
      (strictComplexInclusion (boundarySimplex_faces_subset_full n) q v) = v := rfl

@[simp] theorem fullSimplexLowerFace_included (n q : ℕ) (hq : q + 1 < n + 3)
    (v : StrictOrderedSimplex (fullSimplexComplex n) q) :
    strictComplexInclusion (boundarySimplex_faces_subset_full n) q
      (fullSimplexLowerFace n q hq v) = v := rfl

def boundarySimplexLowerFaceEquiv (n q : ℕ) (hq : q + 1 < n + 3) :
    StrictOrderedSimplex (boundarySimplexComplex n) q ≃
      StrictOrderedSimplex (fullSimplexComplex n) q where
  toFun := strictComplexInclusion (boundarySimplex_faces_subset_full n) q
  invFun := fullSimplexLowerFace n q hq
  left_inv := fullSimplexLowerFace_inclusion n q hq
  right_inv := fullSimplexLowerFace_included n q hq

def boundarySimplexLowerChainEquiv (n q : ℕ) (hq : q + 1 < n + 3) :
    FiniteRationalChains (boundarySimplexComplex n) q ≃ₗ[ℚ]
      FiniteRationalChains (fullSimplexComplex n) q :=
  Finsupp.domLCongr (boundarySimplexLowerFaceEquiv n q hq)

theorem boundarySimplexLowerChainEquiv_eq_inclusion (n q : ℕ) (hq : q + 1 < n + 3) :
    (boundarySimplexLowerChainEquiv n q hq).toLinearMap =
      finiteComplexChainInclusion (boundarySimplex_faces_subset_full n) q := by
  apply Finsupp.lhom_ext
  intro v a
  simp [boundarySimplexLowerChainEquiv, boundarySimplexLowerFaceEquiv,
    finiteComplexChainInclusion]

end BanachIsometric.SingularPrism
