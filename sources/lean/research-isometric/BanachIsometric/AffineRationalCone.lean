import BanachIsometric.AffineSingularSimplex

/-! Free rational affine simplex chains and their explicit cone operator.
The boundary/cone identity is proved by literal face deletion, before
realizing these chains as actual singular chains. -/

noncomputable section
namespace BanachIsometric.SingularPrism

abbrev AffineRationalChains (E : Type*) (n : ℕ) := (Fin (n + 1) → E) →₀ ℚ

def affineFace {E : Type*} {n : ℕ} (i : Fin (n + 2)) :
    AffineRationalChains E (n + 1) →ₗ[ℚ] AffineRationalChains E n :=
  Finsupp.lmapDomain ℚ ℚ (fun v => v ∘ i.succAbove)

def affineBoundary {E : Type*} (n : ℕ) :
    AffineRationalChains E (n + 1) →ₗ[ℚ] AffineRationalChains E n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • affineFace i

theorem affineBoundary_single {E : Type*} (n : ℕ) (v : Fin (n + 2) → E) (a : ℚ) :
    affineBoundary n (Finsupp.single v a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • Finsupp.single (v ∘ i.succAbove) a := by
  simp only [affineBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
    affineFace, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

def affineCone {E : Type*} (b : E) (n : ℕ) :
    AffineRationalChains E n →ₗ[ℚ] AffineRationalChains E (n + 1) :=
  Finsupp.lmapDomain ℚ ℚ (fun v : Fin (n + 1) → E => Fin.cons b v)

theorem affineCone_single {E : Type*} (b : E) (n : ℕ) (v : Fin (n + 1) → E) (a : ℚ) :
    affineCone b n (Finsupp.single v a) = Finsupp.single (Fin.cons b v) a := by
  simp only [affineCone, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem affineCons_face_zero {E : Type*} {n : ℕ} (b : E) (v : Fin (n + 1) → E) :
    (Fin.cons b v) ∘ (0 : Fin (n + 2)).succAbove = v := by
  funext j
  simp

theorem affineCons_face_succ {E : Type*} {n : ℕ} (b : E)
    (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (Fin.cons b v) ∘ i.succ.succAbove = Fin.cons b (v ∘ i.succAbove) := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp

theorem affineBoundary_cone_single {E : Type*} (b : E) (n : ℕ)
    (v : Fin (n + 2) → E) (a : ℚ) :
    affineBoundary (n + 1) (affineCone b (n + 1) (Finsupp.single v a)) =
      Finsupp.single v a - affineCone b n (affineBoundary n (Finsupp.single v a)) := by
  rw [affineCone_single, affineBoundary_single, Fin.sum_univ_succ, affineCons_face_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, affineCons_face_succ, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, affineBoundary_single, map_sum, map_zsmul,
    affineCone_single, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem affineBoundary_cone {E : Type*} (b : E) (n : ℕ) :
    (affineBoundary (n + 1)).comp (affineCone b (n + 1)) +
      (affineCone b n).comp (affineBoundary n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, affineBoundary_cone_single,
    sub_add_cancel, LinearMap.id_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affineChainRealization (n : ℕ) : AffineRationalChains E n →ₗ[ℚ] RawRationalChains E n :=
  Finsupp.lmapDomain ℚ ℚ affineSingularSimplex

theorem affineChainRealization_single (n : ℕ) (v : Fin (n + 1) → E) (a : ℚ) :
    affineChainRealization n (Finsupp.single v a) = Finsupp.single (affineSingularSimplex v) a := by
  simp only [affineChainRealization, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem affineChainRealization_boundary (n : ℕ) :
    (rawBoundary n).comp (affineChainRealization (E := E) (n + 1)) =
      (affineChainRealization n).comp (affineBoundary n) := by
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, affineChainRealization_single, rawBoundary_single,
    affineBoundary_single, map_sum, map_zsmul, face, affineSingularSimplex_precomp]

end BanachIsometric.SingularPrism
