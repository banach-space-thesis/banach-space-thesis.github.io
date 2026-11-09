import BanachIsometric.FiniteNerveRationalQuotientHomology

/-! Actual face-subcomplex inclusions on the same ordered vertex set.
The literal tuple inclusions induce injective chain maps commuting with the
actual alternating boundary. Degreewise injectivity does NOT assert
injectivity on homology. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type} [LinearOrder ι] [Fintype ι]
  {K L : Complex ι}

def orderedComplexInclusion (h : K.faces ⊆ L.faces) (n : ℕ) :
    OrderedSimplex K n → OrderedSimplex L n := fun v => ⟨v.val, h v.property⟩

def strictComplexInclusion (h : K.faces ⊆ L.faces) (n : ℕ) :
    StrictOrderedSimplex K n → StrictOrderedSimplex L n :=
  fun v => ⟨orderedComplexInclusion h n v.val, v.property⟩

@[simp] theorem strictComplexInclusion_apply (h : K.faces ⊆ L.faces) (n : ℕ)
    (v : StrictOrderedSimplex K n) (j : Fin (n + 1)) :
    (strictComplexInclusion h n v).val.val j = v.val.val j := rfl

theorem strictComplexInclusion_injective (h : K.faces ⊆ L.faces) (n : ℕ) :
    Function.Injective (strictComplexInclusion h n) := by
  intro v w he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : StrictOrderedSimplex L n => z.val.val) he

@[simp] theorem strictComplexInclusion_face (h : K.faces ⊆ L.faces) (n : ℕ)
    (i : Fin (n + 2)) (v : StrictOrderedSimplex K (n + 1)) :
    strictComplexInclusion h n (strictOrderedFace K i v) =
      strictOrderedFace L i (strictComplexInclusion h (n + 1) v) := rfl

def finiteComplexChainInclusion (h : K.faces ⊆ L.faces) (n : ℕ) :
    FiniteRationalChains K n →ₗ[ℚ] FiniteRationalChains L n :=
  Finsupp.lmapDomain ℚ ℚ (strictComplexInclusion h n)

@[simp] theorem finiteComplexChainInclusion_single (h : K.faces ⊆ L.faces) (n : ℕ)
    (v : StrictOrderedSimplex K n) (a : ℚ) :
    finiteComplexChainInclusion h n (Finsupp.single v a) =
      Finsupp.single (strictComplexInclusion h n v) a := by
  simp [finiteComplexChainInclusion]

theorem finiteComplexChainInclusion_injective (h : K.faces ⊆ L.faces) (n : ℕ) :
    Function.Injective (finiteComplexChainInclusion h n) :=
  Finsupp.mapDomain_injective (strictComplexInclusion_injective h n)

theorem finiteComplexChainInclusion_boundary (h : K.faces ⊆ L.faces) (n : ℕ) :
    (finiteRationalBoundary L n).comp (finiteComplexChainInclusion h (n + 1)) =
      (finiteComplexChainInclusion h n).comp (finiteRationalBoundary K n) := by
  apply Finsupp.lhom_ext
  intro v a
  have ha : Finsupp.single v a = a • Finsupp.single v 1 := by simp
  rw [ha]
  simp only [map_smul]
  congr 1
  simp only [LinearMap.comp_apply, finiteComplexChainInclusion_single,
    finiteRationalBoundary_single, map_sum, map_zsmul, strictComplexInclusion_face]

end BanachIsometric.FiniteNerve
