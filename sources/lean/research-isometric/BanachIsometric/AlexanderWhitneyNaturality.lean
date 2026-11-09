import BanachIsometric.AlexanderWhitneyChainMap

/-! Strict naturality of the actual rational Alexander--Whitney map for
actual continuous maps of the two spaces. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct DirectSum Topology

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

def awProductMap (f : C(X, X')) (g : C(Y, Y')) : C(X × Y, X' × Y') :=
  ⟨fun z => (f z.1, g z.2),
    (f.continuous.comp continuous_fst).prodMk (g.continuous.comp continuous_snd)⟩

def rawBigradedTensorMap (f : C(X, X')) (g : C(Y, Y')) :
    RawBigradedTensorChains X Y →ₗ[ℚ] RawBigradedTensorChains X' Y' :=
  DirectSum.toModule ℚ (ℕ × ℕ) (RawBigradedTensorChains X' Y') (fun ij =>
    (rawTensorInclusion X' Y' ij.1 ij.2).comp
      (TensorProduct.map (rawChainMap f ij.1) (rawChainMap g ij.2)))

@[simp] theorem rawBigradedTensorMap_inclusion (f : C(X, X')) (g : C(Y, Y'))
    (p q : ℕ) (c : RawTensorChains X Y p q) :
    rawBigradedTensorMap f g (rawTensorInclusion X Y p q c) =
      rawTensorInclusion X' Y' p q (TensorProduct.map (rawChainMap f p) (rawChainMap g q) c) := by
  simp only [rawBigradedTensorMap, rawTensorInclusion, DirectSum.toModule_lof, LinearMap.comp_apply]

theorem awPureTerm_naturality (f : C(X, X')) (g : C(Y, Y'))
    {n p q : ℕ} (h : p + q = n) (σ : RawSingularSimplex (X × Y) n) :
    TensorProduct.map (rawChainMap f p) (rawChainMap g q) (awPureTerm σ p q h) =
      awPureTerm ((awProductMap f g).comp σ) p q h := by
  simp only [awPureTerm, TensorProduct.map_tmul, rawChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rfl

theorem rawAlexanderWhitney_naturality (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawBigradedTensorMap f g).comp (rawAlexanderWhitney (X := X) (Y := Y) n) =
      (rawAlexanderWhitney (X := X') (Y := Y') n).comp (rawChainMap (awProductMap f g) n) := by
  apply Finsupp.lhom_ext
  intro σ a
  change rawBigradedTensorMap f g (rawAlexanderWhitney n (Finsupp.single σ a)) =
    rawAlexanderWhitney n (rawChainMap (awProductMap f g) n (Finsupp.single σ a))
  have hsingle : rawChainMap (awProductMap f g) n (Finsupp.single σ a) =
      Finsupp.single ((awProductMap f g).comp σ) a := by simp [rawChainMap]
  rw [hsingle, rawAlexanderWhitney_single, rawAlexanderWhitney_single, map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [map_smul, rawBigradedTensorMap_inclusion, awPureTerm_naturality]

end BanachIsometric.SingularAW
