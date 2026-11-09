import BanachIsometric.RawSingularPrismChain
import BanachIsometric.RawSingularHomology

/-! Degree-zero rational singular homology and its actual prism proof of
homotopy invariance. There is no negative chain-index convention. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f₀ f₁ : C(X, Y)}

theorem rawPrism_zero_single (H : f₀.Homotopy f₁) (simplex : RawSingularSimplex X 0) :
    rawBoundary 0 (rawPrism H 0 (Finsupp.single simplex 1)) =
      Finsupp.single (f₁.comp simplex) 1 - Finsupp.single (f₀.comp simplex) 1 := by
  have hP : rawPrism H 0 (Finsupp.single simplex 1) =
      Finsupp.single (homotopyPrism H (0 : Fin 1) simplex) 1 := by
    rw [rawPrism_single_one]
    change (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) •
      Finsupp.single (homotopyPrism H i simplex) 1) = _
    simp
  rw [hP, rawBoundary_single]
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
    Finsupp.single ((homotopyPrism H (0 : Fin 1) simplex).comp (face i)) 1) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
  rw [homotopyPrism_face_top H 0 simplex]
  have hb := homotopyPrism_face_bottom H 0 simplex
  change (homotopyPrism H (0 : Fin 1) simplex).comp (face (1 : Fin 2)) = f₀.comp simplex at hb
  rw [hb]
  rw [sub_eq_add_neg]

theorem rawPrism_zero_identity (H : f₀.Homotopy f₁) :
    (rawBoundary 0).comp (rawPrism H 0) = rawChainMap f₁ 0 - rawChainMap f₀ 0 := by
  apply Finsupp.lhom_ext
  intro simplex a
  have hsingle : Finsupp.single simplex a = a • Finsupp.single simplex 1 := by simp
  rw [hsingle]
  simp only [map_smul]
  congr 1
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply,
    rawChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
      rawPrism_zero_single H simplex

def RawZeroHomology (X : Type*) [TopologicalSpace X] : Type _ :=
  (RawRationalChains X 0) ⧸ LinearMap.range (rawBoundary (X := X) 0)

instance (X : Type*) [TopologicalSpace X] : AddCommGroup (RawZeroHomology X) :=
  inferInstanceAs (AddCommGroup ((RawRationalChains X 0) ⧸ LinearMap.range (rawBoundary (X := X) 0)))

instance (X : Type*) [TopologicalSpace X] : Module ℚ (RawZeroHomology X) :=
  inferInstanceAs (Module ℚ ((RawRationalChains X 0) ⧸ LinearMap.range (rawBoundary (X := X) 0)))

def rawZeroHomologyMap (f : C(X, Y)) : RawZeroHomology X →ₗ[ℚ] RawZeroHomology Y :=
  (LinearMap.range (rawBoundary (X := X) 0)).mapQ
    (LinearMap.range (rawBoundary (X := Y) 0)) (rawChainMap f 0) (by
      rintro _ ⟨c, rfl⟩
      exact ⟨rawChainMap f 1 c, LinearMap.congr_fun (rawChainMap_boundary f 0) c⟩)

theorem rawZeroHomologyMap_homotopy (H : f₀.Homotopy f₁) :
    rawZeroHomologyMap f₀ = rawZeroHomologyMap f₁ := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawChainMap f₀ 0 c) = Submodule.Quotient.mk (rawChainMap f₁ 0 c)
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-rawPrism H 0 c, ?_⟩
    rw [map_neg]
    have hp := LinearMap.congr_fun (rawPrism_zero_identity H) c
    change rawBoundary 0 (rawPrism H 0 c) = rawChainMap f₁ 0 c - rawChainMap f₀ 0 c at hp
    rw [hp]
    abel

theorem rawZeroHomologyMap_id : rawZeroHomologyMap (ContinuousMap.id X) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawChainMap (ContinuousMap.id X) 0 c) = Submodule.Quotient.mk c
    rw [rawChainMap_id]
    rfl

theorem rawZeroHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    rawZeroHomologyMap (g.comp f) = (rawZeroHomologyMap g).comp (rawZeroHomologyMap f) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawChainMap (g.comp f) 0 c) =
      Submodule.Quotient.mk (rawChainMap g 0 (rawChainMap f 0 c))
    rw [rawChainMap_comp]
    rfl

end BanachIsometric.SingularPrism
