import BanachIsometric.VectorChainHomologyMap

/-! A genuine chain homotopy acts identically on the actual quotient
homology. A chain homotopy equivalence therefore induces a linear
equivalence of those quotient modules. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting

open CategoryTheory HomologicalComplex

variable {K : Type*} [Field K]
  {C D : ℕ → ModuleCat.{u} K}
  {d : ∀ n, C (n + 1) →ₗ[K] C n} {e : ∀ n, D (n + 1) →ₗ[K] D n}
  {hd : ∀ n, (d n).comp (d (n + 1)) = 0}
  {he : ∀ n, (e n).comp (e (n + 1)) = 0}
  {f g : chainComplex C d hd ⟶ chainComplex D e he}

theorem chainCyclesMap_homotopy (h : Homotopy f g) (n : ℕ) (c : cycles C d n) :
    chainCyclesMap f n c =
      boundaryMap D e he n ((h.hom n (n + 1)).hom c.val) + chainCyclesMap g n c := by
  apply Subtype.ext
  have hc := h.comm n
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)] at hc
  cases n with
  | zero =>
    rw [dNext_eq_zero _ 0 (by simp [ChainComplex.next_nat_zero, ComplexShape.down_Rel]),
      zero_add, chainComplex_d] at hc
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) c.val
  | succ n =>
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
      chainComplex_d, chainComplex_d] at hc
    have h' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) c.val
    change (show D (n + 1) from (f.f (n + 1)).hom c.val) =
      (show D (n + 1) from (h.hom n (n + 1)).hom (d n c.val)) +
        e (n + 1) ((h.hom (n + 1) (n + 2)).hom c.val) +
          (show D (n + 1) from (g.f (n + 1)).hom c.val) at h'
    rwa [show d n c.val = 0 from c.property, map_zero, zero_add] at h'

theorem chainHomologyMap_eq_of_homotopy (h : Homotopy f g) (n : ℕ) :
    chainHomologyMap f n = chainHomologyMap g n := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H c =>
    have hb : (boundaries D e he n).mkQ
        (boundaryMap D e he n ((h.hom n (n + 1)).hom c.val)) = 0 :=
      (Submodule.Quotient.mk_eq_zero (boundaries D e he n)).mpr ⟨_, rfl⟩
    simp only [chainHomologyMap_mk]
    change (boundaries D e he n).mkQ (chainCyclesMap f n c) =
      (boundaries D e he n).mkQ (chainCyclesMap g n c)
    rw [chainCyclesMap_homotopy h, map_add, hb, zero_add]

def chainHomologyEquiv (F : HomotopyEquiv (chainComplex C d hd) (chainComplex D e he)) (n : ℕ) :
    Homology C d hd n ≃ₗ[K] Homology D e he n :=
  { chainHomologyMap F.hom n with
    invFun := chainHomologyMap F.inv n
    left_inv := fun x => by
      have h := chainHomologyMap_eq_of_homotopy F.homotopyHomInvId n
      rw [chainHomologyMap_comp, chainHomologyMap_id] at h
      exact LinearMap.congr_fun h x
    right_inv := fun x => by
      have h := chainHomologyMap_eq_of_homotopy F.homotopyInvHomId n
      rw [chainHomologyMap_comp, chainHomologyMap_id] at h
      exact LinearMap.congr_fun h x }

end BanachIsometric.VectorChainSplitting
