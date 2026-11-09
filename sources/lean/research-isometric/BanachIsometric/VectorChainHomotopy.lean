import BanachIsometric.VectorChainContraction
import BanachIsometric.DegreeOneChainHomotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Every nonnegative chain complex of vector spaces is genuinely chain
homotopy equivalent to its actual cycles/boundaries homology with zero
differential. The maps and homotopy are the constructed linear sections. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting
open CategoryTheory CategoryTheory.Limits

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

def chainComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of C (fun n => ModuleCat.ofHom (d n))
    (fun n => ModuleCat.hom_ext_iff.mpr (hd n))

theorem chainComplex_d (n : ℕ) :
    (chainComplex C d hd).d (n + 1) n = ModuleCat.ofHom (d n) :=
  ChainComplex.of_d _ _ _ n

def homologyComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of K (Homology C d hd n))
    (fun _ => 0) (fun _ => by simp)

theorem homologyComplex_d (n : ℕ) :
    (homologyComplex C d hd).d (n + 1) n = 0 :=
  ChainComplex.of_d _ _ _ n

def projectionChainMap : chainComplex C d hd ⟶ homologyComplex C d hd where
  f n := ModuleCat.ofHom (homologyProjection C d hd n)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    rw [chainComplex_d, homologyComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro x
    change 0 = homologyProjection C d hd j (d j x)
    exact (homologyProjection_boundary C d hd j x).symm

def inclusionChainMap : homologyComplex C d hd ⟶ chainComplex C d hd where
  f n := ModuleCat.ofHom (homologyInclusion C d hd n)
  comm' i j hij := by
    have hi : j + 1 = i := hij
    subst i
    rw [chainComplex_d, homologyComplex_d, zero_comp]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro a
    change d j (homologyInclusion C d hd (j + 1) a) = 0
    exact differential_homologyInclusion C d hd j a

theorem inclusion_projection_identity :
    inclusionChainMap C d hd ≫ projectionChainMap C d hd = 𝟙 (homologyComplex C d hd) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext_iff.mpr
  apply LinearMap.ext
  intro a
  exact homologyProjection_inclusion C d hd n a

def identity_projection_inclusion_homotopy :
    Homotopy (𝟙 (chainComplex C d hd)) (projectionChainMap C d hd ≫ inclusionChainMap C d hd) :=
  chainHomotopyOfDegreeOne (fun n => ModuleCat.ofHom (contraction C d hd n)) (by
    rw [chainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro x
    change x = d 0 (contraction C d hd 0 x) +
      homologyInclusion C d hd 0 (homologyProjection C d hd 0 x)
    exact sub_eq_iff_eq_add.mp (contraction_zero_identity C d hd x).symm) (by
      intro n
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext_iff.mpr
      apply LinearMap.ext
      intro x
      change x = contraction C d hd n (d n x) +
        d (n + 1) (contraction C d hd (n + 1) x) +
        homologyInclusion C d hd (n + 1) (homologyProjection C d hd (n + 1) x)
      calc
        x = d (n + 1) (contraction C d hd (n + 1) x) +
            contraction C d hd n (d n x) +
            homologyInclusion C d hd (n + 1) (homologyProjection C d hd (n + 1) x) :=
          sub_eq_iff_eq_add.mp (contraction_succ_identity C d hd n x).symm
        _ = _ := by abel)

def homotopyEquivHomology :
    HomotopyEquiv (chainComplex C d hd) (homologyComplex C d hd) where
  hom := projectionChainMap C d hd
  inv := inclusionChainMap C d hd
  homotopyHomInvId := (identity_projection_inclusion_homotopy C d hd).symm
  homotopyInvHomId := Homotopy.ofEq (inclusion_projection_identity C d hd)

end BanachIsometric.VectorChainSplitting
