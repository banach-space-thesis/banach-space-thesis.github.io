import BanachIsometric.VectorChainKernel

/-! The chosen degree decompositions commute with the actual differentials.
This gives a genuine chain isomorphism to homology with zero differential
plus the proved contractible kernel complex. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting
open CategoryTheory

variable {K : Type*} [Field K] (C : ℕ → ModuleCat.{u} K)
  (d : ∀ n, C (n + 1) →ₗ[K] C n)
  (hd : ∀ n, (d n).comp (d (n + 1)) = 0)

def splitDifferential (n : ℕ) :
    (Homology C d hd (n + 1) × homologyKernel C d hd (n + 1)) →ₗ[K]
      (Homology C d hd n × homologyKernel C d hd n) :=
  (0 : (Homology C d hd (n + 1) × homologyKernel C d hd (n + 1)) →ₗ[K]
    Homology C d hd n).prod ((kernelDifferential C d hd n).comp
      (LinearMap.snd K (Homology C d hd (n + 1)) (homologyKernel C d hd (n + 1))))

theorem splitDifferential_squared (n : ℕ) :
    (splitDifferential C d hd n).comp (splitDifferential C d hd (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun (kernelDifferential_squared C d hd n) x.2

abbrev splitChainComplex : ChainComplex (ModuleCat.{u} K) ℕ :=
  chainComplex (fun n => ModuleCat.of K (Homology C d hd n × homologyKernel C d hd n))
    (splitDifferential C d hd) (splitDifferential_squared C d hd)

theorem degreeSplit_differential (n : ℕ) (x : C (n + 1)) :
    degreeSplit C d hd n (d n x) =
      splitDifferential C d hd n (degreeSplit C d hd (n + 1) x) := by
  apply Prod.ext
  · exact homologyProjection_boundary C d hd n x
  · apply Subtype.ext
    change d n x - homologyInclusion C d hd n (homologyProjection C d hd n (d n x)) =
      d n (x - homologyInclusion C d hd (n + 1) (homologyProjection C d hd (n + 1) x))
    rw [homologyProjection_boundary, map_zero, sub_zero, map_sub,
      differential_homologyInclusion, sub_zero]

def chainSplitIso : chainComplex C d hd ≅ splitChainComplex C d hd :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (degreeSplit C d hd n).toModuleIso) (by
    intro i j hij
    have hi : j + 1 = i := hij
    subst i
    rw [chainComplex_d, chainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro x
    exact (degreeSplit_differential C d hd j x).symm)

end BanachIsometric.VectorChainSplitting
