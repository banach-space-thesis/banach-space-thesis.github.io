import BanachIsometric.RawSingularChainComplex
import BanachIsometric.RawZeroSingularHomology
import BanachIsometric.DegreeOneChainHomotopy

/-! The actual prism maps form a categorical chain homotopy. This connects
the explicit geometric construction to Mathlib's homological-complex API. -/

noncomputable section
universe u
namespace BanachIsometric.SingularPrism

open CategoryTheory

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

def rawCategoricalPrism (H : f₀.Homotopy f₁) :
    Homotopy (rawRationalChainMap f₁) (rawRationalChainMap f₀) :=
  chainHomotopyOfDegreeOne (fun n => ModuleCat.ofHom (rawPrism H n)) (by
    rw [rawRationalChainMap_f, rawRationalChainMap_f, rawRationalChainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro c
    have hp := LinearMap.congr_fun (rawPrism_zero_identity H) c
    change rawBoundary 0 (rawPrism H 0 c) = rawChainMap f₁ 0 c - rawChainMap f₀ 0 c at hp
    exact sub_eq_iff_eq_add.mp hp.symm) (by
    intro n
    rw [rawRationalChainMap_f, rawRationalChainMap_f, rawRationalChainComplex_d,
      rawRationalChainComplex_d]
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro c
    have hp := LinearMap.congr_fun (rawPrism_chain_identity H n) c
    change rawBoundary (n + 1) (rawPrism H (n + 1) c) +
      rawPrism H n (rawBoundary n c) =
        rawChainMap f₁ (n + 1) c - rawChainMap f₀ (n + 1) c at hp
    change rawChainMap f₁ (n + 1) c = rawPrism H n (rawBoundary n c) +
      rawBoundary (n + 1) (rawPrism H (n + 1) c) + rawChainMap f₀ (n + 1) c
    calc
      _ = rawBoundary (n + 1) (rawPrism H (n + 1) c) +
          rawPrism H n (rawBoundary n c) + rawChainMap f₀ (n + 1) c :=
        sub_eq_iff_eq_add.mp hp.symm
      _ = _ := by abel)

end BanachIsometric.SingularPrism
