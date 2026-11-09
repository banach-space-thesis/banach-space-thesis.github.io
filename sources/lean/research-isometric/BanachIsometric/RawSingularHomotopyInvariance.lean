import BanachIsometric.RawSingularHomology
import BanachIsometric.RawSingularPrismChain

/-! Actual homotopy invariance of the concrete rational singular homology
quotient modules, derived from the proved actual prism-chain identity. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f₀ f₁ : C(X, Y)}

theorem rawHomologyMap_homotopy (H : f₀.Homotopy f₁) (n : ℕ) :
    rawHomologyMap f₀ n = rawHomologyMap f₁ n := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk (rawCyclesMap f₀ n c) =
      Submodule.Quotient.mk (rawCyclesMap f₁ n c)
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-rawPrism H (n + 1) c.val, ?_⟩
    apply Subtype.ext
    change rawBoundary (n + 1) (-rawPrism H (n + 1) c.val) =
      rawChainMap f₀ (n + 1) c.val - rawChainMap f₁ (n + 1) c.val
    rw [map_neg]
    have hc : rawBoundary n c.val = 0 := c.property
    have hp : rawBoundary (n + 1) (rawPrism H (n + 1) c.val) =
        rawChainMap f₁ (n + 1) c.val - rawChainMap f₀ (n + 1) c.val := by
      have h := LinearMap.congr_fun (rawPrism_chain_identity H n) c.val
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        hc, map_zero, add_zero] using h
    rw [hp]
    abel

theorem rawHomology_retract_identity (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (n : ℕ) :
    (rawHomologyMap g n).comp (rawHomologyMap f n) = LinearMap.id := by
  rw [← rawHomologyMap_comp, rawHomologyMap_homotopy H, rawHomologyMap_id]

theorem rawHomology_injective_of_domination (f : C(X, Y)) (g : C(Y, X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (n : ℕ) :
    Function.Injective (rawHomologyMap f n) := by
  apply Function.LeftInverse.injective (g := rawHomologyMap g n)
  intro x
  exact LinearMap.congr_fun (rawHomology_retract_identity f g H n) x

end BanachIsometric.SingularPrism
