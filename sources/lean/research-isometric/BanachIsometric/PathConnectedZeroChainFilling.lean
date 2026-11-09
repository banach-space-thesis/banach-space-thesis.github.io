import BanachIsometric.PathConnectedZeroHomology

/-! Actual rational zero-chains with augmentation zero admit actual one-chain
fillings in a path-connected space. This is derived from the proved literal
H0 quotient computation. A total choice filler is supplied for universal
acyclic-model constructions; its boundary identity is asserted precisely
on augmentation-zero chains. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawAugmentation_natural (f : C(X, Y)) :
    (rawAugmentation Y).comp (rawChainMap f 0) = rawAugmentation X := by
  apply Finsupp.lhom_ext
  intro simplex a
  simp only [LinearMap.comp_apply, rawChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, rawAugmentation_single]

theorem exists_raw_zero_chain_filling [PathConnectedSpace X] (x : X)
    (c : RawRationalChains X 0) (hc : rawAugmentation X c = 0) :
    ∃ b : RawRationalChains X 1, rawBoundary 0 b = c := by
  have hq : (Submodule.Quotient.mk c : RawZeroHomology X) = 0 := by
    apply (rawZeroHomologyPathConnectedEquiv x).injective
    change rawAugmentation X c = 0
    exact hc
  exact (Submodule.Quotient.mk_eq_zero _).mp hq

def rawZeroChainFiller [PathConnectedSpace X] (x : X) (c : RawRationalChains X 0) :
    RawRationalChains X 1 :=
  if hc : rawAugmentation X c = 0 then Classical.choose (exists_raw_zero_chain_filling x c hc)
  else 0

theorem rawBoundary_zero_chain_filler [PathConnectedSpace X] (x : X)
    (c : RawRationalChains X 0) (hc : rawAugmentation X c = 0) :
    rawBoundary 0 (rawZeroChainFiller x c) = c := by
  rw [rawZeroChainFiller, dif_pos hc]
  exact Classical.choose_spec (exists_raw_zero_chain_filling x c hc)

end BanachIsometric.SingularPrism
