import BanachIsometric.FiniteNerveRawHomologyMap
import BanachIsometric.RawTensorComponents
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual finite-face tensor chains embed in the actual raw singular tensor
chains. Injectivity is proved by actual linear left inverses of the factor
maps over ℚ. These inverses are only linear: no chain inverse or homology
injectivity is asserted. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open SingularAW
open scoped TensorProduct DirectSum

variable {ι : Type} [LinearOrder ι] [Fintype ι]

abbrev FiniteTensorChains (K : Complex ι) (p q : ℕ) :=
  FiniteRationalChains K p ⊗[ℚ] FiniteRationalChains K q

abbrev FiniteBigradedTensorChains (K : Complex ι) :=
  ⨁ ij : ℕ × ℕ, FiniteTensorChains K ij.1 ij.2

def finiteTensorInclusion (K : Complex ι) (p q : ℕ) :
    FiniteTensorChains K p q →ₗ[ℚ] FiniteBigradedTensorChains K :=
  DirectSum.lof ℚ (ℕ × ℕ) (fun ij => FiniteTensorChains K ij.1 ij.2) (p, q)

def finiteTensorToRaw (K : Complex ι) :
    FiniteBigradedTensorChains K →ₗ[ℚ] RawBigradedTensorChains K.space K.space :=
  DirectSum.lmap (fun ij : ℕ × ℕ =>
    TensorProduct.map (finiteToRawSingularChain K ij.1) (finiteToRawSingularChain K ij.2))

@[simp] theorem finiteTensorToRaw_inclusion (K : Complex ι) (p q : ℕ)
    (c : FiniteTensorChains K p q) :
    finiteTensorToRaw K (finiteTensorInclusion K p q c) =
      rawTensorInclusion K.space K.space p q
        (TensorProduct.map (finiteToRawSingularChain K p) (finiteToRawSingularChain K q) c) := by
  simp only [finiteTensorToRaw, finiteTensorInclusion, rawTensorInclusion, DirectSum.lmap_lof]

theorem finiteTensorToRaw_factor_injective (K : Complex ι) (p q : ℕ) :
    Function.Injective
      (TensorProduct.map (finiteToRawSingularChain K p) (finiteToRawSingularChain K q)) := by
  obtain ⟨r, hr⟩ := (finiteToRawSingularChain K p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (finiteToRawSingularChain_injective K p))
  obtain ⟨s, hs⟩ := (finiteToRawSingularChain K q).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (finiteToRawSingularChain_injective K q))
  intro a b hab
  have hh := congrArg (TensorProduct.map r s) hab
  simpa only [TensorProduct.map_map, hr, hs, TensorProduct.map_id, LinearMap.id_apply] using hh

theorem finiteTensorToRaw_injective (K : Complex ι) : Function.Injective (finiteTensorToRaw K) := by
  intro x y he
  apply DirectSum.ext_component ℚ
  rintro ⟨p, q⟩
  apply finiteTensorToRaw_factor_injective K p q
  exact congrArg (fun z : RawBigradedTensorChains K.space K.space => z (p, q)) he

end BanachIsometric.FiniteNerve
