import BanachIsometric.RawSmallChains
import BanachIsometric.RawSubdivisionIteration

/-! Explicit fillings of a cycle minus any iterated subdivision. If the
cycle is already small, every simplex of the filling is small as well. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable (X : Type*) [TopologicalSpace X]

theorem rawSubdivision_boundary_power (n k : ℕ) :
    (rawBoundary n).comp (rawSubdivision X (n + 1) ^ k) =
      (rawSubdivision X n ^ k).comp (rawBoundary n) :=
  (linearMap_power_intertwines (rawSubdivision X (n + 1)) (rawSubdivision X n)
    (rawBoundary n) (rawSubdivision_boundary X n).symm k).symm

def rawSubdivisionCycleFilling (n : ℕ) :
    (k : ℕ) → RawRationalChains X (n + 1) →ₗ[ℚ] RawRationalChains X (n + 2)
  | 0 => 0
  | k + 1 => rawSubdivisionCycleFilling n k +
      (rawSubdivision X (n + 2) ^ k).comp (rawSubdivisionHomotopy X (n + 1))

theorem rawSubdivisionCycleFilling_boundary (n k : ℕ) (c : RawRationalChains X (n + 1))
    (hc : rawBoundary n c = 0) :
    rawBoundary (n + 1) (rawSubdivisionCycleFilling X n k c) =
      c - (rawSubdivision X (n + 1) ^ k) c := by
  have hT : rawBoundary (n + 1) (rawSubdivisionHomotopy X (n + 1) c) =
      c - rawSubdivision X (n + 1) c := by
    have h := LinearMap.congr_fun (rawSubdivisionHomotopy_identity X n) c
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, hc, map_zero, add_zero,
      LinearMap.sub_apply, LinearMap.id_apply] using h
  induction k with
  | zero => simp [rawSubdivisionCycleFilling]
  | succ k ih =>
    change rawBoundary (n + 1) (rawSubdivisionCycleFilling X n k c +
        (rawSubdivision X (n + 2) ^ k) (rawSubdivisionHomotopy X (n + 1) c)) = _
    rw [map_add, ih]
    have hpow := LinearMap.congr_fun (rawSubdivision_boundary_power X (n + 1) k)
      (rawSubdivisionHomotopy X (n + 1) c)
    simp only [LinearMap.comp_apply] at hpow
    rw [hpow, hT, map_sub]
    simp only [pow_succ, Module.End.mul_apply]
    abel

theorem rawSubdivisionCycleFilling_preserves_small {ι : Type*} (U : ι → Set X) (n k : ℕ) :
    rawSmallChainCarrier U (n + 1) ≤
      (rawSmallChainCarrier U (n + 2)).comap (rawSubdivisionCycleFilling X n k) := by
  have hpow (j : ℕ) : rawSmallChainCarrier U (n + 2) ≤
      (rawSmallChainCarrier U (n + 2)).comap (rawSubdivision X (n + 2) ^ j) := by
    induction j with
    | zero => exact fun _ hc => hc
    | succ j ih =>
      intro c hc
      have h := rawSubdivision_preserves_small U (n + 2) (ih hc)
      simpa only [pow_succ', Module.End.mul_apply] using h
  induction k with
  | zero => exact fun _ _ => (rawSmallChainCarrier U (n + 2)).zero_mem
  | succ k ih =>
    intro c hc
    change rawSubdivisionCycleFilling X n k c +
        (rawSubdivision X (n + 2) ^ k) (rawSubdivisionHomotopy X (n + 1) c) ∈
      rawSmallChainCarrier U (n + 2)
    exact (rawSmallChainCarrier U (n + 2)).add_mem (ih hc)
      (hpow k (rawSubdivisionHomotopy_preserves_small U (n + 1) hc))

end BanachIsometric.SingularPrism
