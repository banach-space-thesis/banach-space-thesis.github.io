import BanachIsometric.LipschitzSubdivision
import BanachIsometric.SubdivisionCycleFilling

/-! Powers of subdivision and the corresponding cycle fillings preserve
Lipschitz support. -/

noncomputable section
namespace BanachIsometric.SingularPrism

variable {X : Type*} [PseudoMetricSpace X]

theorem rawSubdivision_power_preserves_lipschitz (n k : ℕ) :
    rawLipschitzCarrier X n ≤ (rawLipschitzCarrier X n).comap (rawSubdivision X n ^ k) := by
  induction k with
  | zero => exact fun _ hc => hc
  | succ k ih =>
    intro c hc
    have h := rawSubdivision_preserves_lipschitz n (ih hc)
    simpa only [pow_succ', Module.End.mul_apply] using h

theorem rawSubdivisionCycleFilling_mem_lipschitz (n k : ℕ)
    (c : RawRationalChains X (n + 1)) (hc : c ∈ rawLipschitzCarrier X (n + 1)) :
    rawSubdivisionCycleFilling X n k c ∈ rawLipschitzCarrier X (n + 2) := by
  induction k with
  | zero => exact (rawLipschitzCarrier X (n + 2)).zero_mem
  | succ k ih =>
    change rawSubdivisionCycleFilling X n k c +
      (rawSubdivision X (n + 2) ^ k) (rawSubdivisionHomotopy X (n + 1) c) ∈ rawLipschitzCarrier X (n + 2)
    exact (rawLipschitzCarrier X (n + 2)).add_mem ih
      (rawSubdivision_power_preserves_lipschitz (n + 2) k (rawSubdivisionHomotopy_preserves_lipschitz (n + 1) hc))

end BanachIsometric.SingularPrism
