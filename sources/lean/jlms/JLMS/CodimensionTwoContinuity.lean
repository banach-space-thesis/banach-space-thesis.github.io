import JLMS.CodimensionOneContinuity

/-! # Extending continuity from the common kernel of two bounded functionals -/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem continuous_of_continuous_on_two_kernels
    (f : E →ₗ[𝕜] F) (χ ψ : E →L[𝕜] 𝕜) (e r : E)
    (hχe : χ e = 1) (hχr : χ r = 0) (hψr : ψ r = 1)
    (hf : Continuous (f.comp ((LinearMap.ker χ) ⊓ LinearMap.ker ψ).subtype)) :
    Continuous f := by
  let η : E →L[𝕜] 𝕜 := ψ - ψ e • χ
  let L : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - χ.smulRight e - η.smulRight r
  have hχ (x : E) : χ (L x) = 0 := by
    change χ (x - χ x • e - η x • r) = 0
    simp [hχe, hχr]
  have hψ (x : E) : ψ (L x) = 0 := by
    change ψ (x - χ x • e - η x • r) = 0
    simp only [map_sub, map_smul, hψr, smul_eq_mul, mul_one]
    change ψ x - χ x * ψ e - (ψ x - ψ e * χ x) = 0
    ring
  let P : Submodule 𝕜 E := (LinearMap.ker χ) ⊓ LinearMap.ker ψ
  let R : E →L[𝕜] P := L.codRestrict P (fun x => ⟨hχ x, hψ x⟩)
  have hecont : Continuous (fun x : E => χ x • f e) := χ.continuous.smul continuous_const
  have hrcont : Continuous (fun x : E => η x • f r) := η.continuous.smul continuous_const
  have hc := (hf.comp R.continuous).add (hecont.add hrcont)
  convert hc using 1
  funext x
  change f x = f (x - χ x • e - η x • r) + (χ x • f e + η x • f r)
  rw [map_sub, map_sub, map_smul, map_smul]
  abel

end JLMS
