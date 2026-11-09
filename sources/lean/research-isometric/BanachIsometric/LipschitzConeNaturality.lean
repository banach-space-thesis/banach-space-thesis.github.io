import BanachIsometric.LipschitzSingularCone

/-! Coning commutes with actual continuous linear maps, in particular with
evaluation of a section operator and with positive scalar multiplication. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology NNReal

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

def continuousLinearSingularMap (f : V →L[ℝ] W) : C(V, W) := ⟨f, f.continuous⟩

theorem lipschitzSingularCone_comp_linear (n : ℕ) (f : V →L[ℝ] W) (σ : RawSingularSimplex V n)
    (hσ : ∃ L : ℝ≥0, LipschitzWith L σ) :
    lipschitzSingularCone n ((continuousLinearSingularMap f).comp σ) =
      (continuousLinearSingularMap f).comp (lipschitzSingularCone n σ) := by
  obtain ⟨L, hL⟩ := hσ
  apply ContinuousMap.ext
  intro x
  change lipschitzSingularCone n ((continuousLinearSingularMap f).comp σ) x =
    f (lipschitzSingularCone n σ x)
  rw [lipschitzSingularCone_apply n _ ⟨_, f.lipschitz.comp hL⟩, lipschitzSingularCone_apply n σ ⟨L, hL⟩]
  unfold singularConeFun
  split_ifs <;> simp [continuousLinearSingularMap]

theorem rawLipschitzCone_rawChainMap_linear (n : ℕ) (f : V →L[ℝ] W)
    (c : RawRationalChains V n) (hc : c ∈ rawLipschitzCarrier V n) :
    rawLipschitzCone n (rawChainMap (continuousLinearSingularMap f) n c) =
      rawChainMap (continuousLinearSingularMap f) (n + 1) (rawLipschitzCone n c) := by
  let A := (rawLipschitzCone n).comp (rawChainMap (continuousLinearSingularMap f) n)
  let B := (rawChainMap (continuousLinearSingularMap f) (n + 1)).comp (rawLipschitzCone n)
  have hsub : rawLipschitzCarrier V n ≤ LinearMap.ker (A - B) := by
    rw [rawLipschitzCarrier, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change (A - B) (Finsupp.single σ 1) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    simp [A, B, rawChainMap, lipschitzSingularCone_comp_linear n f σ hσ]
  have hz := hsub hc
  change (A - B) c = 0 at hz
  exact sub_eq_zero.mp hz

end BanachIsometric.SingularPrism
