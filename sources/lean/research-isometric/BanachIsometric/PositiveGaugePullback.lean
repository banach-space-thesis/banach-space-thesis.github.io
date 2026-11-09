import BanachIsometric.GaugeNormModel

/-! Positive real bilinear gauge data pull back along injective maps for
exactly the original scalar action; no ambient topology is needed. -/

namespace BanachIsometric.MetricGeometry

noncomputable section

variable {X V : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]

def PositiveGaugeData.comap {q : V → ℝ} (D : PositiveGaugeData q)
    (j : X →ₗ[ℝ] V) (hj : Function.Injective j) : PositiveGaugeData (fun x => q (j x)) where
  bilinear := D.bilinear.compl₁₂ j j
  symmetric x y := D.symmetric (j x) (j y)
  diagonal x := D.diagonal (j x)
  nonneg x := D.nonneg (j x)
  eq_zero_iff x := by
    rw [D.eq_zero_iff]
    exact ⟨fun hx => hj (hx.trans j.map_zero.symm), fun hx => by rw [hx, j.map_zero]⟩

end
end BanachIsometric.MetricGeometry
