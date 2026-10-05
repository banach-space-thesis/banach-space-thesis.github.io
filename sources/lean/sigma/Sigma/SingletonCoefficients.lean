import Sigma.IndexedAtoms
import Sigma.JLEvaluation

/-! At an isolated atom the dual coefficient is the value of the functional
on the corresponding singleton indicator. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem jlDual_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (φ : JL B →L[ℝ] ℝ) (p : Point) :
    jlDualEquiv hB hInf φ (↑(Sum.inl p : MrowkaBase B)) =
      φ ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩ := by
  classical
  have h := (jlDual_apply_hasSum hB hInf φ
    ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩).tsum_eq
  rw [jlContinuous_singleton] at h
  simp only [singletonFunction_apply,mul_ite,mul_one,mul_zero] at h
  rw [tsum_eq_single (f := fun q : AUCompactum B =>
    if q = ↑(Sum.inl p : MrowkaBase B) then jlDualEquiv hB hInf φ q else 0)
    (↑(Sum.inl p : MrowkaBase B) : AUCompactum B) (fun q hq => if_neg hq),if_pos rfl] at h
  exact h

theorem indexedJLDual_singleton {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : JL B →L[ℝ] ℝ) (p : Point) :
    indexedJLDualEquiv hB hInf e φ (.inl p) =
      φ ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩ := jlDual_singleton hB hInf φ p

def fibreVector (B : Set (Set Point)) (n : ℕ) : antisymmetricJL B :=
  ⟨characteristic {(n,false)} - characteristic {(n,true)},fibre_difference_mem B n⟩

theorem fibreVector_norm (B : Set (Set Point)) (n : ℕ) : ‖fibreVector B n‖ = 1 := by
  apply le_antisymm
  · change ‖characteristic {(n,false)} - characteristic {(n,true)}‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rintro ⟨m,bit⟩
    cases bit <;> by_cases h : m = n <;> simp [h]
  · have h := (fibreVector B n).val.norm_coe_le_norm (n,false)
    simpa [fibreVector] using h

end SigmaNonprimarity
