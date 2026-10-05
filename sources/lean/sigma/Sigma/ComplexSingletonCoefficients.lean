import Sigma.ComplexIndexedAtoms
import Sigma.ComplexJLEvaluation

/-! At an isolated atom the dual coefficient is the value of the functional
on the corresponding singleton indicator. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem complexJLDual_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (φ : ComplexJL B →L[ℂ] ℂ) (p : Point) :
    complexJLDualEquiv hB hInf φ (↑(Sum.inl p : MrowkaBase B)) =
      φ ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩ := by
  classical
  have h := (complexJLDual_apply_hasSum hB hInf φ
    ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩).tsum_eq
  rw [complexJLContinuous_singleton] at h
  have hcast (q : AUCompactum B) :
      (complexLiftRealContinuous (singletonFunction hB p) q) =
        if q = ↑(Sum.inl p : MrowkaBase B) then (1 : ℂ) else 0 := by
    simp only [complexLiftRealContinuous_apply,singletonFunction_apply]
    split_ifs <;> simp
  simp only [hcast,mul_ite,mul_one,mul_zero] at h
  rw [tsum_eq_single (f := fun q : AUCompactum B =>
    if q = ↑(Sum.inl p : MrowkaBase B) then complexJLDualEquiv hB hInf φ q else 0)
    (↑(Sum.inl p : MrowkaBase B) : AUCompactum B) (fun q hq => if_neg hq),if_pos rfl] at h
  exact h

theorem complexIndexedJLDual_singleton {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : ComplexJL B →L[ℂ] ℂ) (p : Point) :
    complexIndexedJLDualEquiv hB hInf e φ (.inl p) =
      φ ⟨complexCharacteristic {p},complexCharacteristic_singleton_mem_ComplexJL B p⟩ := complexJLDual_singleton hB hInf φ p

def complexFibreVector (B : Set (Set Point)) (n : ℕ) : complexAntisymmetricJL B :=
  ⟨complexCharacteristic {(n,false)} - complexCharacteristic {(n,true)},complex_fibre_difference_mem B n⟩

theorem complexFibreVector_norm (B : Set (Set Point)) (n : ℕ) : ‖complexFibreVector B n‖ = 1 := by
  apply le_antisymm
  · change ‖complexCharacteristic {(n,false)} - complexCharacteristic {(n,true)}‖ ≤ 1
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    rintro ⟨m,bit⟩
    cases bit <;> by_cases h : m = n <;> simp [h]
  · have h := (complexFibreVector B n).val.norm_coe_le_norm (n,false)
    simpa [complexFibreVector] using h

end SigmaNonprimarity


