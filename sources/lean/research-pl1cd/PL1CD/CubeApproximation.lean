import PL1CD.HaarCubeEntropy
import PL1.WalshExpectations

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ENNReal

namespace PL1CD.Entropy
open PL1.Walsh PL1.Bonami

def liftLp (n : ℕ) (f : Cube n → ℝ) : Lp ℝ 1 haar :=
  ContinuousMap.toLp 1 haar ℝ (liftContinuous n f)

theorem liftLp_zero (n : ℕ) : liftLp n (fun _ => 0) = 0 := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n (fun _ => 0)), Lp.coeFn_zero ℝ 1 haar] with x hx hz
  exact hx.trans hz.symm

theorem liftLp_add (n : ℕ) (f g : Cube n → ℝ) :
    liftLp n (fun x => f x + g x) = liftLp n f + liftLp n g := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n (fun x => f x + g x)),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n f),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n g),
    Lp.coeFn_add (liftLp n f) (liftLp n g)] with x hx hf hg ha
  change liftLp n (fun x => f x + g x) x = f (sample n x) + g (sample n x) at hx
  change liftLp n f x = f (sample n x) at hf
  change liftLp n g x = g (sample n x) at hg
  rw [ha, Pi.add_apply, hf, hg]
  exact hx

theorem liftLp_smul (n : ℕ) (a : ℝ) (f : Cube n → ℝ) :
    liftLp n (fun x => a * f x) = a • liftLp n f := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n (fun x => a * f x)),
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar (liftContinuous n f),
    Lp.coeFn_smul a (liftLp n f)] with x hx hf hs
  change liftLp n (fun x => a * f x) x = a * f (sample n x) at hx
  change liftLp n f x = f (sample n x) at hf
  rw [hs, Pi.smul_apply, smul_eq_mul, hf]
  exact hx

theorem liftLp_character (n : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.range n) :
    liftLp n (cubeCharacter n F) = scalarCharacterLp ℝ 1 F := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
    (liftContinuous n (cubeCharacter n F)), coeFn_scalarCharacterLp ℝ 1 F] with x hx hy
  exact hx.trans ((cubeCharacter_sample n F hF x).trans hy.symm)

theorem exists_lift_of_finiteSpan (n : ℕ) (f : Lp ℝ 1 haar)
    (hf : f ∈ PL1.WalshExpectations.finiteSpan ℝ n) :
    ∃ g : Cube n → ℝ, liftLp n g = f := by
  apply Submodule.span_induction (p := fun f _ => ∃ g : Cube n → ℝ, liftLp n g = f)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨cubeCharacter n F, liftLp_character n F (Finset.mem_powerset.mp hF)⟩
  · exact ⟨fun _ => 0, liftLp_zero n⟩
  · rintro f g _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨fun x => v x + w x, liftLp_add n v w⟩
  · rintro a f _ ⟨v, rfl⟩
    exact ⟨fun x => a * v x, liftLp_smul n a v⟩

theorem sample_surjective (n : ℕ) : Function.Surjective (sample n) := by
  induction n with
  | zero => intro x; rcases x with ⟨⟩; exact ⟨1, rfl⟩
  | succ n ih =>
      rintro ⟨b, x⟩
      obtain ⟨y, hy⟩ := ih x
      let z : PL1.Walsh.Group := Function.update y n
        (if b then Multiplicative.ofAdd (1 : ZMod 2) else 1)
      have hz : sample n z = sample n y := by
        apply sample_congr
        intro j hj
        exact Function.update_of_ne (Nat.ne_of_lt hj) _ _
      refine ⟨z, ?_⟩
      change (signBit (z n), sample n z) = (b, x)
      rw [hz, hy]
      congr 1
      simp only [z, Function.update_self]
      cases b <;> decide

theorem convolution_preserves_Icc (ν : Measure PL1.Walsh.Group) [IsProbabilityMeasure ν]
    (f : Lp ℝ 1 haar) (C : ℝ) (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C) :
    ∀ᵐ x ∂haar, convolutionL1 ν f x ∈ Set.Icc 0 C := by
  have hb := (measurePreserving_multiply ν).quasiMeasurePreserving.ae hf
  filter_upwards [coeFn_convolutionL1 ν f, ae_ae_of_ae_prod hb,
    (integrable_convolution_integrand ν f).prod_right_ae] with x hx hbound hi
  rw [hx]
  constructor
  · exact integral_nonneg_of_ae (hbound.mono (fun y hy => hy.1))
  · calc
      _ ≤ ∫ _y : PL1.Walsh.Group, C ∂ν :=
        integral_mono_ae hi (integrable_const C) (hbound.mono (fun y hy => hy.2))
      _ = C := by simp [measureReal_def]

theorem liftLp_mem_Icc (n : ℕ) (f : Cube n → ℝ) (C : ℝ)
    (hf : ∀ᵐ x ∂haar, liftLp n f x ∈ Set.Icc 0 C) : ∀ x, f x ∈ Set.Icc 0 C := by
  have hae : ∀ᵐ x ∂haar, f (sample n x) ∈ Set.Icc 0 C := by
    filter_upwards [hf, ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) haar
      (liftContinuous n f)] with x hx he
    change liftLp n f x = f (sample n x) at he
    rwa [he] at hx
  have heq := ((isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) C)).preimage
    (continuous_lift n f)).ae_eq_univ_iff_eq.mp (ae_eq_univ.mpr hae)
  intro x
  obtain ⟨y, rfl⟩ := sample_surjective n x
  have hy := heq.symm ▸ (Set.mem_univ y)
  exact hy

theorem exists_bounded_lift_expectation (n : ℕ) (f : Lp ℝ 1 haar) (C : ℝ)
    (hf : ∀ᵐ x ∂haar, f x ∈ Set.Icc 0 C) :
    ∃ g : Cube n → ℝ, liftLp n g = PL1.WalshExpectations.expectationL1 ℝ n f ∧
      ∀ x, g x ∈ Set.Icc 0 C := by
  obtain ⟨g, hg⟩ := exists_lift_of_finiteSpan n _
    (PL1.WalshExpectations.expectationL1_mem_finiteSpan ℝ n f)
  refine ⟨g, hg, liftLp_mem_Icc n g C ?_⟩
  rw [hg]
  exact convolution_preserves_Icc _ f C hf

end PL1CD.Entropy
