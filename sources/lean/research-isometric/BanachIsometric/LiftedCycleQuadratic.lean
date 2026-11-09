import BanachIsometric.LiftedCycleMomentIdentity
import BanachIsometric.EuclideanPolynomialQuadratic

/-! The actual lifted finite chain gives the same consecutive even powers as
the exact-family calculation. Nonzero signed moments are supplied by the
oriented reference sphere cycle. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set Metric MeasureTheory
open scoped NNReal Topology

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => EuclideanSpace ℝ (Fin (d + 2))
local notation "N" => (d + 2)
local notation "S" => sphere (0 : V) 1
local notation "P" => (Fin N → ℝ)
local notation "Op" => (E →L[ℝ] V)

theorem exists_posDef_quadratic_of_liftedCycle
    (μ : Measure P) [μ.IsAddHaarMeasure] {g : V → ℝ} {p : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : Continuous g) {K : ℝ≥0} (hK : LipschitzOnWith K g S)
    (hEven : Even N)
    (A : C(X, Op)) {LA : ℝ≥0} (hA : LipschitzWith LA A)
    (normal : C(X, S)) {LN : ℝ≥0} (hN : LipschitzWith LN normal)
    (htan : ∀ x y, inner ℝ (A x y) (normal x).val = 0)
    (hexact : ∀ x y, g (A x y) = p y)
    (c : RawRationalChains X (d + 1)) (hc : c ∈ rawLipschitzCarrier X (d + 1))
    (hcycle : rawBoundary d c = 0)
    (a : RawRationalChains S (d + 1)) (ha : a ∈ rawLipschitzCarrier S (d + 1))
    (b : RawRationalChains S (d + 2)) (hb : b ∈ rawLipschitzCarrier S (d + 2))
    (hfill : rawBoundary (d + 1) b = rawChainMap normal (d + 1) c - a)
    (hMoment : ∀ k ≤ 1, rawSignedSimplexMoment N μ (euclideanSimplexWeight N k)
      (rawLipschitzCone (d + 1) (rawChainMap (scaledGaugeSphereMap hg hcont 1) (d + 1) a)) ≠ 0) :
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  have hPow (k : ℕ) (hk : k ≤ 1) : ∃ Q : MvPolynomial (Fin m) ℝ, ∀ y : E,
      MvPolynomial.eval (fun j => y j) Q = p y ^ (N + 2 * k) := by
    let cA := rawLipschitzCone (d + 1) (rawChainMap A (d + 1) c)
    have hcA : cA ∈ rawLipschitzCarrier Op N := rawLipschitzCone_preserves_lipschitz (d + 1)
      (rawChainMap_preserves_lipschitz A hA (d + 1) hc)
    obtain ⟨Q, hQ, hQval⟩ := exists_homogeneous_operatorChain_moment m N μ k cA hcA
    let M := rawSignedSimplexMoment N μ (euclideanSimplexWeight N k)
      (rawLipschitzCone (d + 1) (rawChainMap (scaledGaugeSphereMap hg hcont 1) (d + 1) a))
    have hM : M ≠ 0 := hMoment k hk
    refine ⟨MvPolynomial.C M⁻¹ * Q, fun y => ?_⟩
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    by_cases hy : y = 0
    · subst y
      have hd : N + 2 * k ≠ 0 := by omega
      have hcQ : Q.coeff 0 = 0 := hQ.coeff_eq_zero (by simpa using Ne.symm hd)
      change M⁻¹ * MvPolynomial.eval (0 : Fin m → ℝ) Q = p 0 ^ (N + 2 * k)
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, hcQ, (hp.eq_zero_iff 0).mpr rfl,
        zero_pow hd, mul_zero]
    · have he := liftedCycle_operatorMoment_eq_power μ hg hp hcont hK A hA normal hN htan hexact
        c hc hcycle a ha b hb hfill k y hy
      rw [hQval]
      change M⁻¹ * (rawSignedSimplexMoment N μ (euclideanSimplexWeight N k)
        (rawChainMap (continuousLinearSingularMap (operatorSimplexEval m N y)) N cA)) = _
      rw [show _ = p y ^ (N + 2 * k) * M from he]
      calc
        M⁻¹ * (p y ^ (N + 2 * k) * M) = p y ^ (N + 2 * k) * (M⁻¹ * M) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hM, mul_one]
  obtain ⟨j, hj⟩ := hEven
  have hj₂ : N = 2 * j := by omega
  have hj₀ : 0 < j := by omega
  obtain ⟨Q₀, hQ₀⟩ := hPow 0 (by omega)
  obtain ⟨Q₁, hQ₁⟩ := hPow 1 (by omega)
  apply exists_posDef_euclidean_quadraticForm_of_consecutive_even_powers hp hj₀
  · exact ⟨Q₀, fun y => by simpa only [hj₂, mul_zero, add_zero] using hQ₀ y⟩
  · exact ⟨Q₁, fun y => by simpa only [hj₂, mul_one] using hQ₁ y⟩

end BanachIsometric.SingularPrism
