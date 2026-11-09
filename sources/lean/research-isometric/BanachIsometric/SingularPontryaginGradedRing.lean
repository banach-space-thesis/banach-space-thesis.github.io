import BanachIsometric.SingularPontryaginProduct
import Mathlib.Algebra.DirectSum.Algebra

/-! The literal direct sum of rational homology groups is the graded
Pontryagin algebra. Its homogeneous multiplication is the actual
singular product induced by monoid multiplication. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW
open scoped DirectSum

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

instance rawHomologyGMonoid : GradedMonoid.GMonoid (RawHomology G) := by
  letI gOne : GradedMonoid.GOne (RawHomology G) := ⟨rawPontryaginUnit G⟩
  letI gMul : GradedMonoid.GMul (RawHomology G) := ⟨fun a b => rawPontryaginMul G rfl a b⟩
  refine
    { toGOne := gOne
      toGMul := gMul
      one_mul := ?_
      mul_one := ?_
      mul_assoc := ?_
      gnpow := GradedMonoid.GMonoid.gnpowRec
      gnpow_zero' := GradedMonoid.GMonoid.gnpowRec_zero
      gnpow_succ' := GradedMonoid.GMonoid.gnpowRec_succ }
  ·
    rintro ⟨n, a⟩
    apply Sigma.ext (Nat.zero_add n)
    exact (rawPontryaginMul_heq G (Nat.zero_add n) (rawPontryaginUnit G) a).trans
      (heq_of_eq (rawPontryaginMul_one_left G n a))
  ·
    rintro ⟨n, a⟩
    exact Sigma.ext rfl (heq_of_eq (rawPontryaginMul_one_right G n a))
  ·
    rintro ⟨p, a⟩ ⟨q, b⟩ ⟨r, c⟩
    apply Sigma.ext (Nat.add_assoc p q r)
    have h : p + (q + r) = p + q + r := (Nat.add_assoc p q r).symm
    exact (heq_of_eq (rawPontryaginMul_assoc G (rfl : p + q + r = p + q + r) a b c)).trans
      (rawPontryaginMul_heq G h a (rawPontryaginMul G rfl b c)).symm

instance rawHomologyGRing : DirectSum.GRing (RawHomology G) where
  __ := rawHomologyGMonoid G
  mul_zero a := (rawPontryaginMul G rfl a).map_zero
  zero_mul b := LinearMap.congr_fun ((rawPontryaginMul G rfl).map_zero) b
  mul_add a b c := (rawPontryaginMul G rfl a).map_add b c
  add_mul a b c := LinearMap.congr_fun ((rawPontryaginMul G rfl).map_add a b) c
  natCast n := n • rawPontryaginUnit G
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    change (n + 1) • rawPontryaginUnit G = n • rawPontryaginUnit G + rawPontryaginUnit G
    rw [add_nsmul, one_nsmul]
  intCast z := z • rawPontryaginUnit G
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

theorem rawPontryaginMul_smul_left {n p q : ℕ} (h : p + q = n) (r : ℚ)
    (a : RawHomology G p) (b : RawHomology G q) :
    rawPontryaginMul G h (r • a) b = r • rawPontryaginMul G h a b :=
  LinearMap.congr_fun ((rawPontryaginMul G h).map_smul r a) b

theorem rawPontryaginMul_smul_right {n p q : ℕ} (h : p + q = n) (r : ℚ)
    (a : RawHomology G p) (b : RawHomology G q) :
    rawPontryaginMul G h a (r • b) = r • rawPontryaginMul G h a b :=
  (rawPontryaginMul G h a).map_smul r b

theorem rawPontryaginMul_scalar_left_heq (n : ℕ) (r : ℚ) (a : RawHomology G n) :
    HEq (rawPontryaginMul G (rfl : 0 + n = 0 + n) (r • rawPontryaginUnit G) a) (r • a) := by
  apply (rawPontryaginMul_heq G (Nat.zero_add n) (r • rawPontryaginUnit G) a).trans
  apply heq_of_eq
  rw [rawPontryaginMul_smul_left, rawPontryaginMul_one_left]

theorem rawPontryaginMul_scalar_right (n : ℕ) (r : ℚ) (a : RawHomology G n) :
    rawPontryaginMul G (rfl : n + 0 = n) a (r • rawPontryaginUnit G) = r • a := by
  rw [rawPontryaginMul_smul_right, rawPontryaginMul_one_right]

instance rawHomologyGAlgebra : DirectSum.GAlgebra ℚ (RawHomology G) where
  toFun := ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (rawPontryaginUnit G)).toAddMonoidHom
  map_one := by
    change (1 : ℚ) • rawPontryaginUnit G = rawPontryaginUnit G
    exact one_smul ℚ _
  map_mul r s := by
    have h : (r * s) • rawPontryaginUnit G =
        rawPontryaginMul G (rfl : 0 + 0 = 0) (r • rawPontryaginUnit G) (s • rawPontryaginUnit G) := by
      rw [rawPontryaginMul_smul_left, rawPontryaginMul_smul_right, rawPontryaginMul_one_left, smul_smul]
    exact congrArg (GradedMonoid.mk (A := RawHomology G) 0) h
  commutes := by
    rintro r ⟨n, a⟩
    apply Sigma.ext (Nat.zero_add n)
    exact (rawPontryaginMul_scalar_left_heq G n r a).trans
      (heq_of_eq (rawPontryaginMul_scalar_right G n r a).symm)
  smul_def := by
    rintro r ⟨n, a⟩
    exact Sigma.ext (Nat.zero_add n).symm (rawPontryaginMul_scalar_left_heq G n r a).symm

abbrev RawPontryaginAlgebra := ⨁ n, RawHomology G n

def rawPontryaginInclusion (n : ℕ) : RawHomology G n →ₗ[ℚ] RawPontryaginAlgebra G :=
  DirectSum.lof ℚ ℕ (RawHomology G) n

theorem rawPontryaginInclusion_one :
    rawPontryaginInclusion G 0 (rawPontryaginUnit G) = 1 := by
  simp only [rawPontryaginInclusion, DirectSum.lof_eq_of, DirectSum.one_def]
  rfl

theorem rawPontryaginInclusion_mul (p q : ℕ) (a : RawHomology G p) (b : RawHomology G q) :
    rawPontryaginInclusion G p a * rawPontryaginInclusion G q b =
      rawPontryaginInclusion G (p + q) (rawPontryaginMul G rfl a b) := by
  simp only [rawPontryaginInclusion, DirectSum.lof_eq_of, DirectSum.of_mul_of]
  rfl

end BanachIsometric.SingularEZ
