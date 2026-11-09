import BanachIsometric.SingularPontryaginInterchange

/-! The actual continuous diagonal induces an algebra homomorphism to
the Koszul tensor algebra of rational singular homology. Thus an actual
positive even primitive class vanishes whenever homology is bounded. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW
open scoped DirectSum TensorProduct

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

theorem rawPontryaginDiagonal_mul (p q : ℕ) (a : RawHomology G p) (b : RawHomology G q) :
    rawPontryaginDiagonal G (p + q) (rawPontryaginMul G rfl a b) =
      rawPontryaginDiagonal G p a * rawPontryaginDiagonal G q b := by
  let δ := awTopologicalDiagonal G
  let μ := awTopologicalMul G
  let γ := awMultiplicationInterchange G
  let u := rawSingularKunnethEquiv G G p (rawFullHomologyMap δ p a)
  let v := rawSingularKunnethEquiv G G q (rawFullHomologyMap δ q b)
  have hgeom : δ.comp μ = γ.comp (awProductMap δ δ) := rfl
  change rawPontryaginTensorInclusion G (p + q) (rawSingularKunnethEquiv G G (p + q)
      (rawFullHomologyMap δ (p + q) (rawFullHomologyMap μ (p + q) (rawHomologyCross G G rfl a b)))) =
    rawPontryaginTensorInclusion G p u * rawPontryaginTensorInclusion G q v
  rw [← rawFullHomologyMap_apply_comp μ δ, hgeom, rawFullHomologyMap_apply_comp,
    rawHomologyCross_naturality]
  have he := rawPontryaginInterchange G p q u v
  dsimp only [u, v] at he
  simpa only [LinearEquiv.symm_apply_apply] using he

def rawPontryaginCoproduct : RawPontryaginAlgebra G →ₐ[ℚ] KoszulTensor (rawPontryaginDegree G) :=
  DirectSum.toAlgebra ℚ (RawHomology G) (rawPontryaginDiagonal G)
    (rawPontryaginDiagonal_one G) (fun a b => rawPontryaginDiagonal_mul G _ _ a b)

@[simp] theorem rawPontryaginCoproduct_inclusion (n : ℕ) (a : RawHomology G n) :
    rawPontryaginCoproduct G (rawPontryaginInclusion G n a) = rawPontryaginDiagonal G n a := by
  rw [rawPontryaginInclusion, DirectSum.lof_eq_of]
  exact DirectSum.toSemiring_of (fun i => (rawPontryaginDiagonal G i).toAddMonoidHom)
    (rawPontryaginDiagonal_one G) (fun a b => rawPontryaginDiagonal_mul G _ _ a b) n a

theorem rawPontryaginUnit_ne_zero : rawPontryaginUnit G ≠ 0 := by
  intro h
  have he := congrArg (rawFullZeroAugmentation G) h
  have he' : (1 : ℚ) = 0 := by
    simpa only [rawPontryaginUnit, rawFullZeroAugmentation_point, map_zero] using he
  exact one_ne_zero he'

theorem rawPontryagin_even_primitive_zero (N : ℕ)
    (hbounded : ∀ n, N < n → Subsingleton (RawHomology G n)) {n : ℕ}
    (hpos : 0 < n) (heven : Even n) (a : RawHomology G n)
    (hprim : rawSingularKunnethEquiv G G n (rawFullHomologyMap (awTopologicalDiagonal G) n a) =
      rawHomologyTensorInclusion G G (n := n) (p := n) (q := 0) (Nat.add_zero n)
        (a ⊗ₜ[ℚ] rawPontryaginUnit G) +
        rawHomologyTensorInclusion G G (n := n) (p := 0) (q := n) (Nat.zero_add n)
          (rawPontryaginUnit G ⊗ₜ[ℚ] a)) :
    a = 0 := by
  letI : Nontrivial (RawPontryaginAlgebra G) := nontrivial_of_ne
    (rawPontryaginInclusion G 0 (rawPontryaginUnit G)) (rawPontryaginInclusion G 0 0)
    (fun h => rawPontryaginUnit_ne_zero G (rawPontryaginInclusion_injective G 0 h))
  have hdiag : rawPontryaginCoproduct G (rawPontryaginInclusion G n a) =
      KoszulTensor.tmul (rawPontryaginDegree G) (rawPontryaginInclusion G n a) 1 +
        KoszulTensor.tmul (rawPontryaginDegree G) 1 (rawPontryaginInclusion G n a) := by
    rw [rawPontryaginCoproduct_inclusion]
    change rawPontryaginTensorInclusion G n
      (rawSingularKunnethEquiv G G n (rawFullHomologyMap (awTopologicalDiagonal G) n a)) = _
    rw [hprim, map_add, rawPontryaginTensorInclusion_tmul, rawPontryaginTensorInclusion_tmul,
      rawPontryaginInclusion_one G]
  have hzero := even_primitive_eq_zero_of_bounded_koszul_algHom (rawPontryaginDegree G) N
    (fun d hd => rawPontryaginDegree_eq_bot_of_subsingleton G d (hbounded d hd))
    (rawPontryaginCoproduct G) hpos heven (rawPontryaginInclusion_mem_degree G n a) hdiag
  apply rawPontryaginInclusion_injective G n
  simpa only [map_zero] using hzero

theorem rawPontryagin_even_class_zero_of_diagonal_graph_sum (N : ℕ)
    (hbounded : ∀ n, N < n → Subsingleton (RawHomology G n)) {n : ℕ}
    (hpos : 0 < n) (heven : Even n) (a : RawHomology G n)
    (hdiag : rawFullHomologyMap (awTopologicalDiagonal G) n a =
      rawFullHomologyMap (awPointGraphRight (1 : G)) n a +
        rawFullHomologyMap (awPointGraphLeft (1 : G)) n a) : a = 0 := by
  apply rawPontryagin_even_primitive_zero G N hbounded hpos heven a
  have hR : rawSingularKunnethEquiv G G n (rawFullHomologyMap (awPointGraphRight (1 : G)) n a) =
      rawHomologyTensorInclusion G G (n := n) (p := n) (q := 0) (Nat.add_zero n)
        (a ⊗ₜ[ℚ] rawPontryaginUnit G) :=
    (congrArg (rawSingularKunnethEquiv G G n) (rawHomologyCross_point_right n a (1 : G)).symm).trans
      (rawHomologyCross_compare G G (n := n) (rfl : n + 0 = n) a (rawPontryaginUnit G))
  have hL : rawSingularKunnethEquiv G G n (rawFullHomologyMap (awPointGraphLeft (1 : G)) n a) =
      rawHomologyTensorInclusion G G (n := n) (p := 0) (q := n) (Nat.zero_add n)
        (rawPontryaginUnit G ⊗ₜ[ℚ] a) :=
    (congrArg (rawSingularKunnethEquiv G G n) (rawHomologyCross_point_left n (1 : G) a).symm).trans
      (rawHomologyCross_compare G G (Nat.zero_add n) (rawPontryaginUnit G) a)
  rw [hdiag, map_add, hR, hL]

end BanachIsometric.SingularEZ
