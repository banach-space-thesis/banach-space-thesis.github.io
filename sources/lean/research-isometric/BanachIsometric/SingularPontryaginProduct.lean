import BanachIsometric.SingularCrossReassociation
import BanachIsometric.SingularCrossPointUnit

/-! The actual Pontryagin product is induced by the continuous monoid
multiplication after the rational singular crossproduct. Its associativity
and unit are inherited from those literal continuous maps. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open SingularAW

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

def awTopologicalMul : C(G × G, G) := ⟨fun z => z.1 * z.2, continuous_mul⟩

def rawPontryaginUnit : RawHomology G 0 := rawHomologyPoint G 1

def rawPontryaginMul {n p q : ℕ} (h : p + q = n) :
    RawHomology G p →ₗ[ℚ] RawHomology G q →ₗ[ℚ] RawHomology G n :=
  (rawHomologyCross G G h).compr₂ (rawFullHomologyMap (awTopologicalMul G) n)

theorem rawPontryaginMul_apply {n p q : ℕ} (h : p + q = n) (a : RawHomology G p)
    (b : RawHomology G q) :
    rawPontryaginMul G h a b = rawFullHomologyMap (awTopologicalMul G) n (rawHomologyCross G G h a b) :=
  rfl

theorem rawPontryaginMul_one_left (n : ℕ) (a : RawHomology G n) :
    rawPontryaginMul G (Nat.zero_add n) (rawPontryaginUnit G) a = a := by
  rw [rawPontryaginMul_apply, rawPontryaginUnit, rawHomologyCross_point_left, ← rawFullHomologyMap_apply_comp]
  have h : (awTopologicalMul G).comp (awPointGraphLeft (1 : G)) = ContinuousMap.id G := by
    apply ContinuousMap.ext
    intro x
    exact one_mul x
  rw [h, rawFullHomologyMap_id, LinearMap.id_apply]

theorem rawPontryaginMul_one_right (n : ℕ) (a : RawHomology G n) :
    rawPontryaginMul G (rfl : n + 0 = n) a (rawPontryaginUnit G) = a := by
  change rawFullHomologyMap (awTopologicalMul G) n
    (rawHomologyCross G G (rfl : n + 0 = n) a (rawHomologyPoint G 1)) = a
  rw [rawHomologyCross_point_right,
    ← rawFullHomologyMap_apply_comp (awPointGraphRight (1 : G)) (awTopologicalMul G) n a]
  have h : (awTopologicalMul G).comp (awPointGraphRight (1 : G)) = ContinuousMap.id G := by
    apply ContinuousMap.ext
    intro x
    exact mul_one x
  rw [h, rawFullHomologyMap_id, LinearMap.id_apply]

theorem rawPontryaginMul_assoc {n p q r : ℕ} (h : p + q + r = n)
    (a : RawHomology G p) (b : RawHomology G q) (c : RawHomology G r) :
    rawPontryaginMul G h (rawPontryaginMul G rfl a b) c =
      rawPontryaginMul G (by omega : p + (q + r) = n) a (rawPontryaginMul G rfl b c) := by
  let μ := awTopologicalMul G
  let f := awProductMap μ (ContinuousMap.id G)
  let g := awProductMap (ContinuousMap.id G) μ
  let t := rawHomologyCross (G × G) G h (rawHomologyCross G G rfl a b) c
  let t' := rawHomologyCross G (G × G) (by omega : p + (q + r) = n) a (rawHomologyCross G G rfl b c)
  have hassoc : (μ.comp g).comp awProductAssoc = μ.comp f := by
    apply ContinuousMap.ext
    intro z
    exact (mul_assoc z.1.1 z.1.2 z.2).symm
  have h₁ := rawHomologyCross_naturality μ (ContinuousMap.id G) h (rawHomologyCross G G rfl a b) c
  rw [rawFullHomologyMap_id, LinearMap.id_apply] at h₁
  have h₂ := rawHomologyCross_naturality (ContinuousMap.id G) μ (by omega : p + (q + r) = n)
    a (rawHomologyCross G G rfl b c)
  rw [rawFullHomologyMap_id, LinearMap.id_apply] at h₂
  simp only [rawPontryaginMul_apply]
  change rawFullHomologyMap μ n _ = rawFullHomologyMap μ n _
  rw [← h₁, ← h₂, ← rawFullHomologyMap_apply_comp f μ n t, ← rawFullHomologyMap_apply_comp g μ n t']
  rw [← hassoc, rawFullHomologyMap_apply_comp]
  exact congrArg (rawFullHomologyMap (μ.comp g) n) (rawHomologyCross_associativity G G G h a b c)

theorem rawPontryaginMul_heq {n p q : ℕ} (h : p + q = n)
    (a : RawHomology G p) (b : RawHomology G q) :
    HEq (rawPontryaginMul G (rfl : p + q = p + q) a b) (rawPontryaginMul G h a b) := by
  subst n
  rfl

end BanachIsometric.SingularEZ
