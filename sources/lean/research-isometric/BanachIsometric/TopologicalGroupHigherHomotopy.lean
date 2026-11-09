import BanachIsometric.ProductHigherHomotopy

/-! Pointwise group multiplication and the actual cubical homotopy groups.
The pointwise operation agrees with the pinned concatenation group law;
therefore every positive homotopy group of an actual topological group is
commutative, including its fundamental group, and its actual power map induces
the power operation on that homotopy group. No torsion or rationalization
assertion is assumed or inferred here. -/

noncomputable section
namespace BanachIsometric

open SphereGenerator
open scoped Topology Topology.Homotopy unitInterval

variable {N G : Type*} [DecidableEq N] [Nonempty N]
    [TopologicalSpace G] [Group G] [ContinuousMul G]

def topologicalGroupMultiplication : C(G × G, G) :=
  ⟨fun z => z.1 * z.2, continuous_fst.mul continuous_snd⟩

def pointwiseGroupGenLoop (α β : GenLoop N G 1) : GenLoop N G 1 :=
  mapGenLoop topologicalGroupMultiplication (one_mul 1) (productGenLoop α β)

omit [DecidableEq N] [Nonempty N] in
@[simp] theorem pointwiseGroupGenLoop_apply (α β : GenLoop N G 1)
    (u : N → unitInterval) : pointwiseGroupGenLoop α β u = α u * β u := rfl

omit [ContinuousMul G] in
theorem productHigherHomotopyEquiv_symm_classes
    (α β : GenLoop N G 1) :
    (productHigherHomotopyEquiv (N := N) (x := (1 : G)) (y := (1 : G))).symm
      (genLoopClass α, genLoopClass β) = genLoopClass (productGenLoop α β) := by
  apply (productHigherHomotopyEquiv (N := N) (x := (1 : G)) (y := (1 : G))).injective
  rw [MulEquiv.apply_symm_apply]
  apply Prod.ext
  · change genLoopClass α = genLoopClass (mapGenLoop ContinuousMap.fst rfl (productGenLoop α β))
    rw [mapGenLoop_fst_product]
  · change genLoopClass β = genLoopClass (mapGenLoop ContinuousMap.snd rfl (productGenLoop α β))
    rw [mapGenLoop_snd_product]

def pointwiseGroupHomotopyHom :
    (HomotopyGroup N G 1 × HomotopyGroup N G 1) →* HomotopyGroup N G 1 :=
  (basedHomotopyGroupMap topologicalGroupMultiplication (one_mul 1)).comp
    (productHigherHomotopyEquiv (N := N) (x := (1 : G)) (y := (1 : G))).symm.toMonoidHom

theorem pointwiseGroupHomotopyHom_classes (α β : GenLoop N G 1) :
    pointwiseGroupHomotopyHom (genLoopClass α, genLoopClass β) =
      genLoopClass (pointwiseGroupGenLoop α β) := by
  change basedHomotopyGroupMap topologicalGroupMultiplication (one_mul 1)
    ((productHigherHomotopyEquiv (N := N) (x := (1 : G)) (y := (1 : G))).symm
      (genLoopClass α, genLoopClass β)) = _
  rw [productHigherHomotopyEquiv_symm_classes]
  rfl

theorem pointwiseGroupHomotopyHom_one_left (a : HomotopyGroup N G 1) :
    pointwiseGroupHomotopyHom (1, a) = a := by
  induction a using Quotient.inductionOn with
  | h α =>
    change pointwiseGroupHomotopyHom (genLoopClass GenLoop.const, genLoopClass α) = _
    rw [pointwiseGroupHomotopyHom_classes]
    congr 1
    ext u
    exact one_mul (α u)

theorem pointwiseGroupHomotopyHom_one_right (a : HomotopyGroup N G 1) :
    pointwiseGroupHomotopyHom (a, 1) = a := by
  induction a using Quotient.inductionOn with
  | h α =>
    change pointwiseGroupHomotopyHom (genLoopClass α, genLoopClass GenLoop.const) = _
    rw [pointwiseGroupHomotopyHom_classes]
    congr 1
    ext u
    exact mul_one (α u)

theorem pointwiseGroupHomotopyHom_eq_mul (a b : HomotopyGroup N G 1) :
    pointwiseGroupHomotopyHom (a, b) = a * b := by
  calc
    pointwiseGroupHomotopyHom (a, b) =
        pointwiseGroupHomotopyHom ((a, 1) * (1, b)) := by simp only [Prod.mk_mul_mk, mul_one, one_mul]
    _ = pointwiseGroupHomotopyHom (a, 1) * pointwiseGroupHomotopyHom (1, b) :=
      map_mul _ _ _
    _ = a * b := by rw [pointwiseGroupHomotopyHom_one_right, pointwiseGroupHomotopyHom_one_left]

theorem genLoopClass_pointwiseGroupGenLoop (α β : GenLoop N G 1) :
    genLoopClass (pointwiseGroupGenLoop α β) = genLoopClass α * genLoopClass β := by
  rw [← pointwiseGroupHomotopyHom_classes, pointwiseGroupHomotopyHom_eq_mul]

theorem homotopyGroup_mul_comm_of_topologicalGroup (a b : HomotopyGroup N G 1) :
    a * b = b * a := by
  rw [← pointwiseGroupHomotopyHom_eq_mul]
  calc
    pointwiseGroupHomotopyHom (a, b) =
        pointwiseGroupHomotopyHom ((1, b) * (a, 1)) := by simp only [Prod.mk_mul_mk, mul_one, one_mul]
    _ = pointwiseGroupHomotopyHom (1, b) * pointwiseGroupHomotopyHom (a, 1) :=
      map_mul _ _ _
    _ = b * a := by rw [pointwiseGroupHomotopyHom_one_left, pointwiseGroupHomotopyHom_one_right]

omit [DecidableEq N] [Nonempty N] in
def topologicalGroupPowerMap (d : ℕ) : C(G, G) :=
  ⟨fun x => x ^ d, continuous_id.pow d⟩

theorem basedHomotopyGroupMap_power (d : ℕ) (a : HomotopyGroup N G 1) :
    basedHomotopyGroupMap (topologicalGroupPowerMap d) (one_pow d) a = a ^ d := by
  induction a using Quotient.inductionOn with
  | h α =>
    induction d with
    | zero =>
      change genLoopClass (mapGenLoop (topologicalGroupPowerMap 0) (one_pow 0) α) = 1
      have hz : mapGenLoop (topologicalGroupPowerMap 0) (one_pow 0) α = GenLoop.const := by
        ext u
        exact pow_zero (α u)
      rw [hz]
      rfl
    | succ d hd =>
      change genLoopClass (mapGenLoop (topologicalGroupPowerMap (d + 1)) (one_pow (d + 1)) α) =
        genLoopClass α ^ (d + 1)
      have hs : mapGenLoop (topologicalGroupPowerMap (d + 1)) (one_pow (d + 1)) α =
          pointwiseGroupGenLoop (mapGenLoop (topologicalGroupPowerMap d) (one_pow d) α) α := by
        ext u
        exact pow_succ (α u) d
      rw [hs, genLoopClass_pointwiseGroupGenLoop]
      change genLoopClass (mapGenLoop (topologicalGroupPowerMap d) (one_pow d) α) =
        genLoopClass α ^ d at hd
      rw [hd, pow_succ]

end BanachIsometric
