import ThesisCommon.Analysis.MilutinInverseLimit
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma

/-! Cylinder functions on the concrete sequential inverse limit form a dense
star subalgebra. This is the Stone-Weierstrass step in Rosenthal Lemma 2.12. -/

noncomputable section
open Set
namespace ThesisCommon

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : ℕ → Type*} [∀ n, TopologicalSpace (K n)]
variable (φ : ∀ n, C(K (n + 1), K n))

def milutinCylinderSet (n : ℕ) : Set C(MilutinInverseLimit φ, 𝕜) :=
  Set.range fun f : C(K n, 𝕜) => f.comp (milutinLimitProjection φ n)

theorem milutinCylinderSet_monotone : Monotone (milutinCylinderSet (𝕜 := 𝕜) φ) := by
  apply monotone_nat_of_le_succ
  intro n g hg
  obtain ⟨f, rfl⟩ := hg
  refine ⟨f.comp (φ n), ?_⟩
  ext z
  exact congrArg f (z.property n)

def milutinCylinderAlgebra : StarSubalgebra 𝕜 C(MilutinInverseLimit φ, 𝕜) where
  carrier := {g | ∃ n, g ∈ milutinCylinderSet φ n}
  zero_mem' := ⟨0, 0, rfl⟩
  one_mem' := ⟨0, 1, rfl⟩
  add_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    obtain ⟨f', hf'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_left n m) hn
    obtain ⟨g', hg'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_right n m) hm
    exact ⟨max n m, f' + g', by rw [← hf', ← hg']; rfl⟩
  mul_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    obtain ⟨f', hf'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_left n m) hn
    obtain ⟨g', hg'⟩ := milutinCylinderSet_monotone φ (Nat.le_max_right n m) hm
    exact ⟨max n m, f' * g', by rw [← hf', ← hg']; rfl⟩
  algebraMap_mem' := fun a => ⟨0, ContinuousMap.const (K 0) a, rfl⟩
  star_mem' := by
    rintro f ⟨n, g, rfl⟩
    exact ⟨n, star g, rfl⟩

theorem milutinCylinderAlgebra_separatesPoints
    [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)] :
    (milutinCylinderAlgebra (𝕜 := 𝕜) φ).SeparatesPoints := by
  intro x y hxy
  have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  obtain ⟨n, hn⟩ : ∃ n, x.val n ≠ y.val n := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨f, hfx, hfy, _⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton : IsClosed ({x.val n} : Set (K n))) isClosed_singleton
    (Set.disjoint_singleton.2 hn)
  let g : C(K n, 𝕜) := ⟨fun t => (f t : 𝕜), by fun_prop⟩
  let h := g.comp (milutinLimitProjection φ n)
  refine ⟨h, ⟨h, ⟨n, g, rfl⟩, rfl⟩, ?_⟩
  change (f (x.val n) : 𝕜) ≠ (f (y.val n) : 𝕜)
  rw [hfx (mem_singleton _), hfy (mem_singleton _)]
  simpa using (zero_ne_one : (0 : 𝕜) ≠ 1)

theorem milutinCylinderAlgebra_dense
    [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)] :
    Dense (milutinCylinderAlgebra (𝕜 := 𝕜) φ : Set C(MilutinInverseLimit φ, 𝕜)) := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (milutinCylinderAlgebra (𝕜 := 𝕜) φ) (milutinCylinderAlgebra_separatesPoints φ)
  rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe, h]
  rfl

theorem milutinCylinder_functions_dense
    [∀ n, CompactSpace (K n)] [∀ n, T2Space (K n)] :
    Dense {g : C(MilutinInverseLimit φ, 𝕜) |
      ∃ (n : ℕ) (f : C(K n, 𝕜)), f.comp (milutinLimitProjection φ n) = g} :=
  milutinCylinderAlgebra_dense φ

end ThesisCommon
