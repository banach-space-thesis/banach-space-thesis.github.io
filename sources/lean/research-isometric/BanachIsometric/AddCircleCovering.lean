import BanachIsometric.GroupLocalCovering
import BanachIsometric.CoveringHigherHomotopy
import BanachIsometric.VectorHigherHomotopy
import Mathlib.Topology.Instances.AddCircle.Real

/-! The actual additive circle is covered by the real line. Combining this
proved covering with actual higher-homotopy invariance and the affine real
contraction proves vanishing of its actual higher homotopy groups. -/

noncomputable section
namespace BanachIsometric

theorem isCoveringMap_of_surjective_addGroup_localHomeomorph
    {E B : Type*} [AddGroup E] [AddGroup B] [TopologicalSpace E] [TopologicalSpace B]
    [IsTopologicalAddGroup E] (p : E →+ B) (hp : IsLocalHomeomorph p)
    (hsurj : Function.Surjective p) : IsCoveringMap p :=
  isCoveringMap_of_surjective_group_localHomeomorph p.toMultiplicative hp hsurj

theorem isCoveringMap_realToAddCircle (period : ℝ) (hperiod : 0 < period) :
    IsCoveringMap ((↑) : ℝ → AddCircle period) := by
  letI : Fact (0 < period) := ⟨hperiod⟩
  let p : ℝ →+ AddCircle period := QuotientAddGroup.mk' (AddSubgroup.zmultiples period)
  exact isCoveringMap_of_surjective_addGroup_localHomeomorph p
    (AddCircle.isLocalHomeomorph_coe period) (QuotientAddGroup.mk'_surjective _)

theorem subsingleton_higherHomotopy_addCircle (period : ℝ) (hperiod : 0 < period)
    (n : ℕ) : Subsingleton (HomotopyGroup (Fin (n + 2)) (AddCircle period) 0) := by
  letI := subsingleton_homotopyGroup_realVector (N := Fin (n + 2)) (0 : ℝ)
  exact (coveringHigherHomotopyEquiv (isCoveringMap_realToAddCircle period hperiod) 0 n).symm.injective.subsingleton

end BanachIsometric
