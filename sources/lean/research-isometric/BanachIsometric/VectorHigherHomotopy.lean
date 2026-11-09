import BanachIsometric.HomotopyRepetition
import Mathlib.Analysis.Normed.Module.Basic

/-! Every actual cubical loop in a real normed vector space is contracted
relative to its actual boundary by affine interpolation to its basepoint.
Consequently its pinned Mathlib homotopy groups are literally trivial. -/

noncomputable section
namespace BanachIsometric
open scoped Topology Topology.Homotopy unitInterval

theorem genLoop_homotopic_const_realVector
    {N V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {v : V}
    (α : GenLoop N V v) : GenLoop.Homotopic α GenLoop.const := by
  refine ⟨{
    toFun := fun z => (1 - (z.1 : ℝ)) • α z.2 + (z.1 : ℝ) • v
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (α.1.continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  · intro u
    change (1 - (0 : ℝ)) • α u + (0 : ℝ) • v = α u
    simp
  · intro u
    change (1 - (1 : ℝ)) • α u + (1 : ℝ) • v = v
    simp
  · intro t u hu
    change (1 - (t : ℝ)) • α u + (t : ℝ) • v = α u
    have hu' : α u = v := α.property u hu
    rw [hu', ← add_smul]
    simp

theorem subsingleton_homotopyGroup_realVector
    {N V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) :
    Subsingleton (HomotopyGroup N V v) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      exact Quotient.sound ((genLoop_homotopic_const_realVector α).trans
        (genLoop_homotopic_const_realVector β).symm)

end BanachIsometric
