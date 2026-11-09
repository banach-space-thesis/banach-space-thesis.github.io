import BanachIsometric.BodyGroupFiniteDomination
import BanachIsometric.OpenSubgroupRetraction
import BanachIsometric.ComponentCovering

/-! The actual connected identity body group is dominated by an actual
finite simplicial polyhedron. It is an open normal subgroup of the actual
compact body group and hence an actual continuous retract. No finite-CW,
cohomological or rational-vanishing assertion is assumed here. -/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory
open scoped Topology

theorem bodyIdentityComponent_finite_polyhedron_domination {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, ∃ K : FiniteNerve.Complex (Fin n),
      ∃ f : C(Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S), K.space),
      ∃ g : C(K.space, Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)),
        Nonempty ((g.comp f).Homotopy
          (ContinuousMap.id (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)))) := by
  let G := bodyAutomorphismGroup S
  let H := Subgroup.connectedComponentOfOne G
  letI : H.Normal := connectedComponentOfOne_normal G
  have hH : IsOpen (H : Set G) :=
    isOpen_bodyAutomorphismGroup_connectedComponent_of_interior μ S hS hreg h0
  let r : C(G, H) := openNormalSubgroupRetraction H hH
  obtain ⟨n, K, f, g, ⟨A⟩⟩ := bodyAutomorphismGroup_finite_polyhedron_domination μ S hS hreg h0
  let fH : C(H, K.space) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  let gH : C(K.space, H) := r.comp g
  refine ⟨n, K, fH, gH, ⟨{
    toFun := fun z => r (A (z.1, z.2.val))
    continuous_toFun := r.continuous.comp
      (A.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    change r (A (0, x.val)) = r (g (f x.val))
    rw [A.apply_zero]
    rfl
  · intro x
    change r (A (1, x.val)) = x
    rw [A.apply_one]
    exact openNormalSubgroupRetraction_fixes H hH x

end BanachIsometric
