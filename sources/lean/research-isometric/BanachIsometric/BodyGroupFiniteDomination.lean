import BanachIsometric.CompactNeighborhoodNerve
import BanachIsometric.BodyRetractionTransport

/-! An actual compact body automorphism group is dominated by a finite
simplicial polyhedron. Its actual inherited operator-unit topology is retained.
The ambient neighborhood retraction and compactness are constructed from the
body hypotheses; finite-type, triangulation or Lie classification is not assumed.
-/

noncomputable section
namespace BanachIsometric

open Set MeasureTheory
open scoped Topology

theorem bodyAutomorphismGroup_finite_polyhedron_domination {m : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (S : Set (EuclideanSpace ℝ (Fin m))) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S) :
    ∃ n : ℕ, ∃ K : FiniteNerve.Complex (Fin n),
      ∃ f : C(bodyAutomorphismGroup S, K.space),
      ∃ g : C(K.space, bodyAutomorphismGroup S),
        Nonempty ((g.comp f).Homotopy (ContinuousMap.id (bodyAutomorphismGroup S))) := by
  let E := EuclideanSpace ℝ (Fin m)
  let A := E →L[ℝ] E
  let G := bodyAutomorphismGroup S
  letI : CompactSpace G := compactSpace_bodyAutomorphismGroup_of_interior μ S hS h0
  let j : G → A := fun g => (g.val : A)
  have hj : Topology.IsEmbedding j :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let T : Set A := Set.range j
  have hT : IsCompact T := isCompact_range hj.continuous
  obtain ⟨D⟩ := nonempty_ambientBodyRetraction μ S hS hreg h0
  have hTU : T ⊆ D.domain := by
    rintro x ⟨g, rfl⟩
    exact D.contains g
  have hrange : ∀ x ∈ D.domain, D.retract x ∈ T := by
    intro x hx
    obtain ⟨⟨u, hu⟩, hbody⟩ := D.range x hx
    refine ⟨⟨u, ?_⟩, hu⟩
    change (u : A) '' S = S
    rwa [hu]
  have hfix : ∀ x ∈ T, D.retract x = x := by
    rintro x ⟨g, rfl⟩
    exact D.fixes g
  obtain ⟨n, K, f, g, ⟨H⟩⟩ := FiniteNerve.exists_finite_nerve_domination
    hT D.isOpen_domain hTU D.retract D.lipschitz.continuousOn hrange hfix
  let e : G ≃ₜ T := hj.toHomeomorph
  let fG : C(G, K.space) := f.comp ⟨e, e.continuous⟩
  let gG : C(K.space, G) := (⟨e.symm, e.symm.continuous⟩ : C(T, G)).comp g
  refine ⟨n, K, fG, gG, ⟨{
    toFun := fun z => e.symm (H (z.1, e z.2))
    continuous_toFun := e.symm.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    change e.symm (H (0, e x)) = e.symm (g (f (e x)))
    rw [H.apply_zero]
    rfl
  · intro x
    change e.symm (H (1, e x)) = x
    rw [H.apply_one]
    exact e.symm_apply_apply x

end BanachIsometric
