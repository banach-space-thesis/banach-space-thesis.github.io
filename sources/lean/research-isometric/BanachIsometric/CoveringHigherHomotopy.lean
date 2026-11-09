import BanachIsometric.SphereRepetition
import BanachIsometric.SphereCovering

/-! An actual covering map induces an actual group isomorphism on the
pinned Mathlib higher homotopy groups in degrees at least two. Surjectivity
uses the proved simple connectivity of the literal metric sphere and the
proved cube quotient comparison. Injectivity lifts actual homotopies
relative to the cube boundary. No higher homotopy finiteness is assumed. -/

noncomputable section
namespace BanachIsometric
open SphereGenerator
open scoped Topology Topology.Homotopy unitInterval

variable {N E B : Type*} [DecidableEq N] [Nonempty N]
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} (hp : IsCoveringMap p) (e₀ : E)

def coveringHomotopyMap : HomotopyGroup N E e₀ →* HomotopyGroup N B (p e₀) where
  toFun := Quotient.map' (mapGenLoop ⟨p, hp.continuous⟩ rfl)
    (fun _ _ h => h.comp_continuousMap ⟨p, hp.continuous⟩)
  map_one' := by
    change genLoopClass (mapGenLoop ⟨p, hp.continuous⟩ rfl GenLoop.const) = _
    rw [mapGenLoop_const]
    rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h α =>
      induction b using Quotient.inductionOn with
      | h β =>
        let Φ : HomotopyGroup N E e₀ → HomotopyGroup N B (p e₀) :=
          Quotient.map' (mapGenLoop ⟨p, hp.continuous⟩ rfl)
            (fun _ _ h => h.comp_continuousMap ⟨p, hp.continuous⟩)
        change Φ (genLoopClass α * genLoopClass β) = Φ (genLoopClass α) * Φ (genLoopClass β)
        have hmul : genLoopClass α * genLoopClass β =
            genLoopClass (GenLoop.transAt (Classical.arbitrary N) β α) := HomotopyGroup.mul_spec
        rw [hmul]
        change genLoopClass (mapGenLoop ⟨p, hp.continuous⟩ rfl
          (GenLoop.transAt (Classical.arbitrary N) β α)) =
          genLoopClass (mapGenLoop ⟨p, hp.continuous⟩ rfl α) *
            genLoopClass (mapGenLoop ⟨p, hp.continuous⟩ rfl β)
        rw [mapGenLoop_transAt]
        exact (HomotopyGroup.mul_spec (i := Classical.arbitrary N)).symm

theorem coveringHomotopyMap_injective : Function.Injective (coveringHomotopyMap (N := N) hp e₀) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h α =>
    induction b using Quotient.inductionOn with
    | h β =>
      intro hab
      apply Quotient.sound
      have he : ∃ u ∈ Cube.boundary N, α.1 u = β.1 u := by
        let u : N → unitInterval := fun _ => 0
        have hu : u ∈ Cube.boundary N := ⟨Classical.arbitrary N, Or.inl rfl⟩
        exact ⟨u, hu, (α.property u hu).trans (β.property u hu).symm⟩
      exact (hp.homotopicRel_iff_comp he).mpr (Quotient.exact hab)

theorem coveringHomotopyMap_surjective (n : ℕ) :
    Function.Surjective (coveringHomotopyMap (N := Fin (n + 2)) hp e₀) := by
  letI := simplyConnectedSpace_euclidean_sphere (n + 2) (by omega)
  letI := locPathConnectedSpace_euclidean_sphere (n + 2)
  intro a
  induction a using Quotient.inductionOn with
  | h α =>
    let f := targetGenLoopSphereMap (n + 1) α
    have hf : f (sphereBasepoint (n + 2)) = p e₀ := targetGenLoopSphereMap_basepoint (n + 1) α
    obtain ⟨F, hF, _⟩ := hp.existsUnique_continuousMap_lifts f (sphereBasepoint (n + 2)) e₀ hf.symm
    let β := sphereTargetMapGenLoop (n + 2) F hF.1
    have hβ : mapGenLoop ⟨p, hp.continuous⟩ rfl β = α := by
      ext u
      change p (F (cubeToSphere (n + 2) u)) = α u
      calc
        _ = f (cubeToSphere (n + 2) u) := congrFun hF.2 _
        _ = α u := congrArg (fun g : C((Fin (n + 2) → unitInterval), B) => g u)
          (targetGenLoopSphereMap_comp_cubeToSphere (n + 1) α)
    refine ⟨genLoopClass β, ?_⟩
    change genLoopClass (mapGenLoop ⟨p, hp.continuous⟩ rfl β) = genLoopClass α
    rw [hβ]

def coveringHigherHomotopyEquiv (n : ℕ) :
    HomotopyGroup (Fin (n + 2)) E e₀ ≃* HomotopyGroup (Fin (n + 2)) B (p e₀) :=
  MulEquiv.ofBijective (coveringHomotopyMap hp e₀)
    ⟨coveringHomotopyMap_injective hp e₀, coveringHomotopyMap_surjective hp e₀ n⟩

end BanachIsometric
