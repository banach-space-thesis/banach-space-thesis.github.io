import BanachIsometric.VectorChainHomotopy

/-! A chain map acts on the actual vector-space cycles/boundaries quotient.
These are the canonical maps of quotient classes, independently of the
linear sections used to construct the chain contractions. -/

noncomputable section
universe u
namespace BanachIsometric.VectorChainSplitting

open CategoryTheory HomologicalComplex

variable {K : Type*} [Field K]
  {C D E : ℕ → ModuleCat.{u} K}
  {d : ∀ n, C (n + 1) →ₗ[K] C n} {e : ∀ n, D (n + 1) →ₗ[K] D n}
  {b : ∀ n, E (n + 1) →ₗ[K] E n}
  {hd : ∀ n, (d n).comp (d (n + 1)) = 0}
  {he : ∀ n, (e n).comp (e (n + 1)) = 0}
  {hb : ∀ n, (b n).comp (b (n + 1)) = 0}

theorem chainMap_boundary_apply (f : chainComplex C d hd ⟶ chainComplex D e he)
    (n : ℕ) (x : C (n + 1)) :
    e n ((f.f (n + 1)).hom x) = (f.f n).hom (d n x) := by
  have h := f.comm (n + 1) n
  rw [chainComplex_d, chainComplex_d] at h
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) x

def chainCyclesMap (f : chainComplex C d hd ⟶ chainComplex D e he) (n : ℕ) :
    cycles C d n →ₗ[K] cycles D e n :=
  ((f.f n).hom.comp (cycles C d n).subtype).codRestrict (cycles D e n) (by
    intro z
    cases n with
    | zero => trivial
    | succ n =>
      change e n ((f.f (n + 1)).hom z.val) = 0
      rw [chainMap_boundary_apply f n, show d n z.val = 0 from z.property, map_zero])

def chainHomologyMap (f : chainComplex C d hd ⟶ chainComplex D e he) (n : ℕ) :
    Homology C d hd n →ₗ[K] Homology D e he n :=
  (boundaries C d hd n).mapQ (boundaries D e he n) (chainCyclesMap f n) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨(f.f (n + 1)).hom x, ?_⟩
    apply Subtype.ext
    exact chainMap_boundary_apply f n x)

@[simp] theorem chainHomologyMap_mk (f : chainComplex C d hd ⟶ chainComplex D e he)
    (n : ℕ) (c : cycles C d n) :
    chainHomologyMap f n (Submodule.Quotient.mk c) = Submodule.Quotient.mk (chainCyclesMap f n c) :=
  rfl

theorem chainHomologyMap_projection_cycle (f : chainComplex C d hd ⟶ chainComplex D e he)
    (n : ℕ) (c : cycles C d n) :
    chainHomologyMap f n (homologyProjection C d hd n c.val) =
      homologyProjection D e he n ((f.f n).hom c.val) := by
  change chainHomologyMap f n ((boundaries C d hd n).mkQ (cycleProjection C d hd n c.val)) =
    (boundaries D e he n).mkQ (cycleProjection D e he n ((chainCyclesMap f n c).val))
  rw [cycleProjection_cycle, cycleProjection_cycle]
  rfl

theorem chainHomologyMap_comp
    (f : chainComplex C d hd ⟶ chainComplex D e he)
    (g : chainComplex D e he ⟶ chainComplex E b hb) (n : ℕ) :
    chainHomologyMap (f ≫ g) n = (chainHomologyMap g n).comp (chainHomologyMap f n) := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H c => rfl

theorem chainHomologyMap_id (n : ℕ) :
    chainHomologyMap (𝟙 (chainComplex C d hd)) n = LinearMap.id := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H c => rfl

end BanachIsometric.VectorChainSplitting
