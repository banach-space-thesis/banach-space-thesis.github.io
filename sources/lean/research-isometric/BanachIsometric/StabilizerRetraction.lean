import BanachIsometric.GenericUnitaryOrbit
import BanachIsometric.TensorOrbitSection
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Equivariant retraction onto an actual stabilizer

The existing orbit section gives a simple alternative to a tubular
neighbourhood retraction inside the compact orthogonal group. If `q(w)·v=w`,
then `r(g)=g*q(g⁻¹·v)` fixes `v`. This formula is exactly equivariant under
left multiplication by the stabilizer. It is not a choice of nearest points.
-/

namespace BanachIsometric

open Set
open scoped Topology Matrix.Norms.Operator

variable {G W : Type*} [Group G] [MulAction G W]

def stabilizerRetraction (v : W) (q : W → G) (g : G) : G := g * q (g⁻¹ • v)

theorem stabilizerRetraction_smul_eq (v : W) (q : W → G) {g : G}
    (hq : q (g⁻¹ • v) • v = g⁻¹ • v) : stabilizerRetraction v q g • v = v := by
  rw [stabilizerRetraction, mul_smul, hq, smul_inv_smul]

theorem stabilizerRetraction_fixed (v : W) (q : W → G) (hq : q v = 1)
    {h : G} (hh : h ∈ MulAction.stabilizer G v) : stabilizerRetraction v q h = h := by
  have hinv : h⁻¹ • v = v := (MulAction.mem_stabilizer_iff).mp
    ((MulAction.stabilizer G v).inv_mem hh)
  rw [stabilizerRetraction, hinv, hq, mul_one]

theorem stabilizerRetraction_equivariant (v : W) (q : W → G)
    {h : G} (hh : h ∈ MulAction.stabilizer G v) (g : G) :
    stabilizerRetraction v q (h * g) = h * stabilizerRetraction v q g := by
  have hinv : h⁻¹ • v = v := (MulAction.mem_stabilizer_iff).mp
    ((MulAction.stabilizer G v).inv_mem hh)
  simp only [stabilizerRetraction, mul_inv_rev, mul_smul, hinv, mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace W] [ContinuousSMul G W]

/-- An actual orbit section yields an equivariant continuous retraction on an
open invariant neighbourhood of the actual stabilizer. Applied to the moment
representation, the orbit-section premise is supplied by our proved slice
theorem. Compactness or a Lie-subgroup theorem is not a hidden field here. -/
theorem exists_continuous_stabilizer_retraction_of_orbit_section
    (v : W) (q : W → G) (N : Set W) (hN : IsOpen N) (hv : v ∈ N)
    (hq : ContinuousOn q N) (hqv : q v = 1)
    (hsect : ∀ w ∈ N, (∃ g : G, g • v = w) → q w • v = w) :
    ∃ U : Set G, ∃ r : G → G,
      IsOpen U ∧ (MulAction.stabilizer G v : Set G) ⊆ U ∧ ContinuousOn r U ∧
      (∀ g ∈ U, r g ∈ MulAction.stabilizer G v) ∧
      (∀ h ∈ MulAction.stabilizer G v, r h = h) ∧
      (∀ h ∈ MulAction.stabilizer G v, ∀ g, r (h * g) = h * r g) ∧
      (∀ h ∈ MulAction.stabilizer G v, ∀ g ∈ U, h * g ∈ U) := by
  let c : G → W := fun g => g⁻¹ • v
  have hc : Continuous c := continuous_inv.smul continuous_const
  let U : Set G := c ⁻¹' N
  refine ⟨U, stabilizerRetraction v q, hN.preimage hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    have hinv : h⁻¹ • v = v := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer G v).inv_mem hh)
    change h⁻¹ • v ∈ N
    rwa [hinv]
  · exact continuous_id.continuousOn.mul (hq.comp hc.continuousOn (fun _ hg => hg))
  · intro g hg
    apply MulAction.mem_stabilizer_iff.mpr
    exact stabilizerRetraction_smul_eq v q (hsect (c g) hg ⟨g⁻¹, rfl⟩)
  · intro h hh
    exact stabilizerRetraction_fixed v q hqv hh
  · intro h hh g
    exact stabilizerRetraction_equivariant v q hh g
  · intro h hh g hg
    have hinv : h⁻¹ • v = v := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer G v).inv_mem hh)
    change (h * g)⁻¹ • v ∈ N
    simpa only [mul_inv_rev, mul_smul, hinv] using hg

/-- Specialisation to the genuine finite tensor representation. The local
orbit section is constructed by the proved slice theorem, not assumed. -/
theorem exists_continuous_tensorTuple_stabilizer_retraction (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    ∃ U : Set (Matrix.orthogonalGroup (Fin m) ℝ),
      ∃ r : Matrix.orthogonalGroup (Fin m) ℝ → Matrix.orthogonalGroup (Fin m) ℝ,
      IsOpen U ∧ (MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M : Set _) ⊆ U ∧
      ContinuousOn r U ∧
      (∀ g ∈ U, r g ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M) ∧
      (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M, r h = h) ∧
      (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M,
        ∀ g, r (h * g) = h * r g) ∧
      (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M,
        ∀ g ∈ U, h * g ∈ U) := by
  obtain ⟨q, N, hN, L, hqv, hqL, hqS⟩ := exists_lipschitz_tensorTuple_orbit_section m I M
  obtain ⟨N', hN'sub, hN'open, hMN'⟩ := mem_nhds_iff.mp hN
  apply exists_continuous_stabilizer_retraction_of_orbit_section M q N' hN'open hMN'
    (hqL.continuousOn.mono hN'sub) hqv
  intro w hw horbit
  exact hqS w (hN'sub hw) horbit

end BanachIsometric
