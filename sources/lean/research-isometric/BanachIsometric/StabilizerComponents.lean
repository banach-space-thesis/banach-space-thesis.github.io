import BanachIsometric.GenericUnitaryOrbit
import BanachIsometric.TensorGroupAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.PathConnected

/-!
# Finitely many components of actual finite moment stabilisers

The local exponential slice proves that every sufficiently small stabiliser
element is an exponential of a vector in the actual orbit-derivative kernel.
Its exponential path stays in the stabiliser. The identity path component is
therefore open, equals the connected component, and has finite index whenever
the ambient unitary group is compact.

This proves the finite-component ingredient in Lemma 4.3 directly, without a
closed-subgroup Lie theorem. It does not assert finiteness of higher homotopy
groups or bundle annihilation.
-/

noncomputable section

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal

variable {A W : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [StarRing A] [StarModule ℝ A] [ContinuousStar A]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual unitary stabiliser of a vector under the supplied linear
representation, with the topology inherited from the original algebra. -/
def unitaryRepresentationStabilizer (ρ : A →* Module.End ℝ W) (v : W) :
    Subgroup (unitary A) where
  carrier := {R | ρ (R : A) v = v}
  one_mem' := by change ρ (1 : A) v = v; rw [map_one]; rfl
  mul_mem' := by
    intro R S hR hS
    change ρ ((R : A) * (S : A)) v = v
    rw [map_mul]
    change ρ (R : A) (ρ (S : A) v) = v
    rw [hS, hR]
  inv_mem' := by
    intro R hR
    have hprod : ρ (R⁻¹ : unitary A) (ρ (R : A) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      have hunit : ((R⁻¹ : unitary A) : A) * (R : A) = 1 :=
        congrArg Subtype.val (inv_mul_cancel R)
      rw [hunit, map_one]
      rfl
    rwa [hR] at hprod

omit [NormedAlgebra ℝ A] [CompleteSpace A] [StarModule ℝ A] [ContinuousStar A] in
theorem isClosed_unitaryRepresentationStabilizer
    (ρ : A →* Module.End ℝ W) (v : W)
    (hρ : Continuous (fun R : A => ρ R v)) :
    IsClosed (unitaryRepresentationStabilizer ρ v : Set (unitary A)) :=
  isClosed_eq (hρ.comp continuous_subtype_val) continuous_const

section LocalComponents

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ W]

/-- Every stabiliser element sufficiently near the identity admits an actual
path to the identity inside that same stabiliser. -/
theorem unitaryRepresentationStabilizer_eventually_joined
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    ∀ᶠ R : unitaryRepresentationStabilizer ρ v in 𝓝 1,
      Joined (1 : unitaryRepresentationStabilizer ρ v) R := by
  classical
  let H := unitaryRepresentationStabilizer ρ v
  let F : A → W := fun X => ρ (NormedSpace.exp ℝ X) v
  have hF : HasStrictFDerivAt F (fderiv ℝ F 0) 0 := by
    have hO : HasStrictFDerivAt (fun R : A => ρ R v)
        (fderiv ℝ (fun R : A => ρ R v) 1) (NormedSpace.exp ℝ (0 : A)) := by
      simpa only [NormedSpace.exp_zero] using
        (horbit.hasStrictFDerivAt (x := (1 : A)) (by simp))
    have h := hO.comp (0 : A) (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A))
    change HasStrictFDerivAt F _ 0 at h
    rw [h.hasFDerivAt.fderiv]
    exact h
  let D : UnitaryOrbit.Skew A →L[ℝ] W :=
    (fderiv ℝ F 0).comp (skewAdjoint.submodule ℝ A).subtypeL
  let V : Submodule ℝ (UnitaryOrbit.Skew A) := LinearMap.ker D.toLinearMap
  obtain ⟨U, hVU⟩ := V.exists_isCompl
  have hc : IsCompl U V := hVU.symm
  let e : U → unitary A := UnitaryOrbit.exponential A U
  let DP : U →L[ℝ] W := D.comp U.subtypeL
  have hDP : HasStrictFDerivAt (fun x : U => ρ (e x : A) v) DP 0 :=
    hF.comp 0 (UnitaryOrbit.inclusion A U).hasStrictFDerivAt
  have hDinj : Function.Injective DP := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hmem : x.val - y.val ∈ U ⊓ V := by
      refine ⟨U.sub_mem x.property y.property, ?_⟩
      change D (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    rw [hc.inf_eq_bot] at hmem
    exact hmem
  obtain ⟨g, B, hB, _, _, _, hg0, _, hgInv, _⟩ :=
    exists_lipschitz_inverse_of_injective_strictDerivative
      (fun x : U => ρ (e x : A) v) DP hDP hDinj
  have he0 : ρ (e 0 : A) v = v := by
    dsimp only [e]
    rw [UnitaryOrbit.exponential_zero]
    change ρ (1 : A) v = v
    rw [map_one]
    rfl
  rw [he0] at hg0
  let z : H → U × V := fun R => SkewFactorization.coordinates A U V hc ((R : unitary A) : A)
  have hval : ContinuousAt (fun R : H => ((R : unitary A) : A)) 1 :=
    continuous_subtype_val.continuousAt.comp continuous_subtype_val.continuousAt
  have hzA : ContinuousAt (SkewFactorization.coordinates A U V hc) (1 : A) :=
    (SkewFactorization.coordinates_hasStrictFDerivAt A U V hc).continuousAt
  have hz : ContinuousAt z 1 := by
    exact hzA.comp (f := fun R : H => ((R : unitary A) : A)) hval
  have hz0 : z 1 = 0 := by simp [z]
  have hsmall : ∀ᶠ R : H in 𝓝 1, (z R).1 ∈ B := by
    apply (continuous_fst.continuousAt.comp hz).tendsto.eventually
    simpa only [Function.comp_apply, hz0, Prod.fst_zero] using hB
  have hfac : ∀ᶠ R : H in 𝓝 1,
      SkewFactorization.expProduct A U V (z R) = ((R : unitary A) : A) := by
    have h := hval.tendsto.eventually (SkewFactorization.expProduct_coordinates A U V hc)
    filter_upwards [h] with R hR
    exact hR (R : unitary A).property
  filter_upwards [hsmall, hfac] with R hRsmall hRfac
  have hY : fderiv ℝ F 0 (((z R).2 : UnitaryOrbit.Skew A) : A) = 0 := (z R).2.property
  have hfixed (t : ℝ) :
      ρ (NormedSpace.exp ℝ (t • (((z R).2 : UnitaryOrbit.Skew A) : A))) v = v :=
    representation_exp_fixed_of_fderiv_eq_zero ρ v hF.differentiableAt _ hY t
  have hOrbitX : ρ (e (z R).1 : A) v = v := by
    have hRmem : ρ (((R : unitary A) : A)) v = v := R.property
    rw [← hRfac] at hRmem
    change ρ (NormedSpace.exp ℝ (((z R).1 : UnitaryOrbit.Skew A) : A) *
      NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v = v at hRmem
    rw [map_mul] at hRmem
    change ρ (e (z R).1 : A)
      (ρ (NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v) = v at hRmem
    have hfixed1 : ρ (NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A)) v = v := by
      simpa only [one_smul] using hfixed 1
    rwa [hfixed1] at hRmem
  have hX : (z R).1 = 0 := by
    have h := hgInv (z R).1 hRsmall
    rw [hOrbitX, hg0] at h
    exact h.symm
  have hExpY : NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A) =
      ((R : unitary A) : A) := by
    change NormedSpace.exp ℝ (((z R).1 : UnitaryOrbit.Skew A) : A) *
      NormedSpace.exp ℝ (((z R).2 : UnitaryOrbit.Skew A) : A) = _ at hRfac
    rw [hX] at hRfac
    simpa only [Submodule.coe_zero, NormedSpace.exp_zero, one_mul] using hRfac
  refine ⟨{
    toFun := fun t => ⟨⟨NormedSpace.exp ℝ ((t : ℝ) •
      (((z R).2 : UnitaryOrbit.Skew A) : A)),
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ
        ((skewAdjoint.submodule ℝ A).smul_mem (t : ℝ) (z R).2.val.property)⟩,
        hfixed (t : ℝ)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (NormedSpace.exp_continuous (𝕂 := ℝ)).comp
        (continuous_subtype_val.smul continuous_const)
    source' := by apply Subtype.ext; apply Subtype.ext; simp
    target' := by
      apply Subtype.ext
      apply Subtype.ext
      change NormedSpace.exp ℝ ((1 : ℝ) • (((z R).2 : UnitaryOrbit.Skew A) : A)) = _
      simpa only [one_smul] using hExpY }⟩

theorem isOpen_unitaryRepresentationStabilizer_pathComponentOne
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    IsOpen (Subgroup.pathComponentOne (unitaryRepresentationStabilizer ρ v) :
      Set (unitaryRepresentationStabilizer ρ v)) :=
  Subgroup.isOpen_of_mem_nhds _ (unitaryRepresentationStabilizer_eventually_joined ρ v horbit)

theorem unitaryRepresentationStabilizer_connected_eq_path
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v) =
      Subgroup.pathComponentOne (unitaryRepresentationStabilizer ρ v) := by
  let H := unitaryRepresentationStabilizer ρ v
  have hopen := isOpen_unitaryRepresentationStabilizer_pathComponentOne ρ v horbit
  have hclosed := (Subgroup.pathComponentOne H).isClosed_of_isOpen hopen
  have hclopen : IsClopen (pathComponent (1 : H)) := ⟨hclosed, hopen⟩
  apply Subgroup.ext
  intro R
  change R ∈ connectedComponent (1 : H) ↔ R ∈ pathComponent (1 : H)
  constructor
  · intro hR
    exact hclopen.connectedComponent_subset (mem_pathComponent_self (1 : H)) hR
  · intro hR
    exact pathComponent_subset_component (1 : H) hR

theorem unitaryRepresentationStabilizer_connectedComponent_normal
    (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    (Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)).Normal := by
  rw [unitaryRepresentationStabilizer_connected_eq_path ρ v horbit]
  infer_instance

/-- The actual compact representation stabiliser has finitely many connected
components, proved from the exponential paths above. -/
theorem finite_unitaryRepresentationStabilizer_componentQuotient
    [CompactSpace (unitary A)] (ρ : A →* Module.End ℝ W) (v : W)
    (horbit : ContDiff ℝ ⊤ (fun R : A => ρ R v)) :
    Finite ((unitaryRepresentationStabilizer ρ v) ⧸
      Subgroup.connectedComponentOfOne (unitaryRepresentationStabilizer ρ v)) := by
  let H := unitaryRepresentationStabilizer ρ v
  letI : CompactSpace H := isCompact_iff_compactSpace.mp
    (isClosed_unitaryRepresentationStabilizer ρ v horbit.continuous).isCompact
  apply Subgroup.quotient_finite_of_isOpen
  rw [unitaryRepresentationStabilizer_connected_eq_path ρ v horbit]
  exact isOpen_unitaryRepresentationStabilizer_pathComponentOne ρ v horbit

end LocalComponents

open scoped Matrix.Norms.Operator

/-- The actual orthogonal body-automorphism subgroup has finitely many
connected components. The finite tuple and its exact stabiliser property are
constructed from the body; neither is an extra premise. -/
theorem finite_orthogonalBodyStabilizer_componentQuotient {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    Finite ((orthogonalBodyStabilizerSubgroup m S) ⧸
      Subgroup.connectedComponentOfOne (orthogonalBodyStabilizerSubgroup m S)) := by
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer μ S hS hreg h0
  have hG : orthogonalBodyStabilizerSubgroup m S =
      unitaryRepresentationStabilizer (tensorTupleLinearRepresentation m I)
        (bodyTensorTuple μ S I) := by
    apply Subgroup.ext
    intro Q
    let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv Q
    have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val := LinearMap.toMatrix'_toLin' Q.val
    simpa only [hmat] using hI e
  letI : CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := compactSpace_orthogonalGroup m
  rw [hG]
  exact finite_unitaryRepresentationStabilizer_componentQuotient
    (tensorTupleLinearRepresentation m I) (bodyTensorTuple μ S I)
    (contDiff_tensorTupleOrbit m I (bodyTensorTuple μ S I))

end BanachIsometric
