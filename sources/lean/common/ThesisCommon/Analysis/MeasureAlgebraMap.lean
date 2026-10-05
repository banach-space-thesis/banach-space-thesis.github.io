import ThesisCommon.Analysis.MeasureAlgebra
import Mathlib.MeasureTheory.Measure.Map

/-! Pullback isomorphisms of actual measure algebras. Surjectivity requires
that the source sigma algebra be the pullback sigma algebra; no pointwise
injectivity, measurable image, or separation-of-points assumption is needed. -/
noncomputable section
open Set MeasureTheory Filter
namespace ThesisCommon
namespace MeasureAlgebra
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable (μ : Measure X) (f : X → Y) (hf : Measurable f)

def comap : MeasureAlgebra (μ.map f) → MeasureAlgebra μ :=
  Quotient.map (fun A : {A : Set Y // MeasurableSet A} => ⟨f ⁻¹' A.val, hf A.property⟩)
    (fun _ _ h => ae_of_ae_map hf.aemeasurable h)

@[simp] theorem comap_mk (A : Set Y) (hA : MeasurableSet A) :
    comap μ f hf (mk (μ.map f) A hA) = mk μ (f ⁻¹' A) (hf hA) := rfl

theorem comap_injective : Function.Injective (comap μ f hf) := by
  intro a b
  induction a using Quotient.inductionOn with | _ A => ?_
  induction b using Quotient.inductionOn with | _ B => ?_
  intro h
  apply (mk_eq_mk A.property B.property).mpr
  have hab := (mk_eq_mk (hf A.property) (hf B.property)).mp h
  rw [← measure_symmDiff_eq_zero_iff] at hab ⊢
  rw [Measure.map_apply hf (A.property.symmDiff B.property)]
  simpa only [preimage_symmDiff] using hab

theorem comap_surjective (hgen : mY.comap f = mX) : Function.Surjective (comap μ f hf) := by
  intro a
  induction a using Quotient.inductionOn with | _ A => ?_
  have hA : MeasurableSet[mY.comap f] A.val := hgen.symm ▸ A.property
  obtain ⟨B, hB, hBA⟩ := (MeasurableSpace.measurableSet_comap).mp hA
  refine ⟨mk (μ.map f) B hB, ?_⟩
  simp only [comap_mk]
  apply (mk_eq_mk _ _).mpr
  exact Filter.Eventually.of_forall fun x => congrArg (fun A : Set X => x ∈ A) hBA

theorem comap_compl (a : MeasureAlgebra (μ.map f)) :
    comap μ f hf (compl a) = compl (comap μ f hf a) := by
  induction a using Quotient.inductionOn with | _ A => ?_
  change comap μ f hf (compl (mk (μ.map f) A.val A.property)) =
    compl (comap μ f hf (mk (μ.map f) A.val A.property))
  simp only [compl_mk, comap_mk]
  rfl

theorem comap_iUnion {ι : Type*} [Countable ι] (a : ι → MeasureAlgebra (μ.map f)) :
    comap μ f hf (iUnion a) = iUnion (fun i => comap μ f hf (a i)) := by
  have ha : a = fun i => mk (μ.map f) (a i).representative.val (a i).representative.property := by
    funext i
    exact (mk_representative _).symm
  rw [ha]
  simp only [iUnion_mk, comap_mk]
  simp only [preimage_iUnion]

theorem measure_comap (a : MeasureAlgebra (μ.map f)) :
    (comap μ f hf a).measure = a.measure := by
  induction a using Quotient.inductionOn with | _ A => ?_
  change (comap μ f hf (mk (μ.map f) A.val A.property)).measure =
    (mk (μ.map f) A.val A.property).measure
  simp only [comap_mk, measure_mk, Measure.map_apply hf A.property]

end MeasureAlgebra
namespace MeasureAlgebraIso
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

/-- The inverse is again a measure-preserving sigma-algebra isomorphism. -/
def symm (Φ : MeasureAlgebraIso μ ν) : MeasureAlgebraIso ν μ where
  toEquiv := Φ.toEquiv.symm
  map_compl a := by
    apply Φ.toEquiv.injective
    simp only [Equiv.apply_symm_apply, Φ.map_compl]
  map_iUnion ι _ a := by
    apply Φ.toEquiv.injective
    simp only [Equiv.apply_symm_apply, Φ.map_iUnion]
  measure_eq a := by
    have h := Φ.measure_eq (Φ.toEquiv.symm a)
    simpa using h.symm

/-- A measurable coding that generates the whole source sigma algebra induces
a genuine isomorphism of measure algebras with its pushforward measure. -/
def ofComapEq (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (hgen : mY.comap f = mX) : MeasureAlgebraIso (μ.map f) μ where
  toEquiv := Equiv.ofBijective (MeasureAlgebra.comap μ f hf)
    ⟨MeasureAlgebra.comap_injective μ f hf, MeasureAlgebra.comap_surjective μ f hf hgen⟩
  map_compl := MeasureAlgebra.comap_compl μ f hf
  map_iUnion := fun _ _ => MeasureAlgebra.comap_iUnion μ f hf
  measure_eq := MeasureAlgebra.measure_comap μ f hf

end MeasureAlgebraIso
end ThesisCommon
