module

public import RiemannMasullo.ForMathlib.RingTheory.Etale.IsDomainLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Smooth curves over a field are locally integral

* `RiemannMasullo.isDomain_stalk_of_smoothOfRelativeDimension_one`: the local rings of a scheme
  smooth of relative dimension one over a field are domains (étale coordinates over the affine
  line, `RiemannMasullo.isDomain_localization_of_etale`).
* `RiemannMasullo.irreducibleSpace_of_isDomain_stalk`: a connected noetherian scheme with domain
  local rings is irreducible.
* `RiemannMasullo.isIntegral_of_smoothOfRelativeDimension_one`: hence a connected quasi-compact
  smooth curve over a field is integral. Applied after base change to an algebraic closure, this
  turns geometric connectedness into geometric integrality.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace RiemannMasullo

theorem isPrincipalIdealRing_mvPolynomial_fin_one {R : Type*} [CommRing R] (hR : IsField R) :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) R) := by
  let := hR.toField
  exact IsPrincipalIdealRing.of_surjective
    ((MvPolynomial.finSuccEquiv R 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)))).symm.toRingHom
    (AlgEquiv.surjective _)

/-- The local rings of a scheme smooth of relative dimension one over a field are domains. -/
theorem isDomain_stalk_of_smoothOfRelativeDimension_one {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] (y : Y) :
    IsDomain (Y.presheaf.stalk y) := by
  obtain ⟨U, hU, V, hV, hy, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) y
  have hUtop : U = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    rw [Subsingleton.elim z (f y)]
    exact e hy
  subst hUtop
  let φ : Γ(Spec (.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hfield : IsField Γ(Spec (.of K), ⊤) := φ.toMulEquiv.isField (Field.toIsField K)
  have : IsDomain Γ(Spec (.of K), ⊤) := hfield.isDomain
  have : IsPrincipalIdealRing (MvPolynomial (Fin 1) Γ(Spec (.of K), ⊤)) :=
    isPrincipalIdealRing_mvPolynomial_fin_one hfield
  obtain ⟨g, -, hg⟩ := RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial hf
  algebraize [g]
  set q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have hdom := isDomain_localization_of_etale (R := MvPolynomial (Fin 1) Γ(Spec (.of K), ⊤))
    (B := Γ(Y, V)) q
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨y, hy⟩
  let eq := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (Y.presheaf.stalk y)
  exact eq.toMulEquiv.isDomain_iff.1 hdom


/-- A connected noetherian scheme whose local rings are domains is irreducible: through each
point passes a single irreducible component (its generic point is the image of the generic point
of the local ring), so the components are disjoint, hence open, hence there is only one. -/
theorem irreducibleSpace_of_isDomain_stalk {Y : Scheme.{u}} [ConnectedSpace Y]
    [TopologicalSpace.NoetherianSpace Y] (h : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) :
    IrreducibleSpace Y := by
  -- the generic point of the local ring at `y`
  have hξ : ∀ y : Y, ∃ ξ : Y, ∀ x : Y, x ⤳ y → ξ ⤳ x := by
    intro y
    have := h y
    let P₀ : Spec (Y.presheaf.stalk y) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨Y.fromSpecStalk y P₀, fun x hx => ?_⟩
    have hmem : x ∈ Set.range (Y.fromSpecStalk y) := by
      rw [Scheme.range_fromSpecStalk]; exact hx
    obtain ⟨P, rfl⟩ := hmem
    have hP : P₀ ⤳ P := (PrimeSpectrum.le_iff_specializes P₀ P).1 bot_le
    exact hP.map (Y.fromSpecStalk y).continuous
  choose ξ hξ using hξ
  -- a point lies in a single irreducible component
  have huniq : ∀ Z ∈ irreducibleComponents Y, ∀ y ∈ Z, Z = closure {ξ y} := by
    intro Z hZ y hy
    have hirr : IsIrreducible Z := hZ.1
    have hgen := hirr.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents Z hZ).closure_eq] at hgen
    have h1 : hirr.genericPoint ⤳ y := hgen.specializes hy
    have h2 : ξ y ⤳ hirr.genericPoint := hξ y _ h1
    have h3 : Z ⊆ closure {ξ y} := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 h2))
        isClosed_closure
    exact h3.antisymm (hZ.2 isIrreducible_singleton.closure h3)
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  set Z := irreducibleComponent y₀
  have hZ : Z ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y₀
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hopen : IsOpen Z := by
    have : Z = (⋃₀ (irreducibleComponents Y \ {Z}))ᶜ := by
      ext x
      constructor
      · intro hx hx'
        obtain ⟨Z', ⟨hZ', hne⟩, hxZ'⟩ := hx'
        exact hne ((huniq Z' hZ' x hxZ').trans (huniq Z hZ x hx).symm)
      · intro hx
        have : x ∈ ⋃₀ irreducibleComponents Y := by
          rw [sUnion_irreducibleComponents]; trivial
        obtain ⟨Z', hZ', hxZ'⟩ := this
        by_cases hZZ : Z' = Z
        · exact hZZ ▸ hxZ'
        · exact absurd ⟨Z', ⟨hZ', hZZ⟩, hxZ'⟩ hx
    rw [this, isOpen_compl_iff]
    exact (hfin.sdiff).isClosed_sUnion fun Z' hZ' => isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have hclopen : IsClopen Z := ⟨isClosed_of_mem_irreducibleComponents Z hZ, hopen⟩
  have huniv : Z = Set.univ := hclopen.eq_univ ⟨y₀, mem_irreducibleComponent⟩
  have hirr : IsIrreducible (Set.univ : Set Y) := huniv ▸ hZ.1
  exact irreducibleSpace_def Y |>.2 hirr


/-- A connected quasi-compact scheme smooth of relative dimension one over a field is integral. -/
theorem isIntegral_of_smoothOfRelativeDimension_one {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] [QuasiCompact f] [ConnectedSpace Y] :
    IsIntegral Y := by
  have hdom := isDomain_stalk_of_smoothOfRelativeDimension_one f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have : IrreducibleSpace Y := irreducibleSpace_of_isDomain_stalk hdom
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have := hdom y; infer_instance
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end RiemannMasullo
