module

public import RiemannMasullo.ForMathlib.AlgebraicGeometry.SmoothCurve
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Points of curves over a field

For a scheme `X` over `Spec k`:
* `RiemannMasullo.sectionsAlgebra`: the `k`-algebra structure on `Γ(X, U)`;
* `RiemannMasullo.isDomain_tensor_of_isIntegral_pullback`: if `X` and its base change to `L` are
  integral, `Γ(X, U) ⊗_k L` is a domain for every nonempty affine open `U`;
* `RiemannMasullo.card_points_affineOpen`: the `K`-points of `X` over `k` lying in an affine open
  `V` are the `k`-algebra maps `Γ(X, V) → K`;
* `RiemannMasullo.finite_compl_of_ringKrullDim_le_one`: on an integral curve (affine charts of
  dimension `≤ 1`), nonempty opens have finite complements.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace RiemannMasullo

/-- The `k`-algebra structure on the sections of `X` over `U`, for a scheme `X` over `Spec k`. -/
noncomputable abbrev sectionsAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

theorem SpecMap_sectionsAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f := by
  let := sectionsAlgebra f U
  have : CommRingCat.ofHom (algebraMap k Γ(X, U)) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top := rfl
  rw [this, Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- If the base change of `X` to `L` is integral, then for every nonempty affine open `U` of the
integral scheme `X`, `Γ(X, U) ⊗[k] L` is a domain. -/
theorem isDomain_tensor_of_isIntegral_pullback {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))))] :
    letI := sectionsAlgebra f U
    IsDomain (Γ(X, U) ⊗[k] L) := by
  let := sectionsAlgebra f U
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have h1 := SpecMap_sectionsAlgebra f hU
  have hnt : Nontrivial (Γ(X, U) ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k Γ(X, U) L
      (algebraMap k Γ(X, U)).injective (algebraMap k L).injective
  let e : pullback (hU.fromSpec ≫ f) g ≅ Spec (.of (Γ(X, U) ⊗[k] L)) :=
    (pullback.congrHom h1.symm rfl).trans (pullbackSpecIso k Γ(X, U) L)
  let j : pullback (hU.fromSpec ≫ f) g ⟶ pullback f g :=
    (pullbackRightPullbackFstIso f g hU.fromSpec).inv ≫ pullback.snd hU.fromSpec (pullback.fst f g)
  have : IsOpenImmersion j := inferInstance
  have : Nonempty (Spec (.of (Γ(X, U) ⊗[k] L))) := inferInstance
  have : Nonempty ↥(pullback (hU.fromSpec ≫ f) g) :=
    ⟨e.inv.base (Classical.arbitrary ↥(Spec (.of (Γ(X, U) ⊗[k] L))))⟩
  have : IsIntegral (pullback (hU.fromSpec ≫ f) g) := isIntegral_of_isOpenImmersion j
  have : IsIntegral (Spec (.of (Γ(X, U) ⊗[k] L))) := IsIntegral.of_isIso e.hom
  exact (affine_isIntegral_iff _).1 this


/-- The points of `X` over `k` with values in a field `K` that land in an affine open `V` are the
`k`-algebra homomorphisms `Γ(X, V) → K`. -/
theorem card_points_affineOpen {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {V : X.Opens} (hV : IsAffineOpen V) (K : Type u) [Field K] [Algebra k K] :
    letI := sectionsAlgebra f V
    Nat.card {p : Spec (.of K) ⟶ X //
        p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
        p (IsLocalRing.closedPoint K) ∈ V} = Nat.card (Γ(X, V) →ₐ[k] K) := by
  let := sectionsAlgebra f V
  have hSpec := SpecMap_sectionsAlgebra f hV
  let Fwd : (Γ(X, V) →ₐ[k] K) → {p : Spec (.of K) ⟶ X //
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
      p (IsLocalRing.closedPoint K) ∈ V} := fun φ =>
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, by
      rw [Category.assoc, ← hSpec, ← Spec.map_comp]
      congr 1
      ext a
      simp, by
      have : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec)
          (IsLocalRing.closedPoint K) ∈ Set.range hV.fromSpec :=
        ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [hV.range_fromSpec] at this⟩
  have hinj : Function.Injective Fwd := by
    intro φ ψ h
    have h1 := congrArg Subtype.val h
    simp only [Fwd] at h1
    have h2 := Spec.map_injective ((cancel_mono hV.fromSpec).1 h1)
    ext a
    exact congrArg (fun g : CommRingCat.of Γ(X, V) ⟶ CommRingCat.of K => g a) h2
  have hsurj : Function.Surjective Fwd := by
    rintro ⟨p, hp, hpV⟩
    have hrange : Set.range p ⊆ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
      exact hpV
    set p' := IsOpenImmersion.lift hV.fromSpec p hrange
    have hp' : p' ≫ hV.fromSpec = p := IsOpenImmersion.lift_fac _ _ _
    set φ := Spec.preimage p'
    have hφ : Spec.map φ = p' := Spec.map_preimage p'
    have hk : CommRingCat.ofHom (algebraMap k Γ(X, V)) ≫ φ =
        CommRingCat.ofHom (algebraMap k K) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, hSpec, ← Category.assoc, hp', hp]
    refine ⟨⟨φ.hom, fun a => ?_⟩, ?_⟩
    · exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of K => g a) hk
    · apply Subtype.ext
      simp only [Fwd]
      rw [← hp']
      congr 1
  exact (Nat.card_congr (Equiv.ofBijective Fwd ⟨hinj, hsurj⟩)).symm


/-- In an integral quasi-compact locally noetherian scheme covered by affine opens whose rings have
Krull dimension at most one, every nonempty open set has finite complement. -/
theorem finite_compl_of_ringKrullDim_le_one {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X]
    (hdim : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ ringKrullDim Γ(X, W) ≤ 1)
    {V : X.Opens} (hV : (V : Set X).Nonempty) : ((V : Set X)ᶜ).Finite := by
  have : IsNoetherian X := {}
  set η := genericPoint X
  -- every point other than the generic point is closed
  have hclosed : ∀ x : X, x ≠ η → IsClosed ({x} : Set X) := by
    intro x hx
    by_contra hnc
    have : closure ({x} : Set X) ≠ {x} := fun h => hnc (h ▸ isClosed_closure)
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ closure ({x} : Set X), z ≠ x := by
      by_contra h
      push Not at h
      exact this (Set.Subset.antisymm (fun z hz => h z hz) subset_closure)
    have hxz : x ⤳ z := specializes_iff_mem_closure.2 hz
    obtain ⟨W, hW, hzW, hWdim⟩ := hdim z
    have hxW : x ∈ W := hxz.mem_open W.isOpen hzW
    have hηW : η ∈ W := (genericPoint_specializes x).mem_open W.isOpen hxW
    have : Nonempty W := ⟨⟨z, hzW⟩⟩
    have hdom : IsDomain Γ(X, W) := inferInstance
    have : Ring.KrullDimLE 1 Γ(X, W) := (Ring.krullDimLE_iff).2 hWdim
    -- specialization inside `W`
    have hspec : ∀ a b : X, (ha : a ∈ W) → (hb : b ∈ W) → a ⤳ b →
        (hW.primeIdealOf ⟨a, ha⟩).asIdeal ≤ (hW.primeIdealOf ⟨b, hb⟩).asIdeal := by
      intro a b ha hb hab
      have h1 : (⟨a, ha⟩ : W) ⤳ ⟨b, hb⟩ :=
        (W.ι.isOpenEmbedding.isInducing.specializes_iff).1 (by simpa using hab)
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (h1.map hW.isoSpec.hom.continuous)
    have hinj : ∀ a b : X, (ha : a ∈ W) → (hb : b ∈ W) →
        hW.primeIdealOf ⟨a, ha⟩ = hW.primeIdealOf ⟨b, hb⟩ → a = b := by
      intro a b ha hb h
      have := congrArg hW.fromSpec h
      rwa [hW.fromSpec_primeIdealOf, hW.fromSpec_primeIdealOf] at this
    have hle := hspec x z hxW hzW hxz
    by_cases hbot : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal = ⊥
    · have h2 := hspec η x hηW hxW (genericPoint_specializes x)
      rw [hbot, le_bot_iff] at h2
      exact hx (hinj η x hηW hxW (PrimeSpectrum.ext (h2.trans hbot.symm))).symm
    · have hmax := (hW.primeIdealOf ⟨x, hxW⟩).isPrime.isMaximal_of_ne_bot hbot
      have := hmax.eq_of_le (hW.primeIdealOf ⟨z, hzW⟩).isPrime.ne_top hle
      exact hzx (hinj x z hxW hzW (PrimeSpectrum.ext this)).symm
  -- the generic point lies in `V`
  have hηV : η ∈ V := by
    obtain ⟨v, hv⟩ := hV
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 ⟨v, trivial, hv⟩
  -- a closed set of closed points in a noetherian space is finite
  obtain ⟨S, hSfin, hSclosed, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (V.isOpen.isClosed_compl)
  rw [hSeq]
  refine hSfin.sUnion fun t ht => ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint_closure
  rw [(hSclosed t ht).closure_eq] at hgen
  set z := (hSirr t ht).genericPoint
  have hzt : z ∈ t := hgen.mem
  have hzV : z ∉ V := by
    have : z ∈ ⋃₀ S := ⟨t, ht, hzt⟩
    rw [← hSeq] at this
    exact this
  have hzη : z ≠ η := fun h => hzV (h ▸ hηV)
  have : t = {z} := by
    rw [← hgen.def, (hclosed z hzη).closure_eq]
  rw [this]
  exact Set.finite_singleton z

end RiemannMasullo
