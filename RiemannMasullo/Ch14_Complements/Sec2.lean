module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.FieldTheory.Finite.Extension
import RiemannMasullo.ForMathlib.NumberTheory.WeilBound.EtaleChart
import RiemannMasullo.ForMathlib.AlgebraicGeometry.CurvePoints

/-!
# §§14.2–14.3: Global function fields and higher rank

Masullo, pp. 534–536. The Euler product (14.2.0.1) uses every closed point of
the smooth projective curve, including those above infinity for a map to the
projective line.
-/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Paper: (14.2.0.1), p. 534. The local factor at a closed point, in the
complex parameter on the covering plane. -/
noncomputable def curveZetaEulerFactor (x : closedPoints X) (s : ℂ) : ℂ :=
  (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s))⁻¹

/-- Paper: (14.2.0.1), p. 534. The zeta Euler product of a smooth projective
geometrically connected curve over a finite field multiplies the reciprocal
factors determined by the sizes of the residue fields of its closed points.
Deviation: The product is defined on `Re(s) > 1`, its half-plane of absolute
convergence. A smooth proper curve over a field is projective. -/
noncomputable def curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' x : closedPoints X, curveZetaEulerFactor x s.val

/-- The residue field of a closed point of a curve over a finite field is a finite extension
of the base field, so its cardinality is a positive power of `Nat.card k`. -/
private theorem closedPoint_residueField_card_pow (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : x ∈ closedPoints X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (X.residueField x) = Nat.card k ^ m := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed ({x} : Set X) := hx
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hclosed
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (X.fromSpecResidueField x ≫ f)
  have h2' : LocallyOfFiniteType (Spec.homEquiv.symm φ) := hφ ▸ h2
  have h3 : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp h2'
  algebraize [φ.hom]
  haveI : Algebra.FiniteType k (X.residueField x) := h3
  haveI : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  haveI : Finite (X.residueField x) := Module.finite_of_finite k (M := X.residueField x)
  have hcard : Nat.card (X.residueField x) = Nat.card k ^ Module.finrank k (X.residueField x) :=
    Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x)
  refine ⟨Module.finrank k (X.residueField x), ?_, hcard⟩
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (X.residueField x) := Fintype.ofFinite _
  have hq : 2 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hc : 2 ≤ Nat.card (X.residueField x) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hlt
  have h0 : Module.finrank k (X.residueField x) = 0 := by omega
  rw [h0, pow_zero] at hcard
  omega

section

open Polynomial

/-- A ring hom out of a finite field is determined by the image of a generator of the unit
group, which is a root of `X ^ q - X`; so there are at most `q` of them. -/
private theorem curveZetaEulerFactor_card_ringHom_finiteField_le {K F : Type*} [Field K]
    [Finite K] [Field F] :
    Nat.card (K →+* F) ≤ Nat.card K := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  set q := Fintype.card K with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  set P : F[X] := X ^ q - X with hP
  have hPdeg : P.natDegree = q := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt (by simp [hq1]), natDegree_X_pow]
  have hP0 : P ≠ 0 := fun h ↦ by
    rw [h, natDegree_zero] at hPdeg
    omega
  let e : (K →+* F) → {x : F // x ∈ P.roots.toFinset} := fun φ ↦ ⟨φ (γ : K), by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X,
      ← map_pow, hq, FiniteField.pow_card, sub_self]⟩
  have he : Function.Injective e := by
    intro φ ψ h
    have h1 : φ (γ : K) = ψ (γ : K) := congrArg Subtype.val h
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨n, hn⟩ := hγ (Units.mk0 x hx)
      have hn' : (γ ^ n : Kˣ) = Units.mk0 x hx := hn
      have : x = ((γ ^ n : Kˣ) : K) := by rw [hn']; rfl
      rw [this, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, h1]
  calc Nat.card (K →+* F) ≤ Nat.card {x : F // x ∈ P.roots.toFinset} :=
        Nat.card_le_card_of_injective e he
    _ = P.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = Nat.card K := by rw [hPdeg, hq, Nat.card_eq_fintype_card]

/-- Ring homs from a polynomial ring in at most one variable over a finite field into a field
with `Q` elements number at most `#K * Q`. -/
private theorem curveZetaEulerFactor_card_ringHom_mvPolynomial_le {K F : Type*} [Field K]
    [Finite K] [Field F]
    [Finite F] {s : ℕ} (hs : s ≤ 1) :
    Finite (MvPolynomial (Fin s) K →+* F) ∧
      Nat.card (MvPolynomial (Fin s) K →+* F) ≤ Nat.card K * Nat.card F := by
  have hinj : Function.Injective (fun ψ : MvPolynomial (Fin s) K →+* F ↦
      (ψ.comp MvPolynomial.C, fun i ↦ ψ (MvPolynomial.X i))) := by
    intro ψ χ h
    simp only [Prod.mk.injEq, funext_iff] at h
    exact MvPolynomial.ringHom_ext (fun c ↦ by simpa using congrArg (· c) h.1) h.2
  have : Finite (K →+* F) := Finite.of_injective _ DFunLike.coe_injective
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  calc Nat.card (MvPolynomial (Fin s) K →+* F)
      ≤ Nat.card ((K →+* F) × (Fin s → F)) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (K →+* F) * Nat.card F ^ s := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    _ ≤ Nat.card K * Nat.card F := by
        gcongr
        · exact curveZetaEulerFactor_card_ringHom_finiteField_le
        · have : 0 < Nat.card F := Nat.card_pos
          interval_cases s <;> simp; omega

/-- Ring homs from a finite-type algebra over a finite field that is integral over a polynomial
ring in at most one variable into a finite field with `Q` elements number `O(Q)`. -/
private theorem curveZetaEulerFactor_card_ringHom_le_of_isIntegral {K S : Type*} [Field K]
    [Finite K] [CommRing S]
    [Algebra K S] [Algebra.FiniteType K S] {s : ℕ} (hs : s ≤ 1)
    (g : MvPolynomial (Fin s) K →ₐ[K] S) (hg : g.IsIntegral) :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [Finite F],
      Finite (S →+* F) ∧ Nat.card (S →+* F) ≤ C * Nat.card F := by
  classical
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := K) (A := S)
  choose p hpm hp using fun a : G ↦ hg (a : S)
  refine ⟨Nat.card K * ∏ a : G, (p a).natDegree, fun F _ _ ↦ ?_⟩
  obtain ⟨hfin, hcard⟩ := curveZetaEulerFactor_card_ringHom_mvPolynomial_le (K := K) (F := F) hs
  let M := MvPolynomial (Fin s) K
  let R : (M →+* F) → G → Finset F := fun ψ a ↦ ((p a).map ψ).roots.toFinset
  let T := Σ ψ : (M →+* F), (Π a : G, {x : F // x ∈ R ψ a})
  let e : (S →+* F) → T :=
    fun φ ↦ ⟨φ.comp g.toRingHom, fun a ↦ ⟨φ a, by
      have hne : (p a).map (φ.comp g.toRingHom) ≠ 0 := ((hpm a).map _).ne_zero
      simp only [R, Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_map]
      rw [← hom_eval₂, hp a, map_zero]⟩⟩
  have he : Function.Injective e := by
    intro φ ψ h
    have h1 : φ.comp g.toRingHom = ψ.comp g.toRingHom := congrArg Sigma.fst h
    have h2 : ∀ a : G, φ a = ψ a := fun a ↦ congrArg (fun σ : T ↦ (σ.2 a).val) h
    have hK : ∀ c : K, φ (algebraMap K S c) = ψ (algebraMap K S c) := by
      intro c
      have := congrArg (fun χ : M →+* F ↦ χ (MvPolynomial.C c)) h1
      simpa [M] using this
    have key : ∀ x ∈ Algebra.adjoin K (G : Set S), φ x = ψ x := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx => exact h2 ⟨x, hx⟩
      | algebraMap c => exact hK c
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
      | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
    exact RingHom.ext fun x ↦ key x (hG ▸ Algebra.mem_top)
  let : Fintype (M →+* F) := Fintype.ofFinite _
  refine ⟨Finite.of_injective e he, ?_⟩
  have hR : ∀ ψ a, (R ψ a).card ≤ (p a).natDegree := fun ψ a ↦
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
      ((hpm a).natDegree_map ψ).le)
  calc Nat.card (S →+* F) ≤ Nat.card T := Nat.card_le_card_of_injective e he
    _ = ∑ ψ : M →+* F, ∏ a : G, (R ψ a).card := by
        simp only [T, Nat.card_sigma, Nat.card_pi, Nat.card_eq_finsetCard]
    _ ≤ ∑ _ψ : M →+* F, ∏ a : G, (p a).natDegree :=
        Finset.sum_le_sum fun ψ _ ↦ Finset.prod_le_prod fun a _ ↦ hR ψ a
    _ = Nat.card (M →+* F) * ∏ a : G, (p a).natDegree := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ Nat.card K * Nat.card F * ∏ a : G, (p a).natDegree := by gcongr
    _ = _ := by ring

/-- A quasi-finite algebra has Krull dimension at most that of the base. -/
private theorem curveZetaEulerFactor_ringKrullDim_le_of_quasiFinite {R S : Type*} [CommRing R]
    [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono
    (fun q : PrimeSpectrum S ↦ PrimeSpectrum.comap (algebraMap R S) q) fun a b hab ↦ ?_
  have hle : a.asIdeal ≤ b.asIdeal := hab.le
  refine lt_of_le_of_ne (show a.asIdeal.comap (algebraMap R S) ≤ b.asIdeal.comap _ from
    Ideal.comap_mono hle) fun h ↦ hab.ne ?_
  ext1
  exact Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) a.asIdeal b.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)

/-- An injective integral extension has Krull dimension at least that of the base. -/
private theorem curveZetaEulerFactor_ringKrullDim_le_of_isIntegral_of_injective {R S : Type*}
    [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (h : Function.Injective (algebraMap R S)) : ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
    (⊥ : Ideal S) (by
      intro x hx
      have : algebraMap R S x = 0 := hx
      rw [h (this.trans (map_zero _).symm)]
      exact zero_mem _)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- A standard smooth algebra of relative dimension one over a field has Krull dimension at
most one: it is etale, hence quasi-finite, over a polynomial ring in one variable. -/
private theorem curveZetaEulerFactor_ringKrullDim_le_one_of_isStandardSmoothOfRelativeDimension_one
    {K S : Type*}
    [Field K] [CommRing S] [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 1 K S] :
    ringKrullDim S ≤ 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K S
  algebraize [g.toRingHom]
  have h1 :=
    curveZetaEulerFactor_ringKrullDim_le_of_quasiFinite (R := MvPolynomial (Fin 1) K) (S := S)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    at h1
  simpa using h1

/-- Ring homs from a standard smooth algebra of relative dimension one over a finite field into
a finite field with `Q` elements number `O(Q)`. -/
private theorem curveZetaEulerFactor_card_ringHom_le_of_isStandardSmoothOfRelativeDimension_one
    {K S : Type*}
    [Field K] [Finite K] [CommRing S] [Algebra K S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K S] :
    ∃ C : ℕ, ∀ (F : Type*) [Field F] [Finite F],
      Finite (S →+* F) ∧ Nat.card (S →+* F) ≤ C * Nat.card F := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · refine ⟨0, fun F _ _ ↦ ?_⟩
    have : IsEmpty (S →+* F) := ⟨fun φ ↦ one_ne_zero (φ.map_one.symm.trans
        (by rw [Subsingleton.elim (1 : S) 0, map_zero]))⟩
    exact ⟨inferInstance, by simp⟩
  have : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K S
  have hdim :=
    curveZetaEulerFactor_ringKrullDim_le_one_of_isStandardSmoothOfRelativeDimension_one
      (K := K) (S := S)
  algebraize [g.toRingHom]
  have h2 := curveZetaEulerFactor_ringKrullDim_le_of_isIntegral_of_injective
    (R := MvPolynomial (Fin s) K) (S := S)
    hginj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    at h2
  have hs : s ≤ 1 := by
    have := h2.trans hdim
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at this
    exact_mod_cast this
  exact curveZetaEulerFactor_card_ringHom_le_of_isIntegral hs g hgint

end

/-- On an affine open `U`, a morphism from the spectrum of a field `K` into `U` is determined by
the ring hom `Γ(X, U) → K` it induces. -/
private theorem curveZetaEulerFactor_specHom_affineOpen_injective (U : X.Opens)
    (hU : IsAffineOpen U) (K : Type u) [Field K] :
    ∃ e : (Spec (.of K) ⟶ ↑U) → (Γ(X, U) →+* K), Function.Injective e :=
  ⟨fun φ ↦ (Spec.homEquiv (φ ≫ hU.isoSpec.hom)).hom, fun φ ψ h ↦ by
    have h2 := Spec.homEquiv.injective (CommRingCat.Hom.ext h)
    have := congrArg (fun t ↦ t ≫ hU.isoSpec.inv) h2
    simpa [Category.assoc] using this⟩

/-- On a standard smooth chart of relative dimension one over the base field, the ring homs
from the sections into a finite field with `Q` elements number `O(Q)`. -/
private theorem curveZetaEulerFactor_card_ringHom_chart (f : X ⟶ Spec (.of k))
    {U : (Spec (.of k)).Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (hU : U = ⊤)
    (hf : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension 1) :
    ∃ C : ℕ, ∀ (K : Type u) [Field K] [Finite K],
      Finite (Γ(X, V) →+* K) ∧ Nat.card (Γ(X, V) →+* K) ≤ C * Nat.card K := by
  subst hU
  let φ : Γ(Spec (.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have hfield : IsField Γ(Spec (.of k), ⊤) := φ.toMulEquiv.isField (Field.toIsField k)
  let : Field Γ(Spec (.of k), ⊤) := hfield.toField
  have : Finite Γ(Spec (.of k), ⊤) := Finite.of_injective φ φ.injective
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨C, hC⟩ :=
    curveZetaEulerFactor_card_ringHom_le_of_isStandardSmoothOfRelativeDimension_one
      (K := Γ(Spec (.of k), ⊤)) (S := Γ(X, V))
  exact ⟨C, fun K _ _ ↦ hC K⟩

/-- A smooth quasi-compact curve over a finite field has `O(Q)` points with values in a finite
field with `Q` elements. -/
private theorem curveZetaEulerFactor_card_specHom_le (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [QuasiCompact f] :
    ∃ C : ℕ, ∀ (K : Type u) [Field K] [Finite K],
      Finite (Spec (.of K) ⟶ X) ∧ Nat.card (Spec (.of K) ⟶ X) ≤ C * Nat.card K := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hpick : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ C : ℕ,
      ∀ (K : Type u) [Field K] [Finite K],
        Finite (Γ(X, V) →+* K) ∧ Nat.card (Γ(X, V) →+* K) ≤ C * Nat.card K := by
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
    have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by
      rw [Subsingleton.elim y (f x)]
      exact e hx
    exact ⟨V, hV, hx, curveZetaEulerFactor_card_ringHom_chart f e hUtop hf⟩
  choose V hV hxV C hC using hpick
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (s := Set.univ)
    (U := fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩)
  have hcover : ∀ y : X, ∃ x : X, x ∈ t ∧ y ∈ V x := by
    intro y
    have h := ht (Set.mem_univ y)
    simpa using h
  refine ⟨∑ i ∈ t, C i, fun K _ _ ↦ ?_⟩
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  have key : ∀ h : Spec (.of K) ⟶ X,
      ∃ (i : t) (h' : Spec (.of K) ⟶ ↑(V (i : X))), h' ≫ (V (i : X)).ι = h := by
    intro h
    obtain ⟨x, hx, hmem⟩ := hcover (h pt)
    have hrange : Set.range ⇑h ⊆ Set.range ⇑(V x).ι := by
      rw [Scheme.Opens.range_ι]
      rintro y ⟨z, rfl⟩
      rw [Subsingleton.elim z pt]
      exact hmem
    exact ⟨⟨x, hx⟩, IsOpenImmersion.lift (V x).ι h hrange,
      IsOpenImmersion.lift_fac (V x).ι h hrange⟩
  let F : (Spec (.of K) ⟶ X) → Σ i : t, (Spec (.of K) ⟶ ↑(V (i : X))) :=
    fun h => ⟨(key h).choose, (key h).choose_spec.choose⟩
  have Ffac : ∀ h, (F h).2 ≫ (V ((F h).1 : X)).ι = h :=
    fun h => (key h).choose_spec.choose_spec
  have hF : Function.Injective F := by
    intro a b hab
    have h1 := Ffac a
    have h2 := Ffac b
    rw [hab] at h1
    exact h1.symm.trans h2
  choose E hE using fun i : t ↦ curveZetaEulerFactor_specHom_affineOpen_injective
    (V (i : X)) (hV i) K
  have hG : Function.Injective (@Sigma.map t t (fun i ↦ Spec (.of K) ⟶ ↑(V (i : X)))
      (fun i ↦ Γ(X, V (i : X)) →+* K) id E ∘ F) :=
    (Function.Injective.sigma_map (fun _ _ h ↦ h) hE).comp hF
  have : ∀ i : t, Finite (Γ(X, V (i : X)) →+* K) := fun i ↦ (hC i K).1
  refine ⟨Finite.of_injective _ hG, ?_⟩
  calc Nat.card (Spec (.of K) ⟶ X)
      ≤ Nat.card (Σ i : t, (Γ(X, V (i : X)) →+* K)) := Nat.card_le_card_of_injective _ hG
    _ = ∑ i : t, Nat.card (Γ(X, V (i : X)) →+* K) := Nat.card_sigma
    _ ≤ ∑ i : t, C i * Nat.card K := Finset.sum_le_sum fun i _ ↦ (hC i K).2
    _ = (∑ i ∈ t, C i) * Nat.card K := by
        rw [Finset.sum_coe_sort t (fun i ↦ C i * Nat.card K), Finset.sum_mul]

/-- The closed points of degree `m` of a smooth proper curve over `k` number `O(q ^ m)`. -/
private theorem curveZetaEulerFactor_closedPointsOfDegree_le (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] :
    ∃ C : ℕ, ∀ m : ℕ,
      {x : X | x ∈ closedPoints X ∧ Nat.card (X.residueField x) = Nat.card k ^ m}.Finite ∧
      {x : X | x ∈ closedPoints X ∧ Nat.card (X.residueField x) = Nat.card k ^ m}.ncard ≤
        C * Nat.card k ^ m := by
  obtain ⟨C, hC⟩ := curveZetaEulerFactor_card_specHom_le f
  refine ⟨C, fun m ↦ ?_⟩
  set S : Set X := {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ m} with hSdef
  rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · rw [hempty]
    simp
  · obtain ⟨-, hx₀card⟩ := hx₀
    have hK0 : Nat.card (X.residueField x₀) ≠ 0 := by
      rw [hx₀card]
      exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
    have : Finite (X.residueField x₀) := (Nat.card_ne_zero.mp hK0).2
    have : Fintype (X.residueField x₀) := Fintype.ofFinite _
    obtain ⟨hfin, hcard⟩ := hC (X.residueField x₀)
    let pt : ↥(Spec (.of (↥(X.residueField x₀)))) := default
    have hsub : S ⊆ Set.range (fun h : Spec (.of (↥(X.residueField x₀))) ⟶ X => h pt) := by
      rintro x ⟨-, hxcard⟩
      have hx0 : Nat.card (X.residueField x) ≠ 0 := by
        rw [hxcard]
        exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
      have : Finite (X.residueField x) := (Nat.card_ne_zero.mp hx0).2
      have : Fintype (X.residueField x) := Fintype.ofFinite _
      have hc : Fintype.card (X.residueField x) = Fintype.card (X.residueField x₀) := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hxcard, hx₀card]
      let e : (X.residueField x) ≃+* (X.residueField x₀) := FiniteField.ringEquivOfCardEq hc
      refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x, ?_⟩
      exact Scheme.fromSpecResidueField_apply x _
    refine ⟨(Set.finite_range _).subset hsub, ?_⟩
    calc S.ncard ≤ (Set.range (fun h : Spec (.of (↥(X.residueField x₀))) ⟶ X => h pt)).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_range _)
      _ ≤ Nat.card (Spec (.of (↥(X.residueField x₀))) ⟶ X) := by
          rw [← Set.image_univ, ← Set.ncard_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ ≤ C * Nat.card (X.residueField x₀) := hcard
      _ = C * Nat.card k ^ m := by rw [hx₀card]

/-- A sum `∑ r ^ deg x` converges when the fibres of `deg` have `O(q ^ m)` elements and
`q r < 1`. -/
private theorem curveZetaEulerFactor_summable_pow_deg {ι : Type*} (deg : ι → ℕ) (C q r : ℝ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hqr : q * r < 1)
    (hcard : ∀ (T : Finset ι) (m : ℕ), ((T.filter (deg · = m)).card : ℝ) ≤ C * q ^ m) :
    Summable (fun x ↦ r ^ deg x) := by
  classical
  have hgeo : Summable (fun m : ℕ ↦ (q * r) ^ m) :=
    summable_geometric_of_lt_one (by positivity) hqr
  refine summable_of_sum_le (c := C * ∑' m : ℕ, (q * r) ^ m) (fun _ ↦ by positivity) fun T ↦ ?_
  rw [Finset.sum_comp (fun m ↦ r ^ m) deg]
  have hC : 0 ≤ C := by
    have := hcard ∅ 0
    simpa using this
  calc ∑ m ∈ T.image deg, (T.filter (deg · = m)).card • r ^ m
      ≤ ∑ m ∈ T.image deg, C * (q * r) ^ m := Finset.sum_le_sum fun m _ ↦ by
        rw [nsmul_eq_mul, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hcard T m) (by positivity)
    _ = C * ∑ m ∈ T.image deg, (q * r) ^ m := by rw [Finset.mul_sum]
    _ ≤ C * ∑' m : ℕ, (q * r) ^ m :=
        mul_le_mul_of_nonneg_left (hgeo.sum_le_tsum _ fun _ _ ↦ by positivity) hC

/-- `‖(1 - u)⁻¹ - 1‖ ≤ 2 ‖u‖` when `‖u‖ ≤ 1/2`. -/
private theorem curveZetaEulerFactor_norm_inv_one_sub_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖(1 - u)⁻¹ - 1‖ ≤ 2 * ‖u‖ := by
  have h1 : 1 / 2 ≤ ‖1 - u‖ := by
    have := norm_sub_norm_le (1 : ℂ) u
    simp only [norm_one] at this
    linarith
  have hne : (1 - u) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    linarith
  rw [show (1 - u)⁻¹ - 1 = u / (1 - u) by field_simp; ring, norm_div,
    div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg u]

/-- Paper: (14.2.0.1), p. 534. The product converges absolutely on its
half-plane of definition. -/
theorem summable_curveZetaEulerFactor_sub_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    Summable (fun x : closedPoints X ↦ ‖curveZetaEulerFactor x s.val - 1‖) := by
  obtain ⟨C, hC⟩ := curveZetaEulerFactor_closedPointsOfDegree_le f
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  set q : ℝ := (Nat.card k : ℝ) with hqdef
  have hq2 : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set σ := s.val.re with hσdef
  have hσ : 1 < σ := s.2
  choose deg hdeg1 hdeg using fun x : closedPoints X ↦ closedPoint_residueField_card_pow f x.2
  set r : ℝ := q ^ (-σ) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hqr : q * r < 1 := by
    have : q * r = q ^ (1 - σ) := by
      rw [hrdef, Real.rpow_sub hq0, Real.rpow_one, Real.rpow_neg hq0.le, div_eq_mul_inv]
    rw [this]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hsum : Summable (fun x : closedPoints X ↦ r ^ deg x) := by
    refine curveZetaEulerFactor_summable_pow_deg deg C q r hr0 hq0.le hqr fun T m ↦ ?_
    obtain ⟨hfin, hle⟩ := hC m
    have h1 : (T.filter (deg · = m)).card ≤ {x : X | x ∈ closedPoints X ∧
        Nat.card (X.residueField x) = Nat.card k ^ m}.ncard := by
      rw [← Finset.card_map (Function.Embedding.subtype _), ← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ hfin
      intro y hy
      simp only [Finset.coe_map, Function.Embedding.subtype_apply, Set.mem_image,
        Finset.mem_coe, Finset.mem_filter] at hy
      obtain ⟨x, ⟨-, hxm⟩, rfl⟩ := hy
      exact ⟨x.2, hxm ▸ hdeg x⟩
    have h2 : ((T.filter (deg · = m)).card : ℝ) ≤ ((C * Nat.card k ^ m : ℕ) : ℝ) := by
      exact_mod_cast h1.trans hle
    simpa [hqdef] using h2
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun x ↦ ?_) (hsum.mul_left 2)
  have hN : (Nat.card (X.residueField x.val) : ℝ) = q ^ deg x := by
    rw [hdeg x, hqdef]
    push_cast
    rfl
  have hNpos : 0 < Nat.card (X.residueField x.val) := by
    rw [hdeg x]
    positivity
  have hnorm : ‖(Nat.card (X.residueField x.val) : ℂ) ^ (-s.val)‖ = r ^ deg x := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re, hN, hrdef,
      ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le, mul_comm]
  have hhalf : r ^ deg x ≤ 1 / 2 := by
    have hr1 : r ≤ 1 / 2 := by
      rw [hrdef]
      calc q ^ (-σ) ≤ q ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = q⁻¹ := Real.rpow_neg_one q
        _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) hq2
    calc r ^ deg x ≤ r ^ 1 :=
          pow_le_pow_of_le_one hr0 (hr1.trans (by norm_num)) (hdeg1 x)
      _ ≤ 1 / 2 := by rw [pow_one]; exact hr1
  show ‖(1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s.val))⁻¹ - 1‖ ≤ 2 * r ^ deg x
  rw [← hnorm]
  exact curveZetaEulerFactor_norm_inv_one_sub_sub_one_le (hnorm ▸ hhalf)

/-- The order of `exp w - 1` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_exp_sub_one (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => Complex.exp s - 1) w = 1 := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (f := fun x : ℂ => x)
    (g := fun s : ℂ => Complex.exp s - 1) (x := w)
    (analyticAt_cexp.sub analyticAt_const) (by simp [Complex.deriv_exp, hw])
  simp only [Function.comp_def] at hcomp
  rw [hcomp, show Complex.exp w - 1 = 0 from by rw [hw]; ring]
  exact meromorphicOrderAt_id (𝕜 := ℂ)

/-- The order of `1 - exp w` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_one_sub_exp (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => 1 - Complex.exp s) w = 1 := by
  have h := meromorphicOrderAt_exp_sub_one w hw
  have hneg : meromorphicOrderAt (fun s : ℂ => -(Complex.exp s - 1)) w = 1 := by
    rw [← meromorphicOrderAt_fun_neg (f := fun s : ℂ => Complex.exp s - 1) (x := w)]
    exact h
  rw [show (fun s : ℂ => 1 - Complex.exp s) = fun s : ℂ => -(Complex.exp s - 1) from by
    funext s; ring]
  exact hneg

/-- The reciprocal local factor `(1 - exp w)⁻¹` has a simple pole at `w`. -/
private lemma meromorphicOrderAt_one_sub_exp_inv (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp s)⁻¹) w = -1 := by
  have h := meromorphicOrderAt_one_sub_exp w hw
  have hfun : (fun s : ℂ => (1 - Complex.exp s)⁻¹) = (fun s : ℂ => 1 - Complex.exp s)⁻¹ := rfl
  rw [hfun, meromorphicOrderAt_inv, h]

/-- Composing with the affine substitution `s ↦ -(s * L)` (`L ≠ 0`) transports the pole. -/
private lemma meromorphicOrderAt_one_sub_exp_inv_affine (L : ℝ) (hL : L ≠ 0) (z : ℂ)
    (hz : Complex.exp (-(z * (L : ℂ))) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp (-(s * (L : ℂ))))⁻¹) z = -1 := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ)
    (f := fun s : ℂ => (1 - Complex.exp s)⁻¹) (g := fun s : ℂ => -(s * (L : ℂ))) (x := z)
    (by fun_prop) (by simp [hL])
  simp only [Function.comp_def] at h
  rw [h]
  exact meromorphicOrderAt_one_sub_exp_inv _ hz

/-- The complex power of a positive natural number, written through the exponential. -/
private lemma natCast_cpow_eq_exp (c : ℕ) (hc : c ≠ 0) (z : ℂ) :
    (c : ℂ) ^ (-z) = Complex.exp (-(z * (Real.log c : ℂ))) := by
  have hc0 : (c : ℂ) ≠ 0 := by simpa using hc
  rw [Complex.cpow_def_of_ne_zero hc0, Complex.natCast_log]
  ring_nf

/-- A single local factor `(1 - c ^ (-s))⁻¹` with `c ≥ 2` has a simple pole at every `z`
where `c ^ (-z) = 1`. -/
private lemma meromorphicOrderAt_cpow_factor (c : ℕ) (hc : 2 ≤ c) (z : ℂ)
    (hz : (c : ℂ) ^ (-z) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) z = -1 := by
  have hc0 : c ≠ 0 := by omega
  have hL : Real.log c ≠ 0 := by
    have h1 : (1 : ℝ) < c := by exact_mod_cast hc
    exact ne_of_gt (Real.log_pos h1)
  have hz' : Complex.exp (-(z * (Real.log c : ℂ))) = 1 := by
    rw [← natCast_cpow_eq_exp c hc0 z]
    exact hz
  have hfun : (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) =
      fun s : ℂ => (1 - Complex.exp (-(s * (Real.log c : ℂ))))⁻¹ := by
    funext s
    rw [natCast_cpow_eq_exp c hc0 s]
  rw [hfun]
  exact meromorphicOrderAt_one_sub_exp_inv_affine _ hL z hz'

/-- Paper: §14.2, p. 534. For a finite set of closed points every local
factor has a simple pole at each integral multiple of the imaginary period.
The product has pole order equal to the number of places. -/
theorem curveZetaEulerFactor_prod_order (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (S : Finset (closedPoints X)) (n : ℤ) :
    meromorphicOrderAt (fun s : ℂ ↦ ∏ x ∈ S, curveZetaEulerFactor x s)
      (2 * Real.pi * Complex.I * n / Real.log (Nat.card k)) = -(S.card : ℤ) := by
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hlogk : Real.log (Nat.card k) ≠ 0 := by
    have h1 : (1 : ℝ) < Nat.card k := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos h1)
  set s0 : ℂ := 2 * Real.pi * Complex.I * n / Real.log (Nat.card k) with hs0
  have hkey : ∀ x ∈ S, meromorphicOrderAt (curveZetaEulerFactor x) s0 = -1 := by
    intro x _
    obtain ⟨m, hm1, hm⟩ := closedPoint_residueField_card_pow f x.2
    have hc2 : 2 ≤ Nat.card (X.residueField x.val) := by
      rw [hm]
      exact le_trans hq (le_self_pow (by omega) (by omega))
    have hval : (Nat.card (X.residueField x.val) : ℂ) ^ (-s0) = 1 := by
      have hc0 : Nat.card (X.residueField x.val) ≠ 0 := by omega
      have hlogc : Real.log (Nat.card (X.residueField x.val)) =
          (m : ℝ) * Real.log (Nat.card k) := by
        rw [hm, Nat.cast_pow, Real.log_pow]
      rw [natCast_cpow_eq_exp _ hc0, hlogc, hs0]
      push_cast
      have hlk : Complex.log ((Nat.card k : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        exact_mod_cast hlogk
      have harg : -((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / Complex.log ((Nat.card k : ℕ) : ℂ)) *
            ((m : ℂ) * Complex.log ((Nat.card k : ℕ) : ℂ))) =
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
        push_cast
        ring
      rw [harg]
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(n * (m : ℤ)))
    exact meromorphicOrderAt_cpow_factor _ hc2 s0 hval
  rw [meromorphicOrderAt_fun_prod fun x hx =>
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hkey x hx]; norm_num)]
  rw [Finset.sum_congr rfl hkey, Finset.sum_const]
  norm_num

-- TODO(paper-gap): Page 534 does not construct the function-field Sobolev
-- quotient or show that the trace approximation requires one Mellin test to
-- cancel all finite-stage poles. Under T = q^(-s) these lifts give one point.

/-- A finitely generated algebra over a finite ring has finitely many ring homs into a
finite field. -/
private theorem finite_ringHom_of_adjoin {R A K : Type u} [CommSemiring R] [Finite R]
    [CommRing A] [Algebra R A] [Field K] [Finite K]
    (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤) : Finite (A →+* K) := by
  refine Finite.of_injective
    (fun φ : A →+* K => (fun r : R => φ (algebraMap R A r), fun a : s => φ a)) ?_
  intro φ ψ h
  simp only [Prod.mk.injEq, funext_iff] at h
  obtain ⟨h1, h2⟩ := h
  have key : ∀ a, a ∈ Algebra.adjoin R (s : Set A) → φ a = ψ a := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => φ a = ψ a) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact h2 ⟨x, hx⟩
    · intro r
      exact h1 r
    · intro x y _ _ ihx ihy
      rw [map_add, map_add, ihx, ihy]
    · intro x y _ _ ihx ihy
      rw [map_mul, map_mul, ihx, ihy]
  exact RingHom.ext fun a => key a (hs ▸ Algebra.mem_top)

/-- Morphisms from the spectrum of a finite field into an affine open of a scheme locally of
finite type over a finite field are finite in number. -/
private theorem finite_spec_hom_affineOpen (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (K : Type u) [Field K] [Finite K] (U : X.Opens) (hU : IsAffineOpen U) :
    Finite (Spec (.of K) ⟶ ↑U) := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let g : Γ(Spec (.of k), ⊤) →+* Γ(X, U) := (Scheme.Hom.appLE f ⊤ U hle).hom
  have hg : g.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU hle
  haveI : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_injective
      ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv : Γ(Spec (.of k), ⊤) → k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective
  have hAfin : Finite (Γ(X, U) →+* K) := by
    letI := g.toAlgebra
    obtain ⟨s, hs⟩ := hg.out
    exact finite_ringHom_of_adjoin s hs
  have h1 : Finite (Spec (.of K) ⟶ Spec (Γ(X, U))) := by
    have h2 : Finite (CommRingCat.of (Γ(X, U)) ⟶ CommRingCat.of K) :=
      Finite.of_injective (fun f => f.hom) (fun f g' h => CommRingCat.Hom.ext h)
    exact Finite.of_injective (fun φ => Spec.homEquiv φ) Spec.homEquiv.injective
  exact Finite.of_injective (fun φ : Spec (.of K) ⟶ ↑U => φ ≫ hU.isoSpec.hom)
    (fun φ ψ h => by
      have := congrArg (fun t => t ≫ hU.isoSpec.inv) h
      simpa [Category.assoc] using this)

/-- A scheme locally of finite type and quasi-compact over a finite field has finitely many
points with values in any fixed finite field. -/
private theorem finite_spec_hom (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Type u) [Field K] [Finite K] : Finite (Spec (.of K) ⟶ X) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hpick : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hx⟩
  choose U hU using hpick
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (s := Set.univ)
    (U := fun x : X => (U x : Set X)) (fun x => (U x : X.Opens).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hU y⟩)
  have hcover : ∀ y : X, ∃ x : X, x ∈ t ∧ y ∈ (U x : X.Opens) := by
    intro y
    have h := ht (Set.mem_univ y)
    simpa using h
  haveI hpiece : ∀ x : X, Finite (Spec (.of K) ⟶ ↑(U x : X.Opens)) :=
    fun x => finite_spec_hom_affineOpen f K (U x : X.Opens) (U x).2
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  haveI : Unique ↥(Spec (.of K)) := inferInstance
  have key : ∀ h : Spec (.of K) ⟶ X,
      ∃ (i : t) (h' : Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)),
        h' ≫ (U (i : X) : X.Opens).ι = h := by
    intro h
    obtain ⟨x, hx, hmem⟩ := hcover (h pt)
    have hrange : Set.range ⇑h ⊆ Set.range ⇑(U x : X.Opens).ι := by
      rw [Scheme.Opens.range_ι]
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      rw [Subsingleton.elim z pt]
      exact hmem
    exact ⟨⟨x, hx⟩, IsOpenImmersion.lift (U x : X.Opens).ι h hrange,
      IsOpenImmersion.lift_fac (U x : X.Opens).ι h hrange⟩
  let F : (Spec (.of K) ⟶ X) → Σ i : t, (Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)) :=
    fun h => ⟨(key h).choose, (key h).choose_spec.choose⟩
  have Ffac : ∀ h, (F h).2 ≫ (U ((F h).1 : X) : X.Opens).ι = h :=
    fun h => (key h).choose_spec.choose_spec
  refine Finite.of_injective F ?_
  intro a b hab
  have h1 := Ffac a
  have h2 := Ffac b
  rw [hab] at h1
  exact h1.symm.trans h2

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Page 534 says that the factors repeat "infinitely many times". The
number at each fixed degree is finite, and p. 535 estimates it; it grows as the
degree tends to infinity. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by
  classical
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rcases m with _ | m
  · have hempty : {x : X | x ∈ closedPoints X ∧
        Nat.card (X.residueField x) = Nat.card k ^ 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hc
      obtain ⟨n, hn, hncard⟩ := closedPoint_residueField_card_pow f hx
      have h2 : 2 ≤ Nat.card (X.residueField x) := by
        rw [hncard]
        exact le_trans hq (le_self_pow (by omega) (by omega))
      rw [pow_zero] at hc
      omega
    rw [hempty]
    exact Set.finite_empty
  · set S : Set X := {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ (m + 1)} with hSdef
    rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · rw [hempty]
      exact Set.finite_empty
    · rw [hSdef] at hx₀
      obtain ⟨hx₀cl, hx₀card⟩ := hx₀
      have hK0 : Nat.card (X.residueField x₀) ≠ 0 := by
        rw [hx₀card]
        exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
      haveI : Finite (X.residueField x₀) := (Nat.card_ne_zero.mp hK0).2
      haveI : Fintype (X.residueField x₀) := Fintype.ofFinite _
      haveI : QuasiCompact f := inferInstance
      haveI : Finite (Spec (.of (↥(X.residueField x₀))) ⟶ X) :=
        finite_spec_hom f (↥(X.residueField x₀))
      let pt : ↥(Spec (.of (↥(X.residueField x₀)))) := default
      have hsub : S ⊆ Set.range (fun h : Spec (.of (↥(X.residueField x₀))) ⟶ X => h pt) := by
        intro x hx
        rw [hSdef] at hx
        obtain ⟨hxcl, hxcard⟩ := hx
        have hx0 : Nat.card (X.residueField x) ≠ 0 := by
          rw [hxcard]
          exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
        haveI : Finite (X.residueField x) := (Nat.card_ne_zero.mp hx0).2
        haveI : Fintype (X.residueField x) := Fintype.ofFinite _
        have hcard : Fintype.card (X.residueField x) =
            Fintype.card (X.residueField x₀) := by
          have h1 : Fintype.card (X.residueField x) = Nat.card (X.residueField x) :=
            (Nat.card_eq_fintype_card).symm
          have h2 : Fintype.card (X.residueField x₀) = Nat.card (X.residueField x₀) :=
            (Nat.card_eq_fintype_card).symm
          rw [h1, h2, hxcard, hx₀card]
        let e : (X.residueField x) ≃+* (X.residueField x₀) :=
          FiniteField.ringEquivOfCardEq hcard
        let h : Spec (.of (↥(X.residueField x₀))) ⟶ X :=
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x
        refine ⟨h, ?_⟩
        show (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x) pt = x
        exact Scheme.fromSpecResidueField_apply x _
      exact Set.Finite.subset (Set.finite_range _) hsub

/-- Paper: §14.2, p. 535. The number of closed points of degree m over k. -/
noncomputable def curveZetaClosedPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) : ℕ :=
  {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ m}.ncard

/-- The structure ring map `k →+* κ(x)` at a point of a curve over `k`: the ring map of the
morphism `Spec κ(x) ⟶ Spec k` induced by `X.fromSpecResidueField x ≫ f`. -/
private noncomputable def curveZetaStructMap (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* ↥(X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom

omit [Finite k] in
private lemma curveZetaStructMap_spec (f : X ⟶ Spec (.of k)) (x : X) :
    Spec.map (CommRingCat.ofHom (curveZetaStructMap f x)) =
      X.fromSpecResidueField x ≫ f := by
  rw [curveZetaStructMap, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

/-- A morphism `Spec K ⟶ Spec κ(x)` composed with the structure map of `x` is a morphism over
`k` exactly when the corresponding ring map is a morphism of `k`-algebras. -/
private lemma curveZeta_structMap_comp_iff {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) (ψ : ↥(X.residueField x) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ↔
      ψ.comp (curveZetaStructMap f x) = algebraMap k K := by
  have hspec := curveZetaStructMap_spec f x
  constructor
  · intro h
    rw [← hspec, ← Spec.map_comp] at h
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h)
    simpa [RingHom.comp_apply] using h2
  · intro h
    rw [← hspec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- A point of a curve over `k` whose residue field maps into a finite field is a closed point. -/
private lemma curveZeta_isClosed_of_residueFieldMap {K : Type u} [Field K] [Algebra k K]
    [Finite K] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f] (x : X)
    (ψ : ↥(X.residueField x) →+* K) (hψ : ψ.comp (curveZetaStructMap f x) = algebraMap k K) :
    IsClosed ({x} : Set X) := by
  classical
  haveI : Module.Finite k K := Module.Finite.of_finite
  haveI : Unique ↥(Spec (.of K)) := inferInstance
  let pt : ↥(Spec (.of K)) := default
  have hof : CommRingCat.ofHom (curveZetaStructMap f x) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (algebraMap k K) := by
    rw [← CommRingCat.ofHom_comp, hψ]
  obtain ⟨p, hp⟩ : ∃ p : Spec (.of K) ⟶ X,
      p = Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x := ⟨_, rfl⟩
  have hpcomp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hp, Category.assoc, ← curveZetaStructMap_spec f x, ← Spec.map_comp, hof]
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsFinite.SpecMap_iff]
    simpa using RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite k K)
  haveI : IsProper (p ≫ f) := hpcomp ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p f
  have hcl : IsClosedMap ⇑p := Scheme.Hom.isClosedMap p
  have hsub : Set.range ⇑p ⊆ {x} := by
    rintro y ⟨s, rfl⟩
    rw [hp, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hxmem : x ∈ Set.range ⇑p :=
    ⟨pt, by
      rw [hp, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply x _⟩
  rw [← show Set.range ⇑p = {x} from
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hxmem)]
  exact hcl.isClosed_range

/-- The residue field of a closed point of a curve over `k` is finite over `k` for the structure
map of the point. -/
private lemma curveZeta_moduleFinite_residueField (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : IsClosed ({x} : Set X)) :
    letI := (curveZetaStructMap f x).toAlgebra
    Module.Finite k ↥(X.residueField x) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hx
  have h2 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (curveZetaStructMap f x))) :=
    (curveZetaStructMap_spec f x) ▸ inferInstance
  have hft : RingHom.FiniteType (curveZetaStructMap f x) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := (curveZetaStructMap f x).toAlgebra
  have h3 : Algebra.FiniteType k ↥(X.residueField x) := hft
  exact finite_of_finite_type_of_isJacobsonRing k _

/-- The ring maps from the residue field of a point into `K` that are compatible with its
structure map, regarded as `k`-algebra maps for the structure map itself. -/
private noncomputable def curveZeta_ringHomEquivAlgHom {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := (curveZetaStructMap f x).toAlgebra
    {ψ : ↥(X.residueField x) →+* K // ψ.comp (curveZetaStructMap f x) = algebraMap k K} ≃
      (↥(X.residueField x) →ₐ[k] K) :=
  letI := (curveZetaStructMap f x).toAlgebra
  { toFun := fun ψ =>
      { toFun := ψ.1
        map_one' := map_one ψ.1
        map_mul' := map_mul ψ.1
        map_zero' := map_zero ψ.1
        map_add' := map_add ψ.1
        commutes' := fun r => RingHom.congr_fun ψ.2 r }
    invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun r => φ.commutes r⟩
    left_inv := fun ψ => Subtype.ext (RingHom.ext fun r => rfl)
    right_inv := fun φ => AlgHom.ext fun r => rfl }

/-- The number of `k`-algebra maps from the residue field of a closed point of degree `d` into a
finite extension of degree divisible by `d` is `d`, and it is `0` otherwise. -/
private lemma curveZeta_natCard_residueFieldMap {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) (x : X) (d : ℕ)
    (hnd : Nat.card (X.residueField x) = Nat.card k ^ d)
    (hfin : letI := (curveZetaStructMap f x).toAlgebra
      Module.Finite k ↥(X.residueField x)) :
    Nat.card {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} =
      if d ∣ Module.finrank k K then d else 0 := by
  classical
  letI := (curveZetaStructMap f x).toAlgebra
  haveI : Module.Finite k ↥(X.residueField x) := hfin
  have hq : 2 ≤ Nat.card k := by
    have : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpow : Nat.card ↥(X.residueField x) =
      Nat.card k ^ Module.finrank k ↥(X.residueField x) := Module.natCard_eq_pow_finrank
  have hfl : Module.finrank k ↥(X.residueField x) = d := by
    refine Nat.pow_right_injective hq ?_
    show Nat.card k ^ Module.finrank k ↥(X.residueField x) = Nat.card k ^ d
    rw [← hpow, hnd]
  rw [Nat.card_congr (curveZeta_ringHomEquivAlgHom f x)]
  by_cases h : d ∣ Module.finrank k K
  · have h' : Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K := hfl ▸ h
    rw [if_pos h, ← hfl]
    exact FiniteField.natCard_algHom_of_finrank_dvd h'
  · rw [if_neg h]
    have hempty : IsEmpty (↥(X.residueField x) →ₐ[k] K) := ⟨fun φ => by
      have hd := FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨φ⟩
      rw [hfl] at hd
      exact h hd⟩
    exact Nat.card_eq_zero.mpr (Or.inl hempty)

/-- A closed point of degree `d` contributes `d` points over an extension whose degree is a
multiple of `d`. -/
private lemma curveZeta_natCard_fiberOfClosed {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] (x : X) (d : ℕ)
    (hx : x ∈ closedPoints X) (hnd : Nat.card (X.residueField x) = Nat.card k ^ d)
    (hdvd : d ∣ Module.finrank k K) :
    Nat.card {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} = d := by
  letI := (curveZetaStructMap f x).toAlgebra
  haveI : Module.Finite k ↥(X.residueField x) :=
    curveZeta_moduleFinite_residueField f (by simpa [closedPoints] using hx)
  rw [curveZeta_natCard_residueFieldMap f x d hnd ‹_›, if_pos hdvd]

/-- A point of the curve whose residue field admits a map into `K` that is compatible with the
structure map has degree dividing the degree of `K`. -/
private lemma curveZeta_dvd_finrank_of_fiber {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) (x : X)
    (ψ : ↥(X.residueField x) →+* K) (hψ : ψ.comp (curveZetaStructMap f x) = algebraMap k K) :
    letI := (curveZetaStructMap f x).toAlgebra
    Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K := by
  letI := (curveZetaStructMap f x).toAlgebra
  exact FiniteField.nonempty_algHom_iff_finrank_dvd.mp
    ⟨{ toFun := ψ
       map_one' := map_one ψ
       map_mul' := map_mul ψ
       map_zero' := map_zero ψ
       map_add' := map_add ψ
       commutes' := fun r => RingHom.congr_fun hψ r }⟩

/-- A sigma type whose fibers carry a predicate is the subtype of the sigma type on which the
predicate holds. -/
private noncomputable def curveZeta_sigmaSubtypeEquiv {α : Type u} (β : α → Type u)
    (q : (a : α) → β a → Prop) :
    ((a : α) × {b : β a // q a b}) ≃ {x : (a : α) × β a // q x.1 x.2} where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The residue-field fiber of a `k`-morphism, in terms of ring maps rather than of morphisms of
commutative rings. -/
private noncomputable def curveZeta_fiberEquiv {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) :
    {φ : X.residueField x ⟶ ↧K //
        Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap k K))} ≃
      {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} where
  toFun φ := ⟨φ.1.hom, (curveZeta_structMap_comp_iff f x φ.1.hom).mp (by
    rw [CommRingCat.ofHom_hom]
    exact φ.2)⟩
  invFun ψ := ⟨CommRingCat.ofHom ψ.1, (curveZeta_structMap_comp_iff f x ψ.1).mpr ψ.2⟩
  left_inv φ := Subtype.ext (CommRingCat.ofHom_hom φ.1)
  right_inv ψ := Subtype.ext rfl

/-- `k`-morphisms from `Spec K` to a curve are pairs of a point of the curve and a compatible
morphism from its residue field into `K`. -/
private noncomputable def curveZeta_overEquiv {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) :
    {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} ≃
      (x : X) × {φ : X.residueField x ⟶ ↧K //
        Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap k K))} :=
  ((Scheme.SpecToEquivOfField K X).subtypeEquiv (p := fun p =>
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (q := fun b : (x : ↥X) × (X.residueField x ⟶ ↧K) =>
      Spec.map b.2 ≫ X.fromSpecResidueField b.1 ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K))) (fun p => by
      have hfac : Spec.map ((Scheme.SpecToEquivOfField K X) p).2 ≫
          X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X) p).1 = p :=
        Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X p
      constructor
      · intro h
        rw [← Category.assoc, hfac]
        exact h
      · intro h
        rw [← Category.assoc, hfac] at h
        exact h)).trans
    (curveZeta_sigmaSubtypeEquiv (fun x => (X.residueField x ⟶ ↧K))
      (fun x φ => Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)))).symm

/-- Paper: §14.2, p. 535. A closed point of degree d contributes d rational
points over an extension of degree m exactly when d divides m.
Deviation: Uses the exact counting identity behind the printed upper bound. -/
theorem curveZeta_extensionPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by
  classical
  have hq : 2 ≤ Nat.card k := by
    have : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  haveI : Module.Finite k K := Module.Finite.of_finite
  have hm : Module.finrank k K ≠ 0 := by
    intro h0
    have hcard : Nat.card K = Nat.card k ^ Module.finrank k K :=
      Module.natCard_eq_pow_finrank
    rw [h0, pow_zero] at hcard
    have : 2 ≤ Nat.card K := by
      have hK : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  set T : ℕ → Set X := fun d => {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ d} with hT
  have hTfin : ∀ d, (T d).Finite := fun d => curveZeta_closedPointsOfDegree_finite f d
  set S : Set X := ⋃ d ∈ (Module.finrank k K).divisors, T d with hS
  set Y : X → Type u := fun x => {φ : X.residueField x ⟶ ↧K //
    Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k K))} with hY
  have hmem : ∀ x : X, Y x → x ∈ S := by
    intro x y
    have hy : y.1.hom.comp (curveZetaStructMap f x) = algebraMap k K :=
      (curveZeta_structMap_comp_iff f x y.1.hom).mp (by
        rw [CommRingCat.ofHom_hom]
        exact y.2)
    have hcl : IsClosed ({x} : Set X) :=
      curveZeta_isClosed_of_residueFieldMap f x y.1.hom hy
    letI := (curveZetaStructMap f x).toAlgebra
    haveI : Module.Finite k ↥(X.residueField x) := curveZeta_moduleFinite_residueField f hcl
    have hpow : Nat.card (X.residueField x) =
        Nat.card k ^ Module.finrank k ↥(X.residueField x) := Module.natCard_eq_pow_finrank
    have hdvd : Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K :=
      curveZeta_dvd_finrank_of_fiber f x y.1.hom hy
    rw [hS]
    exact Set.mem_iUnion₂.mpr
      ⟨_, Nat.mem_divisors.mpr ⟨hdvd, hm⟩, hcl, hpow⟩
  have hYfin : ∀ x ∈ S, Finite (Y x) := by
    intro x hx
    rw [hS] at hx
    obtain ⟨d, -, hxT⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hxcl, -⟩ := hxT
    have hcl : IsClosed ({x} : Set X) := hxcl
    letI := (curveZetaStructMap f x).toAlgebra
    haveI : Module.Finite k ↥(X.residueField x) := curveZeta_moduleFinite_residueField f hcl
    haveI : Finite ↥(X.residueField x) := Module.finite_of_finite k
    haveI : Finite (↥(X.residueField x) →+* K) :=
      Finite.of_injective (fun f : ↥(X.residueField x) →+* K => (f : ↥(X.residueField x) → K))
        DFunLike.coe_injective
    haveI : Finite (X.residueField x ⟶ ↧K) :=
      Finite.of_injective (fun φ : X.residueField x ⟶ ↧K => φ.hom)
        (fun a b hab => CommRingCat.hom_ext hab)
    exact Finite.of_injective (fun y : Y x => y.1) (fun a b hab =>
      Subtype.ext (by simpa using hab))
  have hstep1 : Nat.card
      {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      Nat.card ((x : X) × Y x) := Nat.card_congr (curveZeta_overEquiv f)
  have hSfin : S.Finite := by
    rw [hS]
    exact (Finset.finite_toSet _).biUnion (fun d _ => hTfin d)
  have hstep2 : Nat.card ((x : X) × Y x) = ∑ x ∈ hSfin.toFinset, Nat.card (Y x) := by
    haveI : Fintype ↥S := hSfin.fintype
    haveI : ∀ a : ↥S, Finite (Y a.1) := fun a => hYfin a.1 a.2
    have e : ((x : X) × Y x) ≃ ((a : ↥S) × Y a.1) :=
      { toFun := fun a => ⟨⟨a.1, hmem a.1 a.2⟩, a.2⟩
        invFun := fun a => ⟨a.1.1, a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => by
          obtain ⟨⟨x, hx⟩, y⟩ := a
          rfl }
    rw [Nat.card_congr e, Nat.card_sigma,
      Finset.sum_subtype hSfin.toFinset (fun x => ⟨fun hx =>
        (Set.Finite.mem_toFinset hSfin).mp hx, fun hx =>
        (Set.Finite.mem_toFinset hSfin).mpr hx⟩) (fun x => Nat.card (Y x))]
  have hstep3 : ∑ x ∈ hSfin.toFinset, Nat.card (Y x) =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by
    have hSU : hSfin.toFinset =
        (Module.finrank k K).divisors.biUnion (fun d => (hTfin d).toFinset) := by
      ext x
      rw [Set.Finite.mem_toFinset hSfin, Finset.mem_biUnion]
      constructor
      · intro hx
        rw [hS] at hx
        obtain ⟨d, hd, hxT⟩ := Set.mem_iUnion₂.mp hx
        exact ⟨d, Finset.mem_coe.mp hd, (Set.Finite.mem_toFinset (hTfin d)).mpr hxT⟩
      · rintro ⟨d, hd, hxT⟩
        rw [hS]
        exact Set.mem_iUnion₂.mpr
          ⟨d, Finset.mem_coe.mpr hd, (Set.Finite.mem_toFinset (hTfin d)).mp hxT⟩
    have hdisj : Set.PairwiseDisjoint ((Module.finrank k K).divisors : Set ℕ)
        (fun d => (hTfin d).toFinset) := by
      intro d hd d' hd' hne
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have h1 : x ∈ T d := (Set.Finite.mem_toFinset (hTfin d)).mp hx
      have h2 : x ∈ T d' := (Set.Finite.mem_toFinset (hTfin d')).mp hx'
      obtain ⟨-, hc1⟩ := h1
      obtain ⟨-, hc2⟩ := h2
      refine hne (Nat.pow_right_injective hq ?_)
      show Nat.card k ^ d = Nat.card k ^ d'
      rw [← hc1, ← hc2]
    rw [hSU, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hterm : ∀ x ∈ (hTfin d).toFinset, Nat.card (Y x) = d := by
      intro x hx
      have hxT : x ∈ T d := (Set.Finite.mem_toFinset (hTfin d)).mp hx
      obtain ⟨hxcl, hxq⟩ := hxT
      rw [Nat.card_congr (curveZeta_fiberEquiv f x)]
      exact curveZeta_natCard_fiberOfClosed f x d hxcl hxq
        (Nat.mem_divisors.mp hd).1
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 1
    rw [← Set.ncard_eq_toFinset_card (T d) (hTfin d)]
    rfl
  rw [hstep1, hstep2, hstep3]

/-- A geometric sum in the base `q ≥ 2` is at most twice its last term. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_geom (q : ℝ) (hq : 2 ≤ q) (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, q ^ b ≤ 2 * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ]
    have h0 : 0 ≤ q ^ n := by positivity
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr hq)]

/-- The sum of `√(q^b)` for `b ≤ n` is at most `2 q^n` when `q ≥ 2`. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_geom_sqrt (q : ℝ) (hq : 2 ≤ q)
    (n : ℕ) :
    ∑ b ∈ Finset.Icc 1 n, Real.sqrt (q ^ b) ≤ 2 * q ^ n := by
  have hs := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hs0 := Real.sqrt_nonneg q
  have hs1 : 1 ≤ Real.sqrt q := by nlinarith
  have hc : 2 + Real.sqrt q ≤ 2 * q := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), pow_succ, Real.sqrt_mul (by positivity)]
    have h1 : 1 ≤ q ^ n := one_le_pow₀ (by linarith)
    have hX : Real.sqrt (q ^ n) ≤ q ^ n := by
      calc Real.sqrt (q ^ n) ≤ Real.sqrt ((q ^ n) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = q ^ n := Real.sqrt_sq (by positivity)
    calc ∑ b ∈ Finset.Icc 1 n, Real.sqrt (q ^ b) + Real.sqrt (q ^ n) * Real.sqrt q
        ≤ 2 * q ^ n + q ^ n * Real.sqrt q := add_le_add ih (mul_le_mul_of_nonneg_right hX hs0)
      _ = q ^ n * (2 + Real.sqrt q) := by ring
      _ ≤ q ^ n * (2 * q) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * (q ^ n * q) := by ring

/-- Möbius inversion of the point counts, with the Weil bound as a hypothesis. -/
private theorem curveZeta_closedPointsOfDegree_bound_of_weil_aux (q g : ℝ) (P : ℕ → ℝ)
    (hq : 2 ≤ q) (hg : 0 ≤ g)
    (hW : ∀ r : ℕ, 0 < r →
      |∑ d ∈ r.divisors, (d : ℝ) * P d - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r))
    (m : ℕ) (hm : 0 < m) :
    |P m - q ^ m / m| ≤ (5 + 6 * g) * Real.sqrt (q ^ m) / m := by
  classical
  let N : ℕ → ℝ := fun r ↦ ∑ d ∈ r.divisors, (d : ℝ) * P d
  let E : ℕ → ℝ := fun r ↦ N r - (q ^ r + 1)
  have hEb : ∀ r, 0 < r → |E r| ≤ 2 * g * Real.sqrt (q ^ r) := hW
  have hsum : ∀ r > 0, ∑ i ∈ r.divisors, (((i : ℕ) : ℝ) * P i - if i = 1 then 1 else 0) =
      N r - 1 := by
    intro r hr
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    simp [hr.ne', N]
  have hinv := ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.mp hsum m hm
  have h2 : ∑ i ∈ m.divisors, ((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ) * (N i - 1) =
      (m : ℝ) * P m - if m = 1 then 1 else 0 := by
    rw [← hinv]
    simp only [zsmul_eq_mul]
    exact (Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (N b - 1))).symm
  rw [← Nat.cons_self_properDivisors hm.ne', Finset.sum_cons, Nat.div_self hm,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul] at h2
  set T := ∑ i ∈ m.properDivisors, ((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ) * (N i - 1)
    with hTdef
  have hmain : (m : ℝ) * P m - q ^ m = (if m = 1 then 1 else 0) + E m + T := by
    simp only [E]
    linarith
  have hsub : m.properDivisors ⊆ Finset.Icc 1 (m / 2) := by
    intro i hi
    obtain ⟨⟨c, hc⟩, hlt⟩ := Nat.mem_properDivisors.mp hi
    have hi0 : 0 < i := Nat.pos_of_mem_properDivisors hi
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
        omega
      · simp at hc
        omega
      · omega
    rw [Finset.mem_Icc, Nat.le_div_iff_mul_le (by norm_num)]
    exact ⟨hi0, hc ▸ Nat.mul_le_mul_left i hc2⟩
  have hhalf : q ^ (m / 2) ≤ Real.sqrt (q ^ m) := by
    calc q ^ (m / 2) = Real.sqrt ((q ^ (m / 2)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (q ^ m) := Real.sqrt_le_sqrt (by
          rw [← pow_mul]
          exact pow_le_pow_right₀ (by linarith) (by omega))
  have hT : |T| ≤ ∑ i ∈ m.properDivisors, (q ^ i + 2 * g * Real.sqrt (q ^ i)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    have hi0 : 0 < i := Nat.pos_of_mem_properDivisors hi
    have hμ : |((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hN : |N i - 1| ≤ q ^ i + 2 * g * Real.sqrt (q ^ i) := by
      have h := hEb i hi0
      calc |N i - 1| = |q ^ i + E i| := by
            congr 1
            simp only [E]
            ring
        _ ≤ |q ^ i| + |E i| := abs_add_le _ _
        _ ≤ q ^ i + 2 * g * Real.sqrt (q ^ i) := by
            rw [abs_of_nonneg (by positivity)]
            linarith
    rw [abs_mul]
    calc |((ArithmeticFunction.moebius (m / i) : ℤ) : ℝ)| * |N i - 1|
        ≤ 1 * (q ^ i + 2 * g * Real.sqrt (q ^ i)) :=
          mul_le_mul hμ hN (abs_nonneg _) zero_le_one
      _ = q ^ i + 2 * g * Real.sqrt (q ^ i) := one_mul _
  have hS1 : ∑ i ∈ m.properDivisors, q ^ i ≤ 2 * Real.sqrt (q ^ m) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans
      ((curveZeta_closedPointsOfDegree_bound_of_weil_geom q hq _).trans (by linarith))
  have hS2 : ∑ i ∈ m.properDivisors, Real.sqrt (q ^ i) ≤ 2 * Real.sqrt (q ^ m) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Real.sqrt_nonneg _).trans
      ((curveZeta_closedPointsOfDegree_bound_of_weil_geom_sqrt q hq _).trans (by linarith))
  have hsplit : ∑ i ∈ m.properDivisors, (q ^ i + 2 * g * Real.sqrt (q ^ i)) =
      ∑ i ∈ m.properDivisors, q ^ i + 2 * g * ∑ i ∈ m.properDivisors, Real.sqrt (q ^ i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hone : 1 ≤ Real.sqrt (q ^ m) := Real.one_le_sqrt.mpr (one_le_pow₀ (by linarith))
  have hite : |(if m = 1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have key : |(m : ℝ) * P m - q ^ m| ≤ (5 + 6 * g) * Real.sqrt (q ^ m) := by
    rw [hmain]
    have h3 := abs_add_three (if m = 1 then (1 : ℝ) else 0) (E m) T
    have hE := hEb m hm
    nlinarith [mul_le_mul_of_nonneg_left hS2 (by linarith : (0 : ℝ) ≤ 2 * g)]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [show P m - q ^ m / m = ((m : ℝ) * P m - q ^ m) / m by field_simp, abs_div,
    abs_of_pos hm']
  exact div_le_div_of_nonneg_right key hm'.le

/-- Paper: §14.2, p. 535. The Weil point-count estimate with genus g gives
an error constant depending only on g in the closed-point count.
Deviation: Uses the numerical Weil hypothesis and the closed-point expression
for the extension-field counts. The displayed constant is an explicit bound. -/
theorem curveZeta_closedPointsOfDegree_bound_of_weil (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (g : ℕ) :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    (∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r)) →
    ∀ m : ℕ, 0 < m → |(curveZetaClosedPointCount f m : ℝ) - q ^ m / m| ≤
      (5 + 6 * (g : ℝ)) * Real.sqrt (q ^ m) / m := by
  intro q N hW m hm
  have hq : (2 : ℝ) ≤ q := by
    have h := Finite.one_lt_card (α := k)
    show (2 : ℝ) ≤ (Nat.card k : ℝ)
    exact_mod_cast h
  exact curveZeta_closedPointsOfDegree_bound_of_weil_aux q g
    (fun d ↦ (curveZetaClosedPointCount f d : ℝ)) hq (Nat.cast_nonneg g) hW m hm

/-- The composite `Spec κ(x) → X → Spec k` is `Spec` of the structure map `k → κ(x)`. -/
private theorem curveZeta_fromSpecResidueField_comp {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecResidueField x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k _) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫ f.residueFieldMap x) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [Spec.map_comp, Category.assoc]

/-- A point `Spec K → X` through `x` lies over `k` exactly when its field map is
k-linear for the structure map `k → κ(x)`. -/
private theorem curveZeta_extensionPointCount_isOver_iff {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (K : Type u) [Field K] [Algebra k K] (φ : X.residueField x ⟶ CommRingCat.of K) :
    (Spec.map φ ≫ X.fromSpecResidueField x) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ↔
      φ.hom.comp (CommRingCat.ofHom (algebraMap k _) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫ f.residueFieldMap x).hom =
        algebraMap k K := by
  rw [Category.assoc, curveZeta_fromSpecResidueField_comp, ← Spec.map_comp,
    Spec.map_inj]
  constructor
  · intro h; exact congrArg CommRingCat.Hom.hom h
  · intro h; ext a; exact congrArg (· a) h

/-- Reduction for `curveZeta_pointCount_weil_bound`: finitely many degrees, and the `+ 1`, are
absorbed into the constant. For any real sequence `N` and `q ≥ 1`, an estimate
`|N r - q ^ r| ≤ C √(q ^ r)` for all `r ≥ r₀` gives `g : ℕ` with
`|N r - (q ^ r + 1)| ≤ 2 g √(q ^ r)` for every `r ≥ 1`. -/
private theorem curveZeta_pointCount_weil_bound_of_eventually (q : ℝ) (hq : 1 ≤ q)
    (N : ℕ → ℝ) (C : ℝ) (r₀ : ℕ)
    (h : ∀ r : ℕ, r₀ ≤ r → |N r - q ^ r| ≤ C * Real.sqrt (q ^ r)) :
    ∃ g : ℕ, ∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r) := by
  set B : ℝ := ∑ r ∈ Finset.range r₀, |N r - (q ^ r + 1)| with hBdef
  refine ⟨⌈(max C 0 + 1 + B) / 2⌉₊, fun r _ => ?_⟩
  have hs1 : 1 ≤ Real.sqrt (q ^ r) := Real.one_le_sqrt.mpr (one_le_pow₀ hq)
  have hS : 0 ≤ Real.sqrt (q ^ r) := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hg : max C 0 + 1 + B ≤ 2 * (⌈(max C 0 + 1 + B) / 2⌉₊ : ℝ) := by
    have := Nat.le_ceil ((max C 0 + 1 + B) / 2); linarith
  have hC0 := le_max_right C 0
  calc |N r - (q ^ r + 1)| ≤ (max C 0 + 1 + B) * Real.sqrt (q ^ r) := ?_
    _ ≤ _ := mul_le_mul_of_nonneg_right hg hS
  rcases lt_or_ge r r₀ with hr | hr
  · have : |N r - (q ^ r + 1)| ≤ B :=
      Finset.single_le_sum (f := fun r => |N r - (q ^ r + 1)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hr)
    nlinarith
  · have h1 := h r hr
    have h2 : |N r - (q ^ r + 1)| ≤ |N r - q ^ r| + 1 := by
      calc |N r - (q ^ r + 1)| = |(N r - q ^ r) + (-1)| := by ring_nf
        _ ≤ |N r - q ^ r| + |(-1 : ℝ)| := abs_add_le _ _
        _ = _ := by simp
    have h3 : C * Real.sqrt (q ^ r) ≤ max C 0 * Real.sqrt (q ^ r) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    nlinarith

/-- A finite field has an extension of every positive degree in its own universe (the splitting
field of `X ^ (q ^ r) - X`). -/
private theorem curveZeta_pointCount_weil_bound_exists_extension (r : ℕ) (hr : 0 < r) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Finite K),
      Module.finrank k K = r := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists k
  have := hp
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  have : NeZero r := ⟨hr.ne'⟩
  let P : Polynomial k := Polynomial.X ^ Nat.card k ^ r - Polynomial.X
  let e := Polynomial.IsSplittingField.algEquiv (FiniteField.Extension k p r) P
  have : Module.Finite k P.SplittingField := inferInstance
  refine ⟨P.SplittingField, inferInstance, inferInstance, Module.finite_of_finite k, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact FiniteField.finrank_extension k p r


/-- Reduction for `curveZeta_pointCount_weil_bound` to a point-count estimate over large
extensions: if for every finite extension `K / k` of degree at least `r₀` the number of
`k`-morphisms `Spec K → X` is within `C √#K` of `#K`, then the conclusion of
`curveZeta_pointCount_weil_bound` holds. Uses `curveZeta_extensionPointCount`. -/
private theorem curveZeta_pointCount_weil_bound_of_points (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (C : ℝ) (r₀ : ℕ)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Finite K], r₀ ≤ Module.finrank k K →
      |(Nat.card {p : Spec (.of K) ⟶ X //
          p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} : ℝ) - Nat.card K| ≤
        C * Real.sqrt (Nat.card K)) :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    ∃ g : ℕ, ∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r) := by
  intro q N
  have hq : (1 : ℝ) ≤ q := by
    have : 1 ≤ Nat.card k := Finite.one_lt_card.le
    change (1 : ℝ) ≤ (Nat.card k : ℝ)
    exact_mod_cast this
  refine curveZeta_pointCount_weil_bound_of_eventually q hq N C (max r₀ 1) fun r hr => ?_
  obtain ⟨K, _, _, _, hK⟩ :=
    curveZeta_pointCount_weil_bound_exists_extension (k := k) r (by omega)
  have hcardK : Nat.card K = Nat.card k ^ r := by
    have : Module.Finite k K := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := k), hK]
  have hN : N r = (Nat.card {p : Spec (.of K) ⟶ X //
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} : ℝ) := by
    rw [curveZeta_extensionPointCount f K, hK, Nat.cast_sum]
    exact Finset.sum_congr rfl fun d _ => (Nat.cast_mul _ _).symm
  have h1 := h K (by rw [hK]; omega)
  rw [hcardK] at h1
  rw [hN]
  push_cast at h1
  exact h1

/-- An étale chart of a smooth curve: every point has an affine neighbourhood `V` with an étale
ring map `k[t] → Γ(X, V)` extending the `k`-algebra structure. -/
private theorem curveZeta_pointCount_weil_bound_chart (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (g : Polynomial k →+* Γ(X, V)),
      g.Etale ∧ ∀ a : k, g (Polynomial.C a) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V le_top).hom a := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hUtop : U = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    rw [Subsingleton.elim z (f x)]
    exact e hx
  subst hUtop
  obtain ⟨g, hgC, hg⟩ := RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial hf
  let φ : Γ(Spec (.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let ι : Polynomial k ≃+* MvPolynomial (Fin 1) Γ(Spec (.of k), ⊤) :=
    (Polynomial.mapEquiv φ.symm).trans
      ((MvPolynomial.finSuccEquiv Γ(Spec (.of k), ⊤) 0).trans
        (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv Γ(Spec (.of k), ⊤) (Fin 0)))).symm.toRingEquiv
  refine ⟨V, hV, hx, g.comp ι.toRingHom, RingHom.Etale.respectsIso.right g ι hg, fun a => ?_⟩
  have h1 : ι (Polynomial.C a) = MvPolynomial.C (φ.symm a) := by
    apply ι.symm.injective
    rw [RingEquiv.symm_apply_apply]
    show Polynomial.C a = (Polynomial.mapEquiv φ.symm).symm
      ((Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv _ (Fin 0)))
        ((MvPolynomial.finSuccEquiv Γ(Spec (.of k), ⊤) 0) (MvPolynomial.C (φ.symm a))))
    have hC : (MvPolynomial.finSuccEquiv Γ(Spec (.of k), ⊤) 0) (MvPolynomial.C (φ.symm a)) =
        Polynomial.C (MvPolynomial.C (φ.symm a)) := by
      have h := RingHom.congr_fun
        (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := Γ(Spec (.of k), ⊤)) 0) (φ.symm a)
      have h2 := congrArg (MvPolynomial.finSuccEquiv Γ(Spec (.of k), ⊤) 0) h
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
        AlgEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [hC]
    simp
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1]
  rw [← RingHom.comp_apply, hgC]
  rfl

/-- The affine charts of a smooth curve have Krull dimension at most one. -/
private theorem curveZeta_pointCount_weil_bound_dim (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] (x : X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ ringKrullDim Γ(X, W) ≤ 1 := by
  obtain ⟨V, hV, hx, g, hg, -⟩ := curveZeta_pointCount_weil_bound_chart f x
  refine ⟨V, hV, hx, ?_⟩
  algebraize [g]
  have h1 : ringKrullDim Γ(X, V) ≤ ringKrullDim (Polynomial k) := by
    refine Order.krullDim_le_of_strictMono
      (fun q : PrimeSpectrum Γ(X, V) ↦ PrimeSpectrum.comap (algebraMap (Polynomial k) _) q)
      fun a b hab ↦ ?_
    have hle : a.asIdeal ≤ b.asIdeal := hab.le
    refine lt_of_le_of_ne (show a.asIdeal.comap (algebraMap (Polynomial k) _) ≤ b.asIdeal.comap _
      from Ideal.comap_mono hle) fun h ↦ hab.ne ?_
    ext1
    exact Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Polynomial k) a.asIdeal b.asIdeal hle
      (congrArg PrimeSpectrum.asIdeal h)
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
  simpa using h1

/-- The points over `k` lying over a finite set of points of `X` are bounded independently of the
field of values: a point of `X` with residue field `κ(x)` carries at most `[κ(x) : k]` of them. -/
private theorem curveZeta_pointCount_weil_bound_outside (f : X ⟶ Spec (.of k)) (S : Set X)
    (hS : S.Finite) :
    ∃ D : ℕ, ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
        p (IsLocalRing.closedPoint K) ∈ S} ≤ D := by
  classical
  let alg : ∀ x : X, k →+* X.residueField x := fun x => (CommRingCat.ofHom (algebraMap k _) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫ f.residueFieldMap x).hom
  let T := hS.toFinset
  refine ⟨∑ x ∈ T, @Module.finrank k (X.residueField x) _ _ (alg x).toAlgebra.toModule,
    fun K _ _ _ => ?_⟩
  let G : X → Type u := fun x => {φ : X.residueField x ⟶ CommRingCat.of K //
    φ.hom.comp (alg x) = algebraMap k K}
  have hG : ∀ x, Finite (G x) ∧ Nat.card (G x) ≤
      @Module.finrank k (X.residueField x) _ _ (alg x).toAlgebra.toModule := by
    intro x
    letI := (alg x).toAlgebra
    let e : G x ≃ (X.residueField x →ₐ[k] K) :=
      { toFun := fun φ ↦ { φ.1.hom with commutes' := fun r ↦ congrArg (· r) φ.2 }
        invFun := fun ψ ↦ ⟨CommRingCat.ofHom ψ.toRingHom, RingHom.ext ψ.commutes⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [Nat.card_congr e]
    rcases isEmpty_or_nonempty (X.residueField x →ₐ[k] K) with h | h
    · exact ⟨e.finite_iff.2 inferInstance, by simp⟩
    · obtain ⟨ψ⟩ := h
      have : Finite (X.residueField x) := Finite.of_injective _ ψ.toRingHom.injective
      have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
      exact ⟨e.finite_iff.2 inferInstance, card_algHom_le_finrank k _ K⟩
  let Ψ : {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
      p (IsLocalRing.closedPoint K) ∈ S} → Σ x : T, G x := fun p =>
    ⟨⟨(Scheme.SpecToEquivOfField K X p.1).1, by
        rw [Set.Finite.mem_toFinset]; exact p.2.2⟩,
      ⟨(Scheme.SpecToEquivOfField K X p.1).2, by
        have h := p.2.1
        conv_lhs at h => rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply p.1]
        exact (curveZeta_extensionPointCount_isOver_iff f _ K _).1 h⟩⟩
  have hΨ : Function.Injective Ψ := by
    intro p p' h
    apply Subtype.ext
    apply (Scheme.SpecToEquivOfField K X).injective
    have h1 := congrArg (fun z : Σ x : T, G x =>
      (⟨z.1.1, z.2.1⟩ : Σ x : X, X.residueField x ⟶ CommRingCat.of K)) h
    exact h1
  have : ∀ x : T, Finite (G x) := fun x => (hG x).1
  calc Nat.card _ ≤ Nat.card (Σ x : T, G x) := Nat.card_le_card_of_injective _ hΨ
    _ = ∑ x : T, Nat.card (G x) := Nat.card_sigma
    _ ≤ ∑ x : T, @Module.finrank k (X.residueField x) _ _ (alg x).toAlgebra.toModule :=
        Finset.sum_le_sum fun x _ => (hG x).2
    _ = _ := Finset.sum_coe_sort T (fun x => @Module.finrank k (X.residueField x) _ _
        (alg x).toAlgebra.toModule)

/-- **Weil's bound for the curve**, in the form required by
`curveZeta_pointCount_weil_bound_of_points`: points over large finite extensions `K` number
`#K + O(√#K)`. An étale chart `V` gives, through `RiemannMasullo.WeilBound.weil_etale`, the bound on
a basic open `V' ⊆ V`; the finitely many points outside `V'` contribute a bounded amount. -/
private theorem curveZeta_pointCount_weil_bound_main (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    ∃ (C : ℝ) (r₀ : ℕ), ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      r₀ ≤ Module.finrank k K →
      |(Nat.card {p : Spec (.of K) ⟶ X //
          p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} : ℝ) - Nat.card K| ≤
        C * Real.sqrt (Nat.card K) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  -- `X` and its base change to `k̄` are integral
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
  have hXint : IsIntegral X := isIntegral_of_smoothOfRelativeDimension_one f
  set L := AlgebraicClosure k
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : ConnectedSpace ↥(Limits.pullback f g : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (Limits.pullback.snd f g)
  have : IsIntegral (Limits.pullback f g : Scheme.{u}) :=
    isIntegral_of_smoothOfRelativeDimension_one (Limits.pullback.snd f g)
  -- an étale chart
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨V, hV, hx₀, φ, hφ, hφC⟩ := curveZeta_pointCount_weil_bound_chart f x₀
  have : Nonempty V := ⟨⟨x₀, hx₀⟩⟩
  let := sectionsAlgebra f V
  let : Algebra (Polynomial k) Γ(X, V) := φ.toAlgebra
  have : IsScalarTower k (Polynomial k) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (hφC a).symm
  have : Algebra.Etale (Polynomial k) Γ(X, V) := hφ
  have : IsDomain (TensorProduct k Γ(X, V) L) := isDomain_tensor_of_isIntegral_pullback f hV
  obtain ⟨s, hs0, C, n₀, hW⟩ := RiemannMasullo.WeilBound.weil_etale.{u, u, u} (k := k) (B := Γ(X, V))
  -- the basic open `V'`
  set s' : Γ(X, V) := algebraMap (Polynomial k) Γ(X, V) s
  have hs'0 : s' ≠ 0 :=
    (map_ne_zero_iff _ RiemannMasullo.WeilBound.algebraMap_injective_of_etale).2 hs0
  set V' := X.basicOpen s'
  have hV' : IsAffineOpen V' := hV.basicOpen s'
  have hV'ne : (V' : Set X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hs'0
    rw [← basicOpen_eq_bot_iff]
    exact SetLike.coe_injective (h.trans TopologicalSpace.Opens.coe_bot.symm)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcompl : ((V' : Set X)ᶜ).Finite :=
    finite_compl_of_ringKrullDim_le_one (curveZeta_pointCount_weil_bound_dim f) hV'ne
  obtain ⟨D, hD⟩ := curveZeta_pointCount_weil_bound_outside f _ hcompl
  -- `Γ(X, V')` is `Γ(X, V)[1/s']`
  have hloc := hV.isLocalization_basicOpen s'
  let e : Localization.Away s' ≃ₐ[Γ(X, V)] Γ(X, V') :=
    IsLocalization.algEquiv (Submonoid.powers s') _ _
  let := sectionsAlgebra f V'
  let ek : Localization.Away s' ≃ₐ[k] Γ(X, V') :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun a => by
      rw [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s')]
      have hres : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V le_top ≫
          X.presheaf.map (homOfLE <| X.basicOpen_le s' : V' ⟶ V).op =
          (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V' le_top :=
        congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·)
          (Scheme.Hom.appLE_map f le_top (homOfLE <| X.basicOpen_le s' : V' ⟶ V).op)
      have := congrArg (fun h => CommRingCat.Hom.hom h a) hres
      simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
      exact this
  refine ⟨C + D, n₀, fun K _ _ _ hK => ?_⟩
  have : Fintype K := Fintype.ofFinite K
  have h1 := hW K hK
  have hcount : Nat.card (Localization.Away s' →ₐ[k] K) = Nat.card (Γ(X, V') →ₐ[k] K) :=
    Nat.card_congr (AlgEquiv.arrowCongr ek AlgEquiv.refl)
  have hin := card_points_affineOpen f hV' K
  have hout := hD K
  have : Finite (Spec (.of K) ⟶ X) := finite_spec_hom f K
  set P : (Spec (.of K) ⟶ X) → Prop := fun p => p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))
  set Q : (Spec (.of K) ⟶ X) → Prop := fun p => p (IsLocalRing.closedPoint K) ∈ V'
  have hsplit : Nat.card {p // P p} = Nat.card {p // P p ∧ Q p} + Nat.card {p // P p ∧ ¬ Q p} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr ((Equiv.sumCompl (fun p : {p // P p} => Q p.1)).symm.trans
      (Equiv.sumCongr (Equiv.subtypeSubtypeEquivSubtypeInter P Q)
        (Equiv.subtypeSubtypeEquivSubtypeInter P (fun p => ¬ Q p))))
  have hNin : (Nat.card {p // P p ∧ Q p} : ℝ) = Nat.card (Localization.Away s' →ₐ[k] K) := by
    rw [hcount]; exact_mod_cast hin
  have hNout : (Nat.card {p // P p ∧ ¬ Q p} : ℝ) ≤ D := by exact_mod_cast hout
  have hNout0 : (0 : ℝ) ≤ Nat.card {p // P p ∧ ¬ Q p} := by positivity
  have hsq : (1 : ℝ) ≤ Real.sqrt (Nat.card K) := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  rw [Nat.card_eq_fintype_card (α := K)] at hsq ⊢
  change |(Nat.card {p // P p} : ℝ) - _| ≤ _
  rw [hsplit, Nat.cast_add, hNin]
  calc |(Nat.card (Localization.Away s' →ₐ[k] K) : ℝ) + Nat.card {p // P p ∧ ¬ Q p} -
        Fintype.card K|
      ≤ |(Nat.card (Localization.Away s' →ₐ[k] K) : ℝ) - Fintype.card K| +
          Nat.card {p // P p ∧ ¬ Q p} := by
        rw [show (Nat.card (Localization.Away s' →ₐ[k] K) : ℝ) + Nat.card {p // P p ∧ ¬ Q p} -
          Fintype.card K = ((Nat.card (Localization.Away s' →ₐ[k] K) : ℝ) - Fintype.card K) +
          Nat.card {p // P p ∧ ¬ Q p} by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hNout0]
    _ ≤ C * Real.sqrt (Fintype.card K) + D * Real.sqrt (Fintype.card K) := by
        gcongr
        exact hNout.trans (le_mul_of_one_le_right (by positivity) hsq)
    _ = (C + D) * Real.sqrt (Fintype.card K) := by ring

/-- Paper: §14.2, p. 535 (the Weil bound the paper cites from [TsV, Ch. 2.3, (2.3.2), p. 177]).
The Hasse–Weil estimate: there is `g : ℕ` (the genus of the curve) such that for every `r ≥ 1`
the number `N r = ∑_{d ∣ r} d B_d` satisfies `|N r - (q^r + 1)| ≤ 2 g q^{r/2}`, where `q = #k`
and `B_d = curveZetaClosedPointCount f d` is the number of closed points of degree `d`.
By `curveZeta_extensionPointCount`, `N r` is the number of points of the curve over the
extension of `k` of degree `r`, so this is Weil's theorem (the Riemann hypothesis for
smooth projective geometrically connected curves over finite fields), which is not in Mathlib.
Deviation: the genus is only asserted to exist, not defined; the paper uses the genus of the
curve, for which the bound holds. -/
theorem curveZeta_pointCount_weil_bound (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    ∃ g : ℕ, ∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r) := by
  obtain ⟨C, r₀, h⟩ := curveZeta_pointCount_weil_bound_main f
  exact curveZeta_pointCount_weil_bound_of_points f C r₀ fun K _ _ _ hK => h K hK

/-- Paper: §14.2, p. 535. The number of degree-m closed points is
q^m/m with error O(q^(m/2)/m) as m tends to infinity.
Deviation: The Big-O constant here is for the given curve. The paper also
specifies uniformity in the curve through its genus. -/
theorem curveZeta_closedPointsOfDegree_asymptotic (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    (fun m : ℕ ↦ (curveZetaClosedPointCount f m : ℝ) - q ^ m / m) =O[Filter.atTop]
      (fun m : ℕ ↦ Real.sqrt (q ^ m) / m) := by
  intro q
  obtain ⟨g, hW⟩ := curveZeta_pointCount_weil_bound f
  refine Asymptotics.IsBigO.of_bound (5 + 6 * (g : ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have h := curveZeta_closedPointsOfDegree_bound_of_weil f g hW m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ Real.sqrt (q ^ m) / m by positivity), ← mul_div_assoc]
  exact h

/-- Paper: (14.2.0.1), p. 534. On `Re(s) > 1` the finite products over closed
points converge to the zeta Euler product.
Deviation: `HasProd` asserts convergence of the product in the display. -/
theorem hasProd_curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun x : closedPoints X ↦ curveZetaEulerFactor x s.val)
      (curveZetaEulerProduct f s) := by
  have h := Complex.multipliable_one_add_of_summable
    (summable_curveZetaEulerFactor_sub_one f s).of_norm
  simp only [add_sub_cancel] at h
  exact h.hasProd

-- TODO(paper-gap): The comparison on p. 535 refers to the missing Theorem
-- 13.3.1.2. Equation (5.3.1.5) supplies a finite-place principal-value
-- operator. The function-field completion, convergence in the topology of
-- uniform convergence on bounded sets, and trace identity are unspecified.

-- TODO(paper-gap): The gonality equality on p. 535 fails for the Hermitian
-- quartic y³ + y = x⁴ over 𝔽₉. Its genus is three and projection to x has
-- degree three. It is maximal and its sole Frobenius eigenvalue has
-- multiplicity six. For g ≥ 2 the general bound gon_k(X) ≤ g + 1 < 2g
-- follows by Riemann–Roch at a rational point. For g = 1 the strict
-- inequality also fails, since gon_k(E) = 2 = 2g. The printed equality
-- and strict inequality need curve-genus and gonality interfaces.

-- TODO(paper-gap): The supersingular example on p. 536 needs a choice of
-- curve with equal Frobenius eigenvalues. Over 𝔽₉, y² = x³ − x has numerator
-- (1 + 3T)². The supersingular curve y² = x³ + (1 + i)x with i² = −1 has
-- numerator 1 + 9T² and gives simple zeros for the quadratic cover's L-function.

-- TODO(paper-gap): §14.3, p. 536 gives n[F : ℚ] as a proposed multiplicity
-- bound for generic zeros. Page 533 identifies these as non-central zeros.
-- A unitary imaginary norm twist translates the zeros in the s-plane.
-- The higher-rank centering convention and argument need to be supplied
-- before stating the bound (ERRATA R24 and M43).

end RiemannMasullo
