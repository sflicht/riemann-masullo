module

public import Mathlib.NumberTheory.PrimeCounting
public import RiemannMasullo.Ch11_ShellStructure.Sec2b

import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch11_ShellStructure.Sec1a

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Orbital kernels and orbital traces

Masullo, §11.3, pp. 491–496. The divisorial filtration is on ideles.
All archimedean places are implicit in the finite-place base set.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "N𝔽" => (ideleNorm F).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "above(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "resChar(" v ")" => Rat.HeightOneSpectrum.natGenerator ((v).under (𝓞 ℚ))

/-- Paper: (11.3.1.1), p. 492. For a base with trivial S-integer Picard group and
an unramified outside character, each homogeneous polar theta function has a
representative obtained by adjoining the integer indicators to an S-local test.
Deviation: The printed condition that S contains the places ramified over ℚ is
not used by Theorem 6.2.1.1(2) and is omitted. As on the page, the S-local test
is not asserted to have zero polar values. -/
theorem exists_divisorialThetaRepresentative (S : Finset V)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (f : adelePolarSubspace F) :
    ∃ fS : ℬₛ(S), homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S fS) =
      homogeneousAdelicTheta ω f.val := by
  obtain ⟨e, he⟩ :=
    sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) _hPic (ω := ω) _hω
  have hsurj : Function.Surjective (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) _hω) := by
    rw [← he]
    exact e.surjective
  obtain ⟨y, hy⟩ := hsurj ((LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ f.val)
  obtain ⟨fS, hfS⟩ := Submodule.mkQ_surjective
    (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S
      (sLocalNormOneCharacter (F := F) S ω _hω))) y
  rw [← hfS] at hy
  refine ⟨fS, ?_⟩
  refine (globalHomogeneousThetaSpace_mk_eq_iff (F := F) ω _ _).mp ?_
  have h1 : (homogeneousAdelicThetaLinearMap F ω).ker.mkQ ((sAdeleSchwartzToGlobal F S) fS)
      = (homogeneousAdelicThetaLinearMap F ω).ker.mkQ (f.val) := by
    rw [← sLocalHomogeneousThetaToGlobal_mk (F := F) (S := S) _hω fS]
    exact hy
  simpa only [Submodule.mkQ_apply] using h1

/-- Paper: §11.3.1.1, p. 492, before (11.3.1.2). The local factor is the
indicator of ideles whose component at the chosen finite place is a unit.
Deviation: The unrestricted tensor coordinates contribute the constant one. -/
def divisorialLocalIndicator (v : V) (g : I𝔽) : ℂ :=
  if Valued.v (g.val.2 v) = 1 then 1 else 0

/-- Paper: §11.3.1.1, p. 492. The local indicator detects precisely the
integer units in the chosen coordinate. -/
theorem divisorialLocalIndicator_eq_one_iff (v : V) (g : I𝔽) :
    divisorialLocalIndicator v g = 1 ↔ Valued.v (g.val.2 v) = 1 := by
  unfold divisorialLocalIndicator
  split_ifs with h <;> simp [h]

/-- Paper: (11.3.1.2), p. 492. Multiply the local unit indicators at the
selected finite places. The base set enters through the choice of these places. -/
def divisorialIndicator (T : Finset V) (g : I𝔽) : ℂ :=
  ∏ v ∈ T, divisorialLocalIndicator v g

/-- Paper: (11.3.1.2), p. 492. For a singleton the product recovers the local
indicator. -/
theorem divisorialIndicator_singleton (v : V) (g : I𝔽) :
    divisorialIndicator {v} g = divisorialLocalIndicator v g := by
  simp [divisorialIndicator]

variable (F) in
/-- Paper: §11.3.1.1, p. 492, after (11.3.1.2). The divisorial stratum imposes
the local unit condition at each selected finite place.
Deviation: The ambient set on the right is the full idele group. -/
def divisorialStratum (T : Finset V) : Set I𝔽 :=
  {g | ∀ v ∈ T, Valued.v (g.val.2 v) = 1}

/-- Paper: §11.3.1.1, pp. 492–493. The finite product of local indicators
is the indicator of the stratum. -/
theorem divisorialIndicator_eq_indicator (T : Finset V) :
    divisorialIndicator T = (divisorialStratum F T).indicator (fun _ ↦ 1) := by
  ext g
  by_cases h : g ∈ divisorialStratum F T
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_eq_one fun v hv ↦ by simp [divisorialLocalIndicator, h v hv]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨v, hv, hne⟩ : ∃ v ∈ T, ¬ Valued.v (g.val.2 v) = 1 := by
      simpa [divisorialStratum] using h
    exact Finset.prod_eq_zero hv (by simp [divisorialLocalIndicator, hne])

/-- Paper: §11.3.1.1, p. 492. Every divisorial stratum is open and closed. -/
theorem isClopen_divisorialStratum (T : Finset V) :
    IsClopen (divisorialStratum F T) := by
  have h : divisorialStratum F T = ⋂ v ∈ T, {g : I𝔽 | Valued.v (g.val.2 v) = 1} := by
    ext g; simp [divisorialStratum]
  rw [h]
  refine isClopen_biInter_finset fun v _ ↦ ?_
  have hc : Continuous fun g : I𝔽 ↦ g.val.2 v :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hs : IsClopen {x : v.adicCompletion F | Valued.v.restrict x = 1} :=
    Valued.isClopen_sphere _ one_ne_zero
  simp only [Valuation.restrict_eq_one_iff] at hs
  exact hs.preimage hc

/-- Paper: §11.3.1.1, pp. 492–493. The difference of two nested strata consists
of ideles satisfying the old conditions and failing a condition at some new place.
The failure of a unit condition is the union of the nonzero valuation classes. -/
theorem divisorialStratum_sdiff (T U : Finset V) (hTU : T ⊆ U) :
    divisorialStratum F T \ divisorialStratum F U =
      ⋃ v ∈ U \ T, {g ∈ divisorialStratum F T | Valued.v (g.val.2 v) ≠ 1} := by
  classical
  ext g
  simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_sdiff]
  constructor
  · rintro ⟨hT, hU⟩
    change ¬ ∀ v ∈ U, Valued.v (g.val.2 v) = 1 at hU
    push_neg at hU
    obtain ⟨v, hvU, hv⟩ := hU
    exact ⟨v, ⟨hvU, fun hvT ↦ hv (hT v hvT)⟩, hT, hv⟩
  · rintro ⟨v, ⟨hvU, _⟩, hT, hv⟩
    exact ⟨hT, fun hU ↦ hv (hU v hvU)⟩

private theorem primaryDivisorial_infinite (S : Finset V) :
    (setOf (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v)))).Infinite := by
  have := Nat.infinite_setOf_prime.diff (S.image (fun v ↦ resChar(v))).finite_toSet
  refine this.mono ?_
  intro p hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- Paper: §11.3.1.1, pp. 492–493. The sequence of rational primes omitting the
residue characteristics represented in the finite base consists of primes. -/
theorem primaryDivisorialPrime_isPrime (S : Finset V) (k : ℕ) :
    (Nat.nth (fun p ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) k).Prime :=
  (Nat.nth_mem_of_infinite (primaryDivisorial_infinite S) k).1

/-- Paper: §11.3.1.1, p. 493. The rational prime for the next primary step is
selected in increasing order.
Deviation: Skip the residue characteristics in the base S as required by (11.3.1.2). -/
def primaryDivisorialPrime (S : Finset V) (k : ℕ) : Vℚ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨_, primaryDivisorialPrime_isPrime S k⟩

/-- Paper: §11.3.1.1, p. 493. With no excluded primes the first step uses the
prime 2. -/
theorem primaryDivisorialPrime_empty_zero :
    primaryDivisorialPrime (∅ : Finset V) 0 =
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩ := by
  unfold primaryDivisorialPrime
  refine congrArg Rat.HeightOneSpectrum.primesEquiv.symm (Subtype.ext ?_)
  show Nat.nth _ 0 = 2
  rw [Nat.nth_zero]
  simp only [Finset.image_empty, Finset.notMem_empty, not_false_eq_true, and_true]
  exact le_antisymm (Nat.sInf_le Nat.prime_two)
    (le_csInf ⟨2, Nat.prime_two⟩ fun p hp ↦ hp.two_le)

variable (F) in
/-- Paper: §11.3.1.1, p. 493. The kth primary place set takes the full fibres
over the first k rational primes of the sequence outside the base. -/
def primaryDivisorialPlaces (S : Finset V) (k : ℕ) : Finset V :=
  (Finset.range k).biUnion (fun j ↦ above(primaryDivisorialPrime S j))

/-- Paper: §11.3.1.1, p. 493. The next step adds precisely the places over the
next rational prime. -/
theorem primaryDivisorialPlaces_succ (S : Finset V) (k : ℕ) :
    primaryDivisorialPlaces F S (k + 1) =
      primaryDivisorialPlaces F S k ∪ above(primaryDivisorialPrime S k) := by
  simp only [primaryDivisorialPlaces, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- Paper: §11.3.1.1, p. 493. Every later packet set contains the earlier packets. -/
theorem primaryDivisorialPlaces_mono (S : Finset V) : Monotone (primaryDivisorialPlaces F S) :=
  monotone_nat_of_le_succ fun k ↦ by
    rw [primaryDivisorialPlaces_succ]
    exact Finset.subset_union_left

private theorem primaryDivisorialPrime_eq_iff (S : Finset V) (k : ℕ) (p : Vℚ) :
    primaryDivisorialPrime S k = p ↔
      Rat.HeightOneSpectrum.natGenerator p =
        Nat.nth (fun p ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) k := by
  unfold primaryDivisorialPrime
  constructor
  · rintro rfl
    exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _)
  · intro h
    exact Rat.HeightOneSpectrum.primesEquiv.symm_apply_eq.2 (Subtype.ext h.symm)

/-- Paper: §11.3.1.1, p. 493. Together the indices exhaust the finite places
outside a saturated base. -/
theorem iUnion_primaryDivisorialPlaces (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋃ k, (primaryDivisorialPlaces F S k : Set V)) = (S : Set V)ᶜ := by
  ext w
  simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_compl_iff, primaryDivisorialPlaces,
    Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, j, hj, hw⟩ hwS
    have hw' : w.under (𝓞 ℚ) = primaryDivisorialPrime S j := by
      simpa [Set.Finite.mem_toFinset] using hw
    have h1 := (primaryDivisorialPrime_eq_iff S j _).1 hw'.symm
    have h2 := (Nat.nth_mem_of_infinite (primaryDivisorial_infinite S) j).2
    have h3 : Rat.HeightOneSpectrum.natGenerator (w.under (𝓞 ℚ)) ∈
        S.image (fun v ↦ resChar(v)) := Finset.mem_image.2 ⟨w, hwS, rfl⟩
    rw [h1] at h3
    exact h2 h3
  · intro hwS
    have hq : (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) (resChar(w)) := by
      refine ⟨Rat.HeightOneSpectrum.prime_natGenerator _, fun hin ↦ ?_⟩
      obtain ⟨v, hv, hvq⟩ := Finset.mem_image.1 hin
      apply hwS
      apply _hS v hv w
      exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hvq.symm)
    have hq' : resChar(w) ∈ Set.ofPred
        (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) := hq
    obtain ⟨k, hk⟩ := Nat.subset_range_nth hq'
    refine ⟨k + 1, k, by omega, ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ((primaryDivisorialPrime_eq_iff S k _).2 hk.symm).symm

/-- Paper: §11.3.1.1, p. 493. An idele with unit components at every place over
the chosen rational primes has unit norm components at those primes.
Deviation: The printed reverse inclusion fails when local valuations cancel above
a split prime. -/
theorem relativeIdeleNormRat_mem_divisorialStratum
    (T : Finset Vℚ) :
    divisorialStratum F (T.biUnion (fun p ↦ above(p))) ⊆
      (relativeIdeleNormRat F) ⁻¹' divisorialStratum ℚ T := by
  have hQ (v : Vℚ) (x : v.adicCompletion ℚ) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
    rw [FinitePlace.norm_def, NNReal.coe_eq_one,
      WithZeroMulInt.toNNReal_eq_one_iff _ _ (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']
  have hF (v : V) (x : v.adicCompletion F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
    rw [FinitePlace.norm_def, NNReal.coe_eq_one,
      WithZeroMulInt.toNNReal_eq_one_iff _ _ (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']
  intro g hg p hp
  refine (hQ p _).1 ?_
  refine (rationalAdeleNorm_finitePlace F p g.val).trans ?_
  refine finprod_eq_one_of_forall_eq_one fun w ↦ ?_
  rw [finprod_eq_if]
  split_ifs with hw
  · exact (hF w _).2 (hg w (Finset.mem_biUnion.2
      ⟨p, hp, (finite_nuclearityPlacesAbove p).mem_toFinset.2 hw⟩))
  · rfl

section DivisorialIndicatorPrincipalValue

/-- The global inclusion of an S-local test keeps its value at zero.
Copied from the private `adelePrincipalValue_mem_polarSubspace_toGlobal_zero` in
`RiemannMasullo/Ch11_ShellStructure/Sec1b.lean`. -/
private theorem sec3_toGlobal_zero (S : Finset V) (k : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S k (Multiplicative.ofAdd 0) = k (Multiplicative.ofAdd 0) := by
  rw [sAdeleSchwartzToGlobal_apply, if_pos fun w _ ↦ (w.adicCompletionIntegers F).zero_mem,
    map_zero]

open scoped TensorProduct in
/-- Through a stage containing the selected places, the global principal value of an
inserted test is the insertion of the S-local principal value.
Copied from the private `adelePrincipalValue_mem_polarSubspace_toGlobal_comm` in
`RiemannMasullo/Ch11_ShellStructure/Sec1b.lean`. -/
private theorem sec3_toGlobal_comm {S T : Finset V}
    (hTS : T ⊆ S) (k₀ : ℬₛ(S)) (hk₀ : k₀ (Multiplicative.ofAdd 0) = 1) (k : ℬₛ(S)) :
    adelePrincipalValue F T (sAdeleSchwartzToGlobal F S k) =
      sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F hTS k) := by
  let Tl := SchwartzBruhat (Multiplicative (FiniteAdeleTail F S))
  let e := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleTailSchwartz_inductiveTensor_equiv F S).choose_spec
  let ev : ℬₛ(S) →ₗ[ℂ] ℂ :=
    { toFun := fun a ↦ a (Multiplicative.ofAdd 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : ℬₛ(S) ⊗[ℂ] Tl →ₗ[ℂ] Tl := TensorProduct.lift ((LinearMap.lsmul ℂ Tl).comp ev)
  let c : Tl := L (e.symm (sAdeleSchwartzToGlobal F S k₀))
  have hc (y : FiniteAdeleTail F S) : c (Multiplicative.ofAdd y) =
      if ∀ w, y w ∈ w.val.adicCompletionIntegers F then 1 else 0 := by
    let f : ∀ w : V, w.adicCompletion F := fun w ↦ if h : w ∈ S then 0 else y ⟨w, h⟩
    have hf : ∀ᶠ w in Filter.cofinite, f w ∈ w.adicCompletionIntegers F := by
      filter_upwards [S.eventually_cofinite_notMem, Filter.eventually_comap.mp
        (y.2.filter_mono (Filter.comap_cofinite_le Subtype.val))] with w hw h
      simp only [f, dif_neg hw]
      exact h ⟨w, hw⟩ rfl
    let z : FiniteAdeleRing (𝓞 F) F := ⟨f, hf⟩
    let x : AdeleRing (𝓞 F) F := (0, z)
    have hx (w : V) (hw : w ∉ S) : x.2 w = y ⟨w, hw⟩ := dif_neg hw
    have hp : adeleProjection F S x = 0 :=
      Prod.ext rfl (funext fun w ↦ (dif_pos w.2 : f w.val = 0))
    have ht : finiteAdeleTailProjection F S x.2 = y := by
      apply RestrictedProduct.ext
      intro w
      exact dif_neg w.2
    let evy : Tl →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd y)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    let evx : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) →ₗ[ℂ] ℂ :=
      { toFun := fun b ↦ b (Multiplicative.ofAdd x)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have key : evy ∘ₗ L = evx ∘ₗ (e.toLinearMap : InductiveTensor ℬₛ(S) Tl →ₗ[ℂ] _) := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change (a (Multiplicative.ofAdd 0) • b) (Multiplicative.ofAdd y) =
        e (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x)
      rw [he a b x, hp, ht]
      rfl
    have h2 : c (Multiplicative.ofAdd y) =
        sAdeleSchwartzToGlobal F S k₀ (Multiplicative.ofAdd x) :=
      (LinearMap.congr_fun key (e.symm (sAdeleSchwartzToGlobal F S k₀))).trans
        (congrArg (fun φ : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ↦
          φ (Multiplicative.ofAdd x)) (e.apply_symm_apply _))
    rw [h2, sAdeleSchwartzToGlobal_apply, hp, hk₀]
    by_cases hy : ∀ w, y w ∈ w.val.adicCompletionIntegers F
    · rw [if_pos hy, if_pos fun w hw ↦ by rw [hx w hw]; exact hy ⟨w, hw⟩]
    · rw [if_neg hy, if_neg fun h ↦ hy fun w ↦ by rw [← hx w.val w.2]; exact h w.val w.2]
  have hslice (a : ℬₛ(S)) : e (a ⊗ₜ[ℂ] c) = sAdeleSchwartzToGlobal F S a := by
    apply Subtype.ext
    funext x
    change e (a ⊗ₜ[ℂ] c) (Multiplicative.ofAdd x.toAdd) =
      sAdeleSchwartzToGlobal F S a (Multiplicative.ofAdd x.toAdd)
    rw [he a c x.toAdd, hc, sAdeleSchwartzToGlobal_apply]
    by_cases hx : ∀ w : V, w ∉ S → x.toAdd.2 w ∈ w.adicCompletionIntegers F
    · rw [if_pos hx, if_pos (show ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun w ↦ hx w.val w.2), mul_one]
    · rw [if_neg hx, if_neg (show ¬ ∀ w : {w : V // w ∉ S},
        finiteAdeleTailProjection F S x.toAdd.2 w ∈ w.val.adicCompletionIntegers F from
          fun h ↦ hx fun w hw ↦ h ⟨w, hw⟩), mul_zero]
  rw [← hslice k, ← hslice (sAdelePrincipalValue F hTS k)]
  exact adelePrincipalValue_tmul hTS k c

/-- Every stage containing a fixed finite set carries a test with value one at zero: the
transition of an S-local preimage of the trivial adelic Gaussian, rescaled. -/
private theorem sec3_exists_test_one :
    ∃ S₂ : Finset V, ∀ (R : Finset V), S₂ ⊆ R →
      ∃ k₀ : ℬₛ(R), k₀ (Multiplicative.ofAdd 0) = 1 := by
  obtain ⟨S₂, h₂, hh₂⟩ := sAdeleSchwartzToGlobal_exhaustive F
    (adelicStandardGaussian (F := F) (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)))
  refine ⟨S₂, fun R hS₂ ↦ ?_⟩
  have hk₂ : sAdeleSchwartzTransition F hS₂ h₂ (Multiplicative.ofAdd 0) ≠ 0 := by
    have h2' : sAdeleSchwartzToGlobal F _ (sAdeleSchwartzTransition F hS₂ h₂) =
        sAdeleSchwartzToGlobal F S₂ h₂ :=
      LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hS₂) h₂
    rw [← sec3_toGlobal_zero, h2', hh₂, adelicStandardGaussian_trivial_zero]
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  exact ⟨(sAdeleSchwartzTransition F hS₂ h₂ (Multiplicative.ofAdd 0))⁻¹ •
      sAdeleSchwartzTransition F hS₂ h₂, inv_mul_cancel₀ hk₂⟩

/-- The trivial finite standard Gaussian is the indicator of the integer ring. -/
private theorem sec3_finiteStandardGaussian_apply (v : V) (y : v.adicCompletion F) :
    finiteStandardGaussian v 1 (Multiplicative.ofAdd y) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) y := by
  change finiteStandardGaussianValue v 1 y = _
  unfold finiteStandardGaussianValue
  exact ite_eq_left fun u _ ↦ rfl

/-- The local principal value of the integer-ring indicator is the integer-unit indicator:
the indicator is invariant under the integer units, so the principal value acts on it as
the local difference at a uniformizer. -/
private theorem sec3_principalValue_gaussian (v : V) (y : v.adicCompletion F) :
    finitePlacePrincipalValue v (finiteStandardGaussian v 1) (Multiplicative.ofAdd y) =
      if Valued.v y = 1 then 1 else 0 := by
  obtain ⟨π₀, hπ₀⟩ := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (π₀ : v.adicCompletion F) hπ₀.ne_zero
  have hinv : ∀ u : (v.adicCompletionIntegers F).units,
      schwartzBruhatUnitTranslate u.val (finiteStandardGaussian v 1) =
        ((1 : PontryaginDual (v.adicCompletionIntegers F).units) u : ℂ) •
          finiteStandardGaussian v 1 := by
    intro u
    have hu : Valued.v ((↑(u.val⁻¹) : v.adicCompletion F)) = 1 :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (Subgroup.inv_mem _ u.2)
    have h1 : ((1 : PontryaginDual (v.adicCompletionIntegers F).units) u : ℂ) = 1 := by simp
    rw [h1, one_smul]
    apply Subtype.ext
    funext x
    change finiteStandardGaussian v 1 (Multiplicative.ofAdd
      ((↑(u.val⁻¹) : v.adicCompletion F) * x.toAdd)) =
        finiteStandardGaussian v 1 (Multiplicative.ofAdd x.toAdd)
    rw [sec3_finiteStandardGaussian_apply, sec3_finiteStandardGaussian_apply]
    simp only [Set.indicator, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      map_mul, hu, one_mul]
  have hP := (finitePlacePrincipalValue_unique v π hπ₀).1 1 _ hinv
  rw [if_pos rfl] at hP
  rw [hP, finitePlaceDifference_integerIndicator v π hπ₀ y]
  have hmem : y ∈ Units.val '' ((v.adicCompletionIntegers F).units :
      Set (v.adicCompletion F)ˣ) ↔ Valued.v y = 1 := by
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨u, hu, rfl⟩
      exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
    · have hy0 : y ≠ 0 := fun h0 ↦ by simp [h0] at hy
      exact ⟨Units.mk0 y hy0,
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hy, rfl⟩
  simp only [Set.indicator, hmem]

/-- Two test functions agree once they agree at every point. -/
private theorem sec3_ext_ofAdd {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    {f g : SchwartzBruhat (Multiplicative A)}
    (h : ∀ x : A, f (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd x)) : f = g :=
  Subtype.ext (funext fun x ↦ h (Multiplicative.toAdd x))

/-- Two linear maps out of an S-local test space agree once they agree on pure tensors. -/
private theorem sec3_ext_pure {ι : Type*} [Fintype ι] {E N Q : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N] [AddCommGroup Q] [Module ℂ Q]
    (e : InductiveTensor E (FinestLocallyConvex (PiTensorProduct ℂ M)) ≃L[ℂ] N)
    (L₁ L₂ : N →ₗ[ℂ] Q)
    (h : ∀ (a : E) (g : ∀ i, M i),
      L₁ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g))) =
        L₂ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g)))) :
    L₁ = L₂ := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

open scoped TensorProduct in
/-- On a stage containing S and the selected places T, disjoint from S, the S-local
principal value of the transition of an S-local test multiplies it by the unit
indicators at T: the transition inserts the integer indicator at each place of T. -/
private theorem sec3_principalValue_transition {S T R : Finset V} (hST : Disjoint S T)
    (hSR : S ⊆ R) (hTR : T ⊆ R) (f : ℬₛ(S)) (y : SAdeleRing F R) :
    sAdelePrincipalValue F hTR (sAdeleSchwartzTransition F hSR f) (Multiplicative.ofAdd y) =
      (∏ w : R, if w.val ∈ T then (if Valued.v (y.2 w) = 1 then (1 : ℂ) else 0) else 1) *
        sAdeleSchwartzTransition F hSR f (Multiplicative.ofAdd y) := by
  let eS := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have heS := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let eR := (sAdeleSchwartz_inductiveTensor_equiv F R).choose
  have heR := (sAdeleSchwartz_inductiveTensor_equiv F R).choose_spec
  let ind : ℂ := ∏ w : R, if w.val ∈ T then (if Valued.v (y.2 w) = 1 then (1 : ℂ) else 0) else 1
  let ev : ℬₛ(R) →ₗ[ℂ] ℂ :=
    { toFun := fun h ↦ h (Multiplicative.ofAdd y)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L₁ : ℬₛ(S) →ₗ[ℂ] ℂ :=
    ev ∘ₗ (sAdelePrincipalValue F hTR) ∘ₗ sAdeleSchwartzTransition F hSR
  let L₂ : ℬₛ(S) →ₗ[ℂ] ℂ := ind • (ev ∘ₗ sAdeleSchwartzTransition F hSR)
  suffices key : L₁ = L₂ from LinearMap.congr_fun key f
  refine sec3_ext_pure eS L₁ L₂ fun a g ↦ ?_
  let g' : ∀ w : R, SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) := fun w ↦
    if h : w.val ∈ S then g ⟨w.val, h⟩ else finiteStandardGaussian w.val 1
  have hg' : ∀ w : R, w.val ∉ S → ∀ t : w.val.adicCompletion F,
      g' w (Multiplicative.ofAdd t) =
        Set.indicator (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))
          (fun _ ↦ 1) t := by
    intro w hw t
    simp only [g', dif_neg hw]
    exact sec3_finiteStandardGaussian_apply _ t
  have htrans : sAdeleSchwartzTransition F hSR (eS (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) =
      eR (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g' w)) := by
    refine sec3_ext_ofAdd fun x ↦ ?_
    refine (sAdeleSchwartzTransition_pure F hSR a g' hg' _ (fun z ↦ ?_) x).trans
      (heR a g' x).symm
    refine (heS a g z).trans (congrArg _ (Finset.prod_congr rfl fun w _ ↦ ?_))
    simp only [g', dif_pos w.2]
  have hpv := sAdelePrincipalValue_tmul (F := F) hTR a g'
  change ev (sAdelePrincipalValue F hTR (sAdeleSchwartzTransition F hSR
      (eS (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))) =
    ind * ev (sAdeleSchwartzTransition F hSR (eS (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))
  refine (congrArg (fun h ↦ ev (sAdelePrincipalValue F hTR h)) htrans).trans ?_
  refine ((congrArg ev hpv).trans (heR a _ y)).trans ?_
  refine Eq.trans ?_ (congrArg (fun h ↦ ind * ev h) htrans).symm
  refine Eq.trans ?_ (congrArg (ind * ·) (heR a g' y)).symm
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun w _ ↦ ?_)
  by_cases hT : w.val ∈ T
  · have hS : w.val ∉ S := Finset.disjoint_right.mp hST hT
    have hgw : g' w = finiteStandardGaussian w.val 1 := dif_neg hS
    rw [if_pos hT, if_pos hT, hgw, sec3_principalValue_gaussian,
      sec3_finiteStandardGaussian_apply]
    by_cases hv : Valued.v (y.2 w) = 1
    · rw [if_pos hv, Set.indicator_of_mem
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv.le), mul_one]
    · rw [if_neg hv, zero_mul]
  · rw [if_neg hT, if_neg hT, one_mul]

end DivisorialIndicatorPrincipalValue

/-- Paper: §11.3.1.1, p. 493. The product of the unit indicators on a finite set
outside S converts the integer-extended test to its principal value at those places.
Deviation: Read the remaining integer factors as indexed outside S and the
selected places. The equality is recorded on the ideles. -/
theorem divisorialIndicator_mul_thetaRepresentative (S T : Finset V) (_hST : Disjoint S T)
    (f : ℬₛ(S)) (g : I𝔽) :
    divisorialIndicator T g * sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd g.val) =
      adelePrincipalValue F T (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd g.val) := by
  obtain ⟨S₂, hS₂⟩ := sec3_exists_test_one (F := F)
  have hSR : S ⊆ S ∪ T ∪ S₂ := Finset.subset_union_left.trans Finset.subset_union_left
  have hTR : T ⊆ S ∪ T ∪ S₂ := Finset.subset_union_right.trans Finset.subset_union_left
  obtain ⟨k₀, hk₀⟩ := hS₂ (S ∪ T ∪ S₂) Finset.subset_union_right
  have hG : sAdeleSchwartzToGlobal F (S ∪ T ∪ S₂) (sAdeleSchwartzTransition F hSR f) =
      sAdeleSchwartzToGlobal F S f :=
    LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hSR) f
  have hind : divisorialIndicator T g =
      ∏ w : (S ∪ T ∪ S₂ : Finset V), if w.val ∈ T then
        (if Valued.v ((adeleProjection F (S ∪ T ∪ S₂) g.val).2 w) = 1 then (1 : ℂ) else 0)
        else 1 := by
    have h := Finset.prod_coe_sort (S ∪ T ∪ S₂) (fun v ↦ if v ∈ T then
      (if Valued.v (g.val.2 v) = 1 then (1 : ℂ) else 0) else 1)
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hTR] at h
    exact h.symm
  rw [← hG, sec3_toGlobal_comm hTR k₀ hk₀, sAdeleSchwartzToGlobal_apply,
    sAdeleSchwartzToGlobal_apply]
  split_ifs
  · rw [sec3_principalValue_transition _hST hSR hTR, hind]
  · rw [mul_zero]

/-- The primary primes of §11.3.1.1 are distinct: they are the values of `Nat.nth`
on a set of rational primes. -/
private theorem primaryDivisorialZeta_succ_prime_injective (S : Finset V) :
    Function.Injective (primaryDivisorialPrime (F := F) S) := by
  intro j l hjl
  have hgen : Rat.HeightOneSpectrum.natGenerator (primaryDivisorialPrime S j) =
      Rat.HeightOneSpectrum.natGenerator (primaryDivisorialPrime S l) := by rw [hjl]
  rw [(primaryDivisorialPrime_eq_iff S j _).1 rfl,
    (primaryDivisorialPrime_eq_iff S l _).1 rfl] at hgen
  exact Nat.nth_injective (primaryDivisorial_infinite S) hgen

/-- The places over the next primary prime are new: they are disjoint from the
places over the earlier ones. -/
private theorem primaryDivisorialZeta_succ_disjoint (S : Finset V) (k : ℕ) :
    Disjoint (primaryDivisorialPlaces F S k) (above(primaryDivisorialPrime S k)) := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [primaryDivisorialPlaces, Finset.mem_biUnion, Finset.mem_range] at hw
  obtain ⟨j, hj, hwj⟩ := hw
  have h1 : w.under (𝓞 ℚ) = primaryDivisorialPrime S j := by
    simpa [Set.Finite.mem_toFinset] using hwj
  have h2 : w.under (𝓞 ℚ) = primaryDivisorialPrime S k := by
    simpa [Set.Finite.mem_toFinset] using hw'
  have hjk : j = k := primaryDivisorialZeta_succ_prime_injective S (h1.symm.trans h2)
  omega

/-- The reciprocal Euler product over the new places is the quotient of the
products over the enlarged and the old primary sets. -/
private theorem primaryDivisorialZeta_succ_factor (S : Finset V) (k : ℕ)
    (χ : PontryaginDual C𝔽) (w : ℂ) :
    reciprocalPartialHeckeEulerProduct χ (primaryDivisorialPlaces F S (k + 1)) w =
      reciprocalPartialHeckeEulerProduct χ (primaryDivisorialPlaces F S k) w *
        reciprocalPartialHeckeEulerProduct χ (above(primaryDivisorialPrime S k)) w := by
  simp only [primaryDivisorialPlaces_succ, reciprocalPartialHeckeEulerProduct,
    Finset.prod_union (primaryDivisorialZeta_succ_disjoint S k)]

/-- The norm-twist of a unitary idele-class character is not the trivial character on
the half-plane of absolute convergence: test it on the canonical norm section, where
unitarity of the character forces the norm power to be one. -/
private theorem primaryDivisorialZeta_succ_twist_ne_one (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : 0 < z.re) : ideleClassNormTwist χ z ≠ 1 := by
  intro h
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let u : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  have hu : ((u : ℝ≥0) : ℝ) = 2 := rfl
  have hnorm := congrArg (fun w : ℂ ↦ ‖w‖) (DFunLike.congr_fun h (σ u))
  have hR : ‖((1 : HeckeCharacter (𝓞 F) F) (σ u))‖ = 1 := by simp
  rw [hR] at hnorm
  change ‖(χ (σ u) : ℂ) * (((ideleClassNorm F (σ u) : ℝ≥0) : ℝ) : ℂ) ^ z‖ = 1 at hnorm
  rw [norm_mul, Circle.norm_coe, one_mul, hσ u, hu,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)] at hnorm
  have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hz
  linarith

/-- On the half-plane `1 < re z` the norm twist of a unitary character is not the
norm character: again test on the canonical norm section. -/
private theorem primaryDivisorialZeta_succ_twist_ne_norm (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : 1 < z.re) :
    ideleClassNormTwist χ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) (1 : ℂ) := by
  intro h
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let u : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  have hu : ((u : ℝ≥0) : ℝ) = 2 := rfl
  have hnorm := congrArg (fun w : ℂ ↦ ‖w‖) (DFunLike.congr_fun h (σ u))
  rw [ideleClassNormTwist_one_one] at hnorm
  change ‖(χ (σ u) : ℂ) * (((ideleClassNorm F (σ u) : ℝ≥0) : ℝ) : ℂ) ^ z‖ =
    ‖((((ideleClassNorm F (σ u) : ℝ≥0) : ℝ)) : ℂ)‖ at hnorm
  rw [norm_mul, Circle.norm_coe, one_mul, hσ u, hu,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
    show ‖(((2 : ℝ)) : ℂ)‖ = (2 : ℝ) from by norm_num] at hnorm
  have h1 : (2 : ℝ) ^ z.re = (2 : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]; exact hnorm
  have := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)).mp h1
  linarith

/-- Paper: §11.3.1.1, p. 493. Removing the next prime's integer factors
multiplies the zeta transform of the depleted test by the reciprocal Euler
product over that prime.
Deviation: State the identity on the half-plane of absolute convergence. -/
theorem primaryDivisorialZeta_succ (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (z : ℂ) (_hz : 1 < z.re) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k := by
  let Fg : SchwartzBruhat (Multiplicative 𝔸[F]) := sAdeleSchwartzToGlobal F S f
  have hpunct : (fun t ↦ globalIdelicZFunction
        (adelePrincipalValue F (primaryDivisorialPlaces F S (k + 1)) Fg)
          (ideleClassNormTwist χ t)) =ᶠ[𝓝[≠] z]
      (fun t ↦ reciprocalPartialHeckeEulerProduct χ (above(primaryDivisorialPrime S k)) t *
        globalIdelicZFunction (adelePrincipalValue F (primaryDivisorialPlaces F S k) Fg)
          (ideleClassNormTwist χ t)) := by
    have h₁ := globalPrincipalValueConverse_mellin (F := F)
      (primaryDivisorialPlaces F S (k + 1)) χ Fg
    have h₂ := globalPrincipalValueConverse_mellin (F := F)
      (primaryDivisorialPlaces F S k) χ Fg
    filter_upwards [h₁.filter_mono (nhdsNE_le_codiscrete z),
      h₂.filter_mono (nhdsNE_le_codiscrete z)] with t ht1 ht2
    rw [ht1, ht2, primaryDivisorialZeta_succ_factor S k χ t]
    ring
  have hNF₁ : MeromorphicNFAt (fun t ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S (k + 1)) Fg)
        (ideleClassNormTwist χ t)) z :=
    globalIdelicZFunction_meromorphic _ χ (mem_univ z)
  have hZan : AnalyticAt ℂ (fun t ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S k) Fg)
        (ideleClassNormTwist χ t)) z :=
    (globalIdelicZFunction_poles (adelePrincipalValue F (primaryDivisorialPlaces F S k) Fg)
      χ).1 z ⟨primaryDivisorialZeta_succ_twist_ne_one (F := F) χ (by linarith),
        primaryDivisorialZeta_succ_twist_ne_norm (F := F) χ _hz⟩
  have hAn : AnalyticAt ℂ (fun t ↦
      reciprocalPartialHeckeEulerProduct χ (above(primaryDivisorialPrime S k)) t *
        globalIdelicZFunction (adelePrincipalValue F (primaryDivisorialPlaces F S k) Fg)
          (ideleClassNormTwist χ t)) z :=
    ((strongCoprimalityJetMatrix_det_ne_zero_euler χ
      (above(primaryDivisorialPrime S k))).1 z).mul hZan
  have hNF₂ : MeromorphicNFAt (fun t ↦
      reciprocalPartialHeckeEulerProduct χ (above(primaryDivisorialPrime S k)) t *
        globalIdelicZFunction (adelePrincipalValue F (primaryDivisorialPlaces F S k) Fg)
          (ideleClassNormTwist χ t)) z := hAn.meromorphicNFAt
  have hval := ((hNF₁.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hNF₂).mp hpunct).eq_of_nhds
  dsimp only
  exact hval

/-- Paper: §11.3.1.1, p. 493. For a test whose global extension has both polar
values zero the depletion identity holds at every exponent, in particular at the
zeros of the reciprocal Euler product, which lie on the line of real part zero.
Deviation: The polar condition makes both zeta functions entire, so the
normal-form values at poles do not enter. -/
theorem primaryDivisorialZeta_succ_of_polar (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (_hf : sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F) (z : ℂ) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k :=
  by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f, _hf⟩
  let Z (j : ℕ) (w : ℂ) := globalIdelicZFunction
    (adelePrincipalValue F (primaryDivisorialPlaces F S j) f₀.val) (ideleClassNormTwist χ w)
  have ha (j : ℕ) : AnalyticOnNhd ℂ (Z j) univ := fun z _ ↦
    (globalIdelicZFunction_entire_of_vanishing _
      (adelePrincipalValue_mem_polarSubspace (primaryDivisorialPlaces F S j) f₀) χ).analyticAt z
  let Q := reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k)
  have hQ : AnalyticOnNhd ℂ Q univ := fun w _ ↦
    (strongCoprimalityJetMatrix_det_ne_zero_euler χ above(primaryDivisorialPrime S k)).1 w
  have he : Z (k + 1) =ᶠ[nhds (2 : ℂ)] Q * Z k := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually
      (eventually_gt_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num))] with w hw
    exact primaryDivisorialZeta_succ S k χ _hχ f w hw
  exact congrFun ((ha _).eq_of_eventuallyEq (hQ.mul (ha k)) he) z

-- TODO(paper-gap): The local "Weil's Identity" on p. 492 has an extra factor
-- μᵥ(𝒪ᵥˣ) on the left. With the Tamagawa measure of (A.3.2.2) both
-- Zᵥ(1_{𝒪ᵥˣ}, c) and Lᵥ(c)⁻¹ Zᵥ(1_{𝒪ᵥ}, c) equal μᵥ(𝒪ᵥˣ) for unramified c, so
-- the print holds only where this mass is one. At the place over 2 of ℚ(i) the
-- mass is 1/2 and the two printed sides are 1/4 and 1/2. The same page gives the
-- product of all unit masses as the square root of the absolute different. It
-- is the reciprocal square root of the absolute discriminant.

section ThetaSubquotient

local notation "P" => adelePolarSubspace F
local notation "Θ(" ω ")" =>
  (↥P ⧸ LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P))

/-- Paper: (11.3.1.3), p. 494. The theta denominator at a given stage is the
image of polar-free tests after the selected principal values in the polar
homogeneous theta space. -/
def divisorialThetaStage (ω : PontryaginDual C₁) (T : Finset V) : Submodule ℂ Θ(ω) :=
  Submodule.span ℂ (Set.range fun f : P ↦ (Submodule.Quotient.mk
    ⟨adelePrincipalValue F T f.val, adelePrincipalValue_mem_polarSubspace T f⟩ : Θ(ω)))

/-- Conjugating `map id Q` by an equivalence gives the identity when `Q` fixes every vector.
Stated in the shape of `sAdelePrincipalValue`, so that it applies syntactically. -/
private theorem divisorialThetaStage_empty_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (Q : G →ₗ[ℂ] G) (hQ : ∀ x, Q x = x) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hQ' : Q = LinearMap.id := LinearMap.ext hQ
  subst hQ'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

/-- Conjugating `map Q id` by an equivalence gives the identity when `Q` fixes every vector.
Stated in the shape of `adelePrincipalValue`, so that it applies syntactically. -/
private theorem divisorialThetaStage_empty_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (Q : E →ₗ[ℂ] E) (hQ : ∀ x, Q x = x) :
    e.toLinearMap.comp ((TensorProduct.map Q (LinearMap.id : G →ₗ[ℂ] G)).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hQ' : Q = LinearMap.id := LinearMap.ext hQ
  subst hQ'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

open scoped TensorProduct in
/-- A tensor power of identity maps fixes every vector of the finest locally convex copy. -/
private theorem divisorialThetaStage_empty_piMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (f : ∀ i, M i →ₗ[ℂ] M i) (hf : ∀ i, f i = LinearMap.id)
    (x : FinestLocallyConvex (⨂[ℂ] i, M i)) :
    (PiTensorProduct.map f : FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ]
      FinestLocallyConvex (⨂[ℂ] i, M i)) x = x := by
  have : f = fun _ ↦ LinearMap.id := funext hf
  subst this
  rw [PiTensorProduct.map_id]
  rfl

/-- With no selected places the S-local principal value is the identity. -/
private theorem divisorialThetaStage_empty_sPV (h : (∅ : Finset V) ⊆ ∅) :
    sAdelePrincipalValue F h = LinearMap.id := by
  unfold sAdelePrincipalValue
  exact divisorialThetaStage_empty_conj_left _ _
    (divisorialThetaStage_empty_piMap _ fun w ↦ absurd w.2 (Finset.notMem_empty _))

/-- With no selected places the global principal value is the identity. -/
private theorem divisorialThetaStage_empty_PV :
    adelePrincipalValue F (∅ : Finset V) = LinearMap.id := by
  unfold adelePrincipalValue
  exact divisorialThetaStage_empty_conj_right _ _ fun x ↦
    LinearMap.congr_fun (divisorialThetaStage_empty_sPV _) x

private theorem divisorialThetaStage_empty_span {α M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f g : α → M) (hfg : f = g) (hg : Function.Surjective g) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  subst hfg
  rw [hg.range_eq]
  exact Submodule.span_univ

/-- Paper: (11.3.1.3), p. 494. With no principal values the stage is the entire
polar homogeneous theta space. -/
theorem divisorialThetaStage_empty (ω : PontryaginDual C₁) :
    divisorialThetaStage ω ∅ = ⊤ := by
  unfold divisorialThetaStage
  refine divisorialThetaStage_empty_span _ (fun p : P ↦ (Submodule.Quotient.mk p : Θ(ω))) ?_
    (Submodule.Quotient.mk_surjective _)
  funext p
  have e : (⟨adelePrincipalValue F ∅ p.val, adelePrincipalValue_mem_polarSubspace ∅ p⟩ : P) = p :=
    Subtype.ext (LinearMap.ext_iff.mp divisorialThetaStage_empty_PV p.val)
  exact congrArg (fun y : P ↦ (Submodule.Quotient.mk y : Θ(ω))) e

/-- Two linear maps agree once they agree on the pure tensors of an
inductive tensor product with a finite tensor product. -/
private theorem divisorialThetaStage_antitone_extPi {ι : Type*} [Fintype ι] {E N : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (PiTensorProduct ℂ M)) ≃L[ℂ] N)
    (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (g : ∀ i, M i),
      L₁ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g))) =
        L₂ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g)))) :
    L₁ = L₂ := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

/-- The S-local principal values compose over disjoint sets of selected places. -/
private theorem divisorialThetaStage_antitone_sPV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    sAdelePrincipalValue F (Finset.Subset.refl T') =
      (sAdelePrincipalValue F hT).comp (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T))) := by
  refine divisorialThetaStage_antitone_extPi (sAdeleSchwartz_inductiveTensor_equiv F T').choose _ _ fun a g ↦ ?_
  have h1 := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a g
  have h2 := sAdelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a g
  have h3 := sAdelePrincipalValue_tmul (F := F) hT a
    (fun w : T' ↦ if (w : HeightOneSpectrum (𝓞 F)) ∈ T' \ T then
      finitePlacePrincipalValue (F := F) w.val (g w) else g w)
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (sAdelePrincipalValue F hT) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg
  apply congrArg
  funext w
  by_cases hw : (w : HeightOneSpectrum (𝓞 F)) ∈ T
  · simp [hw, w.2, Finset.mem_sdiff]
  · simp [hw, w.2, Finset.mem_sdiff]

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product. -/
private theorem divisorialThetaStage_antitone_extTail {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (b : G), L₁ (e (TensorProduct.tmul ℂ a b)) = L₂ (e (TensorProduct.tmul ℂ a b))) :
    L₁ = L₂ := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext (h a)

/-- The global principal value at a larger set is the one at the smaller set after the one
at the difference. -/
private theorem divisorialThetaStage_antitone_PV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    adelePrincipalValue F T' =
      (adelePrincipalValue F T).comp (adelePrincipalValue F (T' \ T)) := by
  refine divisorialThetaStage_antitone_extTail (sAdeleTailSchwartz_inductiveTensor_equiv F T').choose _ _ fun a b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a b
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a b
  have h3 := adelePrincipalValue_tmul (F := F) hT
    (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T)) a) b
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (adelePrincipalValue F T) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg₂ _ _ rfl
  exact (LinearMap.ext_iff.mp (divisorialThetaStage_antitone_sPV hT) a).trans (LinearMap.comp_apply _ _ _)

/-- A factorization through a map preserving the submodule gives inclusion of images
after applying the quotient map. -/
private theorem divisorialThetaStage_antitone_range {A β : Type*} [AddCommMonoid A] [Module ℂ A]
    (B : Submodule ℂ A) (Φ : B → β) (L L' R : A → A)
    (h : ∀ f : B, L f.val ∈ B) (h' : ∀ f : B, L' f.val ∈ B) (hR : ∀ f : B, R f.val ∈ B)
    (hc : ∀ f : B, L (R f.val) = L' f.val) :
    Set.range (fun f : B ↦ Φ ⟨L' f.val, h' f⟩) ⊆ Set.range (fun f : B ↦ Φ ⟨L f.val, h f⟩) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨R f.val, hR f⟩, congrArg Φ (Subtype.ext (hc f))⟩

/-- Paper: (11.3.1.3), p. 494. Adding places decreases the principal-value image
of the polar theta space. -/
theorem divisorialThetaStage_antitone (ω : PontryaginDual C₁) :
    Antitone (divisorialThetaStage ω) := by
  intro T T' hTT'
  have hP : ∀ f : P, adelePrincipalValue F T (adelePrincipalValue F (T' \ T) f.val) =
      adelePrincipalValue F T' f.val := fun f ↦
    ((LinearMap.ext_iff.mp (divisorialThetaStage_antitone_PV hTT') f.val).trans
      (LinearMap.comp_apply _ _ _)).symm
  unfold divisorialThetaStage
  exact Submodule.span_mono (divisorialThetaStage_antitone_range P
    (fun f : P ↦ (Submodule.Quotient.mk f : Θ(ω)))
    (adelePrincipalValue F T) (adelePrincipalValue F T') (adelePrincipalValue F (T' \ T))
    (adelePrincipalValue_mem_polarSubspace T) (adelePrincipalValue_mem_polarSubspace T')
    (adelePrincipalValue_mem_polarSubspace (T' \ T)) hP)

/-- Paper: (11.3.1.3), p. 494, and (7.4.0.2), p. 366. At the fibre over one
rational prime the stage is the finite-place denominator of §7.4, so the first
subquotient of the chain is the finite orbital quotient used there. -/
theorem divisorialThetaStage_above (χ : PontryaginDual C𝔽) (p : Vℚ) :
    divisorialThetaStage (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      C₁ →ₜ* C𝔽)) above(p) = finiteNuclearityDenominator χ p := by
  unfold divisorialThetaStage finiteNuclearityDenominator
  with_reducible rfl

/-- Paper: (11.3.1.3), p. 494. Divide the kth principal-value theta image
by the next image, viewed inside the kth stage.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def PrimaryDivisorialThetaSubquotient (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :=
  ↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
      (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype

namespace PrimaryDivisorialThetaSubquotient

instance instAddCommGroup (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    AddCommGroup (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (AddCommGroup
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instModule (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    Module ℂ (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (Module ℂ
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instTopologicalSpace (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    TopologicalSpace (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (TopologicalSpace
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instIsTopologicalAddGroup (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    IsTopologicalAddGroup (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (IsTopologicalAddGroup
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instContinuousSMul (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    ContinuousSMul ℂ (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (ContinuousSMul ℂ
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

end PrimaryDivisorialThetaSubquotient

/-- Paper: (11.3.1.3), p. 494. A representative in the kth stage has zero
class precisely when it belongs to the next stage. -/
theorem primaryDivisorialThetaSubquotient_mk_eq_zero (S : Finset V) (ω : PontryaginDual C₁)
    (k : ℕ) (x : divisorialThetaStage ω (primaryDivisorialPlaces F S k)) :
    (Submodule.Quotient.mk x : PrimaryDivisorialThetaSubquotient S ω k) = 0 ↔
      x.val ∈ divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1)) := by
  simp only [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

/-- Paper: (11.3.1.3), p. 494, and the cutoff limit on p. 496. Restricting
past the new prime packet puts the representative in the denominator, at any
Fourier level. -/
theorem primaryDivisorialThetaSubquotient_later_eq_zero (S : Finset V) (ω : PontryaginDual C₁)
    {k j : ℕ} (hkj : k < j) (x : divisorialThetaStage (F := F) ω (primaryDivisorialPlaces F S k))
    (hx : x.val ∈ divisorialThetaStage (F := F) ω (primaryDivisorialPlaces F S j)) :
    (Submodule.Quotient.mk x : PrimaryDivisorialThetaSubquotient (F := F) S ω k) = 0 := by
  apply (primaryDivisorialThetaSubquotient_mk_eq_zero S ω k x).2
  have hsub : primaryDivisorialPlaces F S (k + 1) ⊆ primaryDivisorialPlaces F S j :=
    primaryDivisorialPlaces_mono (F := F) S hkj
  exact (divisorialThetaStage_antitone (F := F) ω hsub : divisorialThetaStage (F := F) ω _ ≤
    divisorialThetaStage (F := F) ω _) hx

/-- Paper: (11.3.1.3), p. 494. The principal values at the selected places
restrict to an endomorphism of the polar-free global tests. -/
def adelePolarPrincipalValue (T : Finset V) : P →ₗ[ℂ] P :=
  ((adelePrincipalValue F T).comp (adelePolarSubspace F).subtype).codRestrict
    (adelePolarSubspace F) (adelePrincipalValue_mem_polarSubspace T)

local notation "polarPV(" T ")" => adelePolarPrincipalValue (F := F) T

/-- Paper: (11.3.1.3), p. 494. Apply the principal values at a packet set
to a polar-free global test and take its homogeneous theta class. -/
def divisorialThetaRepresentative (ω : PontryaginDual C₁) (T : Finset V) :
    P →ₗ[ℂ] Θ(ω) :=
  ((homogeneousAdelicThetaLinearMap F ω).domRestrict P).ker.mkQ.comp polarPV(T)

section PositiveTwistCancellation

local notation "average(" twist ", " hs ", " ω ")" =>
  (existsUnique_globalThetaSobolevAverage (F := F) (a := twist) (le_refl (0 : ℝ)) hs ω).exists.choose
local notation "endpointImage(" twist ", " hs ", " ω ", " f ")" =>
  (average(twist, hs, ω) ((globalThetaSobolevInclusion F twist (le_refl (0 : ℝ)) hs)
    (Submodule.Quotient.mk (f : P)))).val

private theorem primaryDivisorialThetaClass_average_commutes {G X : Type*} [Monoid G]
    [TopologicalSpace G] [MeasurableSpace G] [NormedAddCommGroup X] [NormedSpace ℂ X]
    (μ : Measure G) (ω : PontryaginDual G) (ρ : G →* (X →L[ℂ] X))
    (A M : X →L[ℂ] X) (hA : IsPettisIsotypicAverageOn μ univ ρ ω A)
    (hM : ∀ k v, M (ρ k v) = ρ k (M v)) (x : X) : M (A x) = A (M x) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro T
  have h₁ := LinearMap.congr_fun (hA (M x)).2 T
  have h₂ := LinearMap.congr_fun (hA x).2 (T.comp M)
  exact (h₁.trans ((integral_congr_ae (.of_forall fun k ↦ congrArg T
    ((congrArg (star (ω k : ℂ) • ·) (hM k x).symm).trans (M.map_smul _ _).symm))).trans h₂.symm)).symm

/-- Paper: (11.2.0.7), p. 486. On the norm-one isotype, applying the completed
principal value to a test image gives the image of the principal-value test. -/
theorem globalThetaSobolevPrincipalValue_homogeneous_apply (T : Finset V) (b : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : P) :
    let M := globalThetaSobolevPrincipalValue F T b hs
    M (endpointImage(b, hs, ω, f)) = endpointImage(b, hs, ω, polarPV(T) f) := by
  intro M
  let hJ := le_refl (0 : ℝ)
  have hc := primaryDivisorialThetaClass_average_commutes (normOneIdeleClassTamagawaMeasure F) ω
    ((exists_globalThetaSobolevAction (F := F) b hJ hs).choose.comp (ideleClassNorm F).ker.subtype)
    _ M (existsUnique_globalThetaSobolevAverage (F := F) (a := b) hJ hs ω).exists.choose_spec.1
    (globalThetaSobolevPrincipalValue_equivariant T b hs) ((globalThetaSobolevInclusion F b hJ hs) (Submodule.Quotient.mk f))
  exact hc.trans (congrArg (fun v ↦ (average(b, hs, ω) v).val)
    (globalThetaSobolevPrincipalValue_apply T b hs f))

private theorem primaryDivisorialThetaClass_cancel_of_embedding {D Q H A : Type*} (q : D → Q) (v : D → H)
    (t : D → A) (i : A → H) (Dmap : D → D) (M : H → H)
    (hi : Injective i) (hM : Injective M)
    (hq : ∀ x y, q x = q y ↔ t x = t y)
    (hv : ∀ x, i (t x) = v x) (hp : ∀ x, M (v x) = v (Dmap x)) (x y : D) :
    q (Dmap x) = q (Dmap y) ↔ q x = q y := by
  have he (a b : D) : q a = q b ↔ v a = v b := by
    rw [← hv, ← hv, hi.eq_iff, hq]
  rw [he, he, ← hp, ← hp, hM.eq_iff]

/-- On homogeneous polar-free tests, cancellation follows by embedding in the
completion with positive twist, where the completed principal value is bijective. -/
private theorem primaryDivisorialThetaClass_cancel (ω : PontryaginDual C₁) (T : Finset V)
    (f g : P) :
    (Submodule.Quotient.mk (polarPV(T) f) : Θ(ω)) =
      Submodule.Quotient.mk (polarPV(T) g) ↔
    (Submodule.Quotient.mk f : Θ(ω)) = Submodule.Quotient.mk g := by
  let hJ := le_refl (0 : ℝ)
  let t (x : P) : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk x.val, Submodule.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  let inc := (exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 1) hJ hJ ω).choose
  let v (x : P) := endpointImage(1, hJ, ω, x)
  have hv (x : P) : (inc (t x)).val = v x :=
    congrArg Subtype.val ((exists_globalHomogeneousThetaSobolevInclusion (F := F)
      (a := 1) hJ hJ ω).choose_spec.2.2 x (t x) rfl).1
  have hq (x y : P) : (Submodule.Quotient.mk x : Θ(ω)) = Submodule.Quotient.mk y ↔
      t x = t y := by
    rw [Subtype.ext_iff]
    change _ ↔ (Submodule.Quotient.mk x.val : GlobalHomogeneousThetaSpace F ω) =
      Submodule.Quotient.mk y.val
    simp only [Submodule.Quotient.eq, LinearMap.mem_ker, LinearMap.domRestrict_apply,
      Submodule.coe_sub]
  let M := globalThetaSobolevPrincipalValue F T 1 hJ
  have hp (x : P) : M (v x) = v (polarPV(T) x) :=
    globalThetaSobolevPrincipalValue_homogeneous_apply T 1 hJ ω x
  exact primaryDivisorialThetaClass_cancel_of_embedding (fun x : P ↦ (Submodule.Quotient.mk x : Θ(ω))) v t
    (fun z ↦ (inc z).val) (polarPV(T)) M
    (Subtype.val_injective.comp (exists_globalHomogeneousThetaSobolevInclusion (F := F)
      (a := 1) hJ hJ ω).choose_spec.1)
    (globalThetaSobolevPrincipalValue_bijective_of_pos (F := F) T zero_lt_one hJ).1 hq hv hp f g

end PositiveTwistCancellation

private theorem divisorialThetaRepresentative_next_sdiff (S : Finset V) (k : ℕ) :
    primaryDivisorialPlaces F S (k + 1) \ primaryDivisorialPlaces F S k =
      above(primaryDivisorialPrime (F := F) S k) := by
  rw [primaryDivisorialPlaces_succ (F := F) S k]
  exact Finset.union_sdiff_cancel_left (primaryDivisorialZeta_succ_disjoint (F := F) S k)

private theorem divisorialThetaRepresentative_polarPV_comp (T U T' : Finset V)
    (h : adelePrincipalValue F T' = (adelePrincipalValue F T).comp (adelePrincipalValue F U))
    (g : P) : polarPV(T') g = polarPV(T) (polarPV(U) g) :=
  Subtype.ext (LinearMap.congr_fun h g.val)

private theorem divisorialThetaRepresentative_next_PV (S : Finset V) (k : ℕ) (g : P) :
    polarPV(primaryDivisorialPlaces F S (k + 1)) g =
      polarPV(primaryDivisorialPlaces F S k) (polarPV(above(primaryDivisorialPrime (F := F) S k)) g) := by
  let T := primaryDivisorialPlaces F S k
  let T' := primaryDivisorialPlaces F S (k + 1)
  have hsub : T ⊆ T' := primaryDivisorialPlaces_mono (F := F) S (Nat.le_succ k)
  apply divisorialThetaRepresentative_polarPV_comp
  exact (divisorialThetaStage_antitone_PV (F := F) hsub).trans
    (congrArg (fun U ↦ (adelePrincipalValue F T).comp (adelePrincipalValue F U))
      (divisorialThetaRepresentative_next_sdiff (F := F) S k))

private theorem divisorialThetaRepresentative_mem_stage (ω : PontryaginDual C₁) (T : Finset V)
    (x : Θ(ω)) : x ∈ divisorialThetaStage ω T ↔
      ∃ g : P, (Submodule.Quotient.mk (polarPV(T) g) : Θ(ω)) = x := by
  have hr : divisorialThetaStage ω T = (divisorialThetaRepresentative ω T).range := by
    exact Submodule.span_eq (divisorialThetaRepresentative ω T).range
  rw [hr, LinearMap.mem_range]
  simp only [divisorialThetaRepresentative, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- Paper: (11.3.1.3), p. 494. A test represents zero in a successive stage quotient
exactly when its original theta class belongs to the principal-value image for the
single new packet. The earlier packets cancel before taking completions. -/
theorem divisorialThetaRepresentative_mem_next_iff (S : Finset V) (ω : PontryaginDual C₁)
    (k : ℕ) (f : P) :
    divisorialThetaRepresentative ω (primaryDivisorialPlaces F S k) f ∈
      divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1)) ↔
      (Submodule.Quotient.mk f : Θ(ω)) ∈
        divisorialThetaStage (F := F) ω above(primaryDivisorialPrime (F := F) S k) := by
  refine (divisorialThetaRepresentative_mem_stage ω _ _).trans
    ((exists_congr fun g ↦ ?_).trans (divisorialThetaRepresentative_mem_stage ω _ _).symm)
  rw [divisorialThetaRepresentative_next_PV S k g]
  simp only [divisorialThetaRepresentative, LinearMap.comp_apply, Submodule.mkQ_apply]
  exact primaryDivisorialThetaClass_cancel ω (primaryDivisorialPlaces F S k)
    (polarPV(above(primaryDivisorialPrime (F := F) S k)) g) f

/-- Paper: (11.3.1.3), p. 494. Global polar-free representatives of an absolute
Paley–Wiener level are integer-indicator insertions of tests with additive Fourier
support in the box of size X at S.
Deviation: Specify the box on the test before applying the kth principal value,
as in (11.3.1.1) and the absolute level on p. 487. -/
def primaryDivisorialAbsolutePWTests (S : Finset V) (X : ℝ) : Submodule ℂ P :=
  (((sLocalPWTests (S := S) le_rfl (sLocalPWBox S X)).map
    (sAdeleSchwartzToGlobal F S)).comap (adelePolarSubspace F).subtype)

private theorem primaryDivisorialAbsolutePW_equiv_of_kernel
    {E A B : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (L : E →ₗ[ℂ] A) (R : E →ₗ[ℂ] B)
    (h : ∀ f, L f = 0 ↔ R f = 0) :
    ∃ e : L.range ≃ₗ[ℂ] R.range, ∀ f : E, e (L.rangeRestrict f) = R.rangeRestrict f := by
  have hk : L.ker = R.ker := Submodule.ext h
  refine ⟨L.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans
    R.quotKerEquivRange), fun f ↦ ?_⟩
  change R.quotKerEquivRange ((Submodule.quotEquivOfEq _ _ hk)
    (L.quotKerEquivRange.symm ⟨L f, _⟩)) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk]
  rfl

/-- Paper: (11.3.1.3), p. 494. At every fixed Fourier bound, the images of the
same tests in the successive quotient and in the smooth single-prime orbital
quotient of (7.4.0.2) are linearly equivalent. The right-hand image realizes
the stage subquotient inside the ambient theta space modulo the next stage.
Deviation: This identifies the algebraic images of actual band-limited tests.
The trace-norm comparison on the half-twisted completion is a separate assertion. -/
theorem primaryDivisorialAbsolutePW_equiv (S : Finset V) (χ : PontryaginDual C𝔽)
    (k : ℕ) (X : ℝ) :
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
    let W := primaryDivisorialAbsolutePWTests (F := F) S X
    let L := ((finiteNuclearityDenominator χ (primaryDivisorialPrime (F := F) S k)).mkQ.comp
      ((homogeneousAdelicThetaLinearMap F ω).domRestrict P).ker.mkQ).domRestrict W
    let B := divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))
    let R := B.mkQ.comp
      ((divisorialThetaRepresentative ω (primaryDivisorialPlaces F S k)).domRestrict W)
    ∃ e : L.range ≃ₗ[ℂ] R.range, ∀ f : W, e (L.rangeRestrict f) = R.rangeRestrict f := by
  intro ω W L B R
  apply primaryDivisorialAbsolutePW_equiv_of_kernel L R
  intro f
  change (Submodule.Quotient.mk (Submodule.Quotient.mk f.val : Θ(ω)) :
    Θ(ω) ⧸ finiteNuclearityDenominator χ (primaryDivisorialPrime (F := F) S k)) = 0 ↔
      B.mkQ (divisorialThetaRepresentative ω (primaryDivisorialPlaces F S k) f.val) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  exact ((divisorialThetaRepresentative_mem_next_iff S ω k f.val).trans
    (by rw [divisorialThetaStage_above (F := F) χ])).symm

end ThetaSubquotient

/-- Paper: (11.3.1.4), p. 494. Multiply an idelic kernel by the next indicator
minus the current indicator.
Deviation: The difference acts on the input coordinate, as in the shell
calculation on pp. 495–496. -/
def divisorialKernelDifference (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽) : ℂ :=
  (divisorialIndicator (primaryDivisorialPlaces F S (k + 1)) xy.2 -
    divisorialIndicator (primaryDivisorialPlaces F S k) xy.2) * K xy

/-- Paper: (11.3.1.4), p. 494. On the removed part of the kth stratum the
successive difference is the negative of the original kernel. -/
theorem divisorialKernelDifference_eq_neg (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽)
    (_hxy : xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S k) \
      divisorialStratum F (primaryDivisorialPlaces F S (k + 1))) :
    divisorialKernelDifference S k K xy = -K xy := by
  have h1 : divisorialIndicator (primaryDivisorialPlaces F S k) xy.2 = 1 := by
    rw [divisorialIndicator_eq_indicator]; exact Set.indicator_of_mem _hxy.1 _
  have h2 : divisorialIndicator (primaryDivisorialPlaces F S (k + 1)) xy.2 = 0 := by
    rw [divisorialIndicator_eq_indicator]; exact Set.indicator_of_notMem _hxy.2 _
  simp [divisorialKernelDifference, h1, h2]

/-- Paper: (11.3.2.3), p. 495. The later input cutoff annihilates the entire
shell kernel pointwise, for every choice of kernel and lifts. -/
theorem divisorialKernelDifference_mul_laterIndicator (S : Finset V) {k j : ℕ}
    (hkj : k < j) (K : I𝔽 × I𝔽 → ℂ) (xy : I𝔽 × I𝔽) :
    divisorialKernelDifference S k K xy * divisorialIndicator (primaryDivisorialPlaces F S j) xy.2
      = 0 := by
  by_cases h : xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S j)
  · have hmem (i : ℕ) (hi : i ≤ j) : xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S i) :=
      fun v hv ↦ h v (primaryDivisorialPlaces_mono S hi hv)
    simp [divisorialKernelDifference, divisorialIndicator_eq_indicator, hmem k hkj.le,
      hmem (k + 1) hkj]
  · rw [divisorialIndicator_eq_indicator, Set.indicator_of_notMem h, mul_zero]

variable (F) in
/-- Paper: §11.3.1.1, p. 491, and §11.3.2, p. 495. The S-local idelic
region in the definition of β consists of ideles that are units outside S. -/
def sLocalDivisorialStratum (S : Finset V) : Set I𝔽 :=
  {g | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}

/-- the finite components of an idele and its inverse multiply to one. -/
private theorem mem_sLocalDivisorialStratum_iff_inv_mul {F : Type*} [Field F] [NumberField F]
    (g : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (g⁻¹).val.2 v * g.val.2 v = 1 := by
  change ((g⁻¹ * g : IdeleGroup (𝓞 F) F).val).2 v = 1
  rw [inv_mul_cancel]
  rfl

/-- an idele component has valuation one exactly when it and the inverse component are
integral. -/
private theorem mem_sLocalDivisorialStratum_iff_valued_eq_one {F : Type*} [Field F]
    [NumberField F] (g : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g.val.2 v) = 1 ↔
      g.val.2 v ∈ v.adicCompletionIntegers F ∧ (g⁻¹).val.2 v ∈ v.adicCompletionIntegers F := by
  have h := congrArg Valued.v (mem_sLocalDivisorialStratum_iff_inv_mul g v)
  rw [map_mul, map_one] at h
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h1
    rw [h1, mul_one] at h
    exact ⟨h1.le, h.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v ((g⁻¹).val.2 v) * Valued.v (g.val.2 v) := h.symm
      _ ≤ 1 * Valued.v (g.val.2 v) := mul_le_mul_left h2 _
      _ = Valued.v (g.val.2 v) := one_mul _

/-- Paper: §11.3.2, p. 495. The region of β is the product of the inserted
S-ideles and the outside integer unit group. -/
theorem mem_sLocalDivisorialStratum_iff (S : Finset V) (g : I𝔽) :
    g ∈ sLocalDivisorialStratum F S ↔
      ∃ (a : (SAdeleRing F S)ˣ) (u : outsideIntegralIdeleUnits F S),
        g = sIdeleInsertion F S a * u.val := by
  constructor
  · intro hg
    set b := sIdeleInsertion F S (Units.map (adeleProjection F S).toMonoidHom g)
    obtain ⟨hb1, hbS, hbout⟩ :=
      sIdeleInsertion_apply F S (Units.map (adeleProjection F S).toMonoidHom g)
    have hinv1 : (b⁻¹).val.1 * b.val.1 = 1 := by
      change ((b⁻¹ * b : I𝔽).val).1 = 1
      rw [inv_mul_cancel]
      rfl
    refine ⟨_, ⟨b⁻¹ * g, ?_⟩, (mul_inv_cancel_left b g).symm⟩
    rw [mem_outsideIntegralIdeleUnits_iff]
    refine ⟨?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · change (b⁻¹).val.1 * g.val.1 = 1
      rw [← hinv1, hb1]
      rfl
    · change (b⁻¹).val.2 w * g.val.2 w = 1
      rw [← mem_sLocalDivisorialStratum_iff_inv_mul b w, hbS ⟨w, hw⟩]
      rfl
    · have hbw : (b⁻¹).val.2 w = 1 := by
        have h := mem_sLocalDivisorialStratum_iff_inv_mul b w
        rwa [hbout w hw, mul_one] at h
      have h1 : (b⁻¹ * g).val.2 w = g.val.2 w := by
        change (b⁻¹).val.2 w * g.val.2 w = _
        rw [hbw, one_mul]
      have h2 : ((b⁻¹ * g)⁻¹).val.2 w = (g⁻¹).val.2 w := by
        rw [mul_inv_rev, inv_inv]
        change (g⁻¹).val.2 w * b.val.2 w = _
        rw [hbout w hw, mul_one]
      rw [h1, h2]
      exact (mem_sLocalDivisorialStratum_iff_valued_eq_one g w).1 (hg w hw)
  · rintro ⟨a, ⟨u, hu⟩, rfl⟩ v hv
    obtain ⟨-, -, hu⟩ := (mem_outsideIntegralIdeleUnits_iff u).1 hu
    have hb := (sIdeleInsertion_apply F S a).2.2 v hv
    have hval : (sIdeleInsertion F S a * u).val.2 v = u.val.2 v := by
      change (sIdeleInsertion F S a).val.2 v * u.val.2 v = _
      rw [hb, one_mul]
    rw [hval]
    exact (mem_sLocalDivisorialStratum_iff_valued_eq_one u v).2 (hu v hv)

/-- Paper: §11.3.2, p. 495, and (D.1.10.1), p. 783. The region of β is the range
of the insertion of the ideles integral outside S. -/
theorem sLocalDivisorialStratum_eq_range_integralIdeleInsertion (S : Finset V) :
    sLocalDivisorialStratum F S = Set.range (integralIdeleInsertion F S) := by
  ext g
  rw [mem_range_integralIdeleInsertion]
  change (∀ v ∉ S, Valued.v (g.val.2 v) = 1) ↔ _
  refine forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  let u := Units.map ((RestrictedProduct.evalRingHom (fun w : V ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom g
  change Valued.v u.val = 1 ↔
    u.val ∈ v.adicCompletionIntegers F ∧ u.inv ∈ v.adicCompletionIntegers F
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hinv : Valued.v u.inv = (Valued.v u.val)⁻¹ := by
    rw [show u.inv = u.val⁻¹ from Units.val_inv_eq_inv_val u, map_inv₀]
  rw [hinv, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr u.ne_zero))]
  exact le_antisymm_iff

/-- Paper: §11.3.1.1, pp. 492–493. At a saturated base, the limit of the
descending primary strata is the S-local idelic region. -/
theorem iInter_primaryDivisorialStratum (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋂ k, divisorialStratum F (primaryDivisorialPlaces F S k)) =
      sLocalDivisorialStratum F S := by
  have hplaces := iUnion_primaryDivisorialPlaces S _hS
  ext g
  rw [Set.mem_iInter]
  change (∀ k v, v ∈ primaryDivisorialPlaces F S k → Valued.v (g.val.2 v) = 1) ↔
    ∀ v ∉ S, Valued.v (g.val.2 v) = 1
  constructor
  · intro hg v hv
    have hu : v ∈ ⋃ k, (primaryDivisorialPlaces F S k : Set V) := by
      rw [hplaces]
      exact hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hu
    exact hg k v hk
  · intro hg k v hv
    apply hg v
    have hu : v ∈ ⋃ k, (primaryDivisorialPlaces F S k : Set V) :=
      Set.mem_iUnion.mpr ⟨k, hv⟩
    rwa [hplaces] at hu

/-- Paper: §11.3.1.1, p. 491 and (11.3.1.4), p. 494. The differences telescope
pointwise to the S-local restriction minus the original kernel. For each pair
of ideles at most one difference contributes.
Deviation: The sign here follows (11.3.1.4). The opening display on p. 491
adds the differences where it would need to subtract them. -/
theorem hasSum_divisorialKernelDifference (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    (K : I𝔽 × I𝔽 → ℂ) (xy : I𝔽 × I𝔽) :
    HasSum (fun k ↦ divisorialKernelDifference S k K xy)
      ((sLocalDivisorialStratum F S).indicator (fun _ ↦ K xy) xy.2 - K xy) := by
  classical
  let a : ℕ → ℂ := fun k ↦ divisorialIndicator (primaryDivisorialPlaces F S k) xy.2
  let b := (sLocalDivisorialStratum F S).indicator (fun _ ↦ (1 : ℂ)) xy.2
  have hi := iInter_primaryDivisorialStratum S _hS
  have hmono : Monotone (primaryDivisorialPlaces F S) :=
    monotone_nat_of_le_succ fun k ↦ by
      rw [primaryDivisorialPlaces_succ]
      exact Finset.subset_union_left
  have htail : ∃ N : ℕ, ∀ k ≥ N, a k = b := by
    by_cases h : xy.2 ∈ sLocalDivisorialStratum F S
    · have hall := Set.mem_iInter.mp (hi.symm ▸ h)
      exact ⟨0, fun k _ ↦ by
        simp [a, b, divisorialIndicator_eq_indicator, h, hall k]⟩
    · have hn : ¬ ∀ k, xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S k) :=
        fun hk ↦ h (hi ▸ Set.mem_iInter.mpr hk)
      push_neg at hn
      obtain ⟨N, hN⟩ := hn
      refine ⟨N, fun k hk ↦ ?_⟩
      have hk' : xy.2 ∉ divisorialStratum F (primaryDivisorialPlaces F S k) :=
        fun hg ↦ hN (fun v hv ↦ hg v (hmono hk hv))
      simp [a, b, divisorialIndicator_eq_indicator, h, hk']
  obtain ⟨N, hN⟩ := htail
  have hs : HasSum (fun k ↦ divisorialKernelDifference S k K xy)
      (∑ k ∈ Finset.range N, divisorialKernelDifference S k K xy) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦ by
      have hk' : N ≤ k := Nat.le_of_not_gt (fun h ↦ hk (Finset.mem_range.mpr h))
      change (a (k + 1) - a k) * K xy = 0
      rw [hN k hk', hN (k + 1) (hk'.trans (Nat.le_succ k)), sub_self, zero_mul]
  change HasSum _ ((∑ k ∈ Finset.range N, (a (k + 1) - a k) * K xy)) at hs
  rw [← Finset.sum_mul, Finset.sum_range_sub a, hN N le_rfl] at hs
  have ha : a 0 = 1 := by simp [a, primaryDivisorialPlaces, divisorialIndicator]
  rw [ha, sub_mul, one_mul] at hs
  by_cases h : xy.2 ∈ sLocalDivisorialStratum F S <;> simpa [b, h] using hs

section OrbitalTraces

open scoped ContDiff FourierTransform SchwartzMap

attribute [local instance] instIdeleClassSecondCountableSec1

local notation "𝒟" => BruhatCompactSupport C𝔽
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "q(" v ")" => (v).asIdeal.absNorm

/-- Paper: §11.3.1.1(2), pp. 494–495, and (11.3.2.5), p. 496.
The local summand of the Poisson evaluation integrates the test against the
character on each norm-one coset through a power of the local uniformizer.
Deviation: For the half-shifted Mellin sum the terms carry the norm weight
`qᵥ^(n/2)`. The Haar factor comes from the norm-one idele class measure. -/
def orbitalPlacePoissonTerm (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (n : ℤ) : ℂ :=
  (Real.log (q(v) : ℝ) : ℂ) * (q(v) : ℂ) ^ ((n : ℂ) / 2) *
    ∫ h : C₁, φ.val (πclass(v, π) ^ n * h.val) * (χ h.val : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F

/-- Paper: §11.3.1.1(2), p. 494. At exponent zero and for the trivial
character, the Poisson term is the log residue size times the norm-one integral. -/
theorem orbitalPlacePoissonTerm_trivial_zero (φ : 𝒟) (v : V) (π : (v.adicCompletion F)ˣ) :
    orbitalPlacePoissonTerm 1 φ v π 0 =
      (Real.log (q(v) : ℝ) : ℂ) * ∫ h : C₁, φ.val h.val
        ∂normOneIdeleClassTamagawaMeasure F := by
  simp [orbitalPlacePoissonTerm]

private def orbitalEulerZero (v : V) (t : ℝ) (n : ℤ) : ℂ :=
  ((n : ℂ) * (2 * (Real.pi : ℂ)) / (Real.log (q(v) : ℝ) : ℂ) - (t : ℂ)) *
    Complex.I

private def orbitalEulerZeroEquiv (χ : PontryaginDual C𝔽) (v : V)
    (hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (t : ℝ)
    (ht : (ideleClassNormTwist χ 0).localValue v =
      (q(v) : ℂ) ^ (-(t : ℂ) * Complex.I)) :
    ℤ ≃ {z : ℂ // (finiteHeckeEulerFactor χ v z)⁻¹ = 0} := by
  let L : ℂ := (Real.log (q(v) : ℝ) : ℂ)
  have hq1 : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q(v) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq1).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hz (z : ℂ) : (finiteHeckeEulerFactor χ v z)⁻¹ = 0 ↔
      ∃ k : ℤ, (-z - (t : ℂ) * Complex.I) * L = k * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [finiteHeckeEulerFactor_inv_eq_phase χ v hχ t ht, sub_eq_zero, eq_comm,
      Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log, Complex.exp_eq_one_iff]
    simp only [L, mul_comm (Real.log (q(v) : ℝ) : ℂ)]
  refine Equiv.ofBijective (fun n ↦ ⟨orbitalEulerZero v t n, (hz _).2 ⟨-n, ?_⟩⟩) ?_
  · unfold orbitalEulerZero
    change (-(((n : ℂ) * (2 * (Real.pi : ℂ)) / L - (t : ℂ)) * Complex.I) -
      (t : ℂ) * Complex.I) * L = ((-n : ℤ) : ℂ) * _
    push_cast
    field_simp
    ring
  constructor
  · intro m n h
    apply Int.cast_injective (α := ℂ)
    have h' := congrArg Subtype.val h
    change (((m : ℂ) * (2 * (Real.pi : ℂ)) / L - (t : ℂ)) * Complex.I) =
      (((n : ℂ) * (2 * (Real.pi : ℂ)) / L - (t : ℂ)) * Complex.I) at h'
    apply (mul_left_inj' (show (2 : ℂ) * (Real.pi : ℂ) ≠ 0 from mul_ne_zero (by norm_num) hpi)).mp
    apply (div_left_inj₀ hL).mp
    apply (sub_left_inj).mp
    exact (mul_left_inj' Complex.I_ne_zero).mp h'
  · intro z
    obtain ⟨k, hk⟩ := (hz z).mp z.property
    refine ⟨-k, Subtype.ext ?_⟩
    change ((((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) / L - (t : ℂ)) *
      Complex.I) = z.val
    push_cast
    apply (mul_left_inj' hL).mp
    field_simp
    linear_combination hk

private theorem orbitalSchwartz_hasSum (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun n : ℤ ↦ 𝓕 f (n : ℝ)) (∑' n : ℤ, f (n : ℝ)) := by
  have hs : Summable (fun n : ℤ ↦ 𝓕 f (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have he := f.tsum_eq_tsum_fourier 0
  simp at he
  exact he.symm ▸ hs.hasSum


private def orbitalNormSection (r : ℝ) : C𝔽 :=
  QuotientGroup.mk (canonicalIdeleNormSection F (Units.mk0 (Real.exp r).toNNReal (by positivity)))

private theorem orbitalNormSection_norm (r : ℝ) :
    ideleClassNorm F (orbitalNormSection (F := F) r) =
      Units.mk0 (Real.exp r).toNNReal (by positivity) :=
  canonicalIdeleNormSection_rightInverse F _

private def orbitalLogProfile (χ : PontryaginDual C𝔽) (φ : 𝒟) (L t : ℝ) (x : ℝ) : ℂ :=
  (L : ℂ) * ∫ h : C₁, φ.val (orbitalNormSection (-L * x) * h.val) *
    ideleClassNormTwist χ (-(1 : ℂ) / 2 - (t : ℂ) * Complex.I)
      (orbitalNormSection (-L * x) * h.val) ∂normOneIdeleClassTamagawaMeasure F

private theorem orbitalLogProfile_at_int (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val) (t : ℝ)
    (ht : ∀ (s : ℂ) (x : (v.adicCompletion F)ˣ),
      finitePlaceRestriction F v (ideleClassNormTwist χ s) x =
        ((‖x.val‖ : ℝ) : ℂ) ^ (s + (t : ℂ) * Complex.I)) (n : ℤ) :
    orbitalLogProfile χ φ (Real.log (q(v) : ℝ)) t (n : ℝ) =
      orbitalPlacePoissonTerm χ φ v π n := by
  let L := Real.log (q(v) : ℝ)
  let g := πclass(v, π) ^ n
  let σ := orbitalNormSection (F := F) (-L * n)
  let ψ := ideleClassNormTwist χ (-(1 : ℂ) / 2 - (t : ℂ) * Complex.I)
  have hq : (0 : ℝ) < q(v) := by exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hgpow : πclass(v, π ^ n) = g :=
    map_zpow (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) π n
  have hnorm : ‖(π ^ n).val‖ = (q(v) : ℝ) ^ (-n) := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_uniformizer_adicCompletion v _ hπ,
      inv_zpow', zpow_neg]
  have hgn : (((ideleClassNorm F g).val : ℝ≥0) : ℝ) = (q(v) : ℝ) ^ (-n) := by
    rw [← hgpow, ideleClassNorm_ofAdicCompletion, Units.coe_map]
    exact hnorm
  have hσ : ideleClassNorm F σ = ideleClassNorm F g := by
    apply Units.ext
    apply NNReal.eq
    rw [show ideleClassNorm F σ = _ from orbitalNormSection_norm _, hgn]
    rw [Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos _).le, ← Real.rpow_intCast, Real.rpow_def_of_pos hq]
    congr 1
    push_cast
    unfold L
    ring
  have hk : ideleClassNorm F (g⁻¹ * σ) = 1 := by rw [map_mul, map_inv, hσ, inv_mul_cancel]
  let k : C₁ := ⟨g⁻¹ * σ, hk⟩
  let A (h : C₁) := φ.val (g * h.val) * ψ (g * h.val)
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have htranslate :
      ∫ h : C₁, φ.val (σ * h.val) * ψ (σ * h.val) ∂normOneIdeleClassTamagawaMeasure F =
        ∫ h, A h ∂normOneIdeleClassTamagawaMeasure F := by
    rw [← integral_mul_left_eq_self A k]
    apply integral_congr_ae
    filter_upwards with h
    have he : g * (k * h).val = σ * h.val := by
      change g * ((g⁻¹ * σ) * h.val) = _
      rw [mul_assoc g⁻¹ σ, mul_inv_cancel_left]
    simp only [A, he]
  have hψ : ψ g = (q(v) : ℂ) ^ ((n : ℂ) / 2) := by
    have hlocal := ht (-(1 : ℂ) / 2 - (t : ℂ) * Complex.I) (π ^ n)
    change ψ (πclass(v, π ^ n)) = _ at hlocal
    rw [hgpow, hnorm, sub_add_cancel] at hlocal
    rw [hlocal, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq (-n)).ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne')]
    rw [← Complex.ofReal_log (zpow_pos hq (-n)).le, Real.log_zpow, ← Complex.natCast_log]
    congr 1
    push_cast
    ring
  have hfactor (h : C₁) : A h = (q(v) : ℂ) ^ ((n : ℂ) / 2) *
      (φ.val (g * h.val) * (χ h.val : ℂ)) := by
    have hc : ψ h.val = (χ h.val : ℂ) := by
      change (χ h.val : ℂ) * (((ideleClassNorm F h.val).val : ℝ) : ℂ) ^
        (-(1 : ℂ) / 2 - (t : ℂ) * Complex.I) = (χ h.val : ℂ)
      rw [show ideleClassNorm F h.val = 1 from h.property]
      simp
    unfold A
    rw [map_mul, hc, hψ]
    ring
  change (L : ℂ) * (∫ h : C₁, φ.val (σ * h.val) * ψ (σ * h.val)
      ∂normOneIdeleClassTamagawaMeasure F) = _
  rw [htranslate]
  simp_rw [hfactor, integral_const_mul]
  exact (mul_assoc _ _ _).symm

private theorem orbitalNormSection_mul_norm (r : ℝ) (h : C₁) :
    (((ideleClassNorm F (orbitalNormSection r * h.val)).val : ℝ≥0) : ℝ) = Real.exp r := by
  rw [map_mul, show ideleClassNorm F h.val = 1 from h.property, mul_one, orbitalNormSection_norm,
    Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos r).le]

private theorem orbitalCompactSupport_mem_schwartz (φ : 𝒟) :
    φ.val ∈ schwartzBruhatSubmodule C𝔽 := by
  obtain ⟨m, _, hm, hms⟩ := exists_ideleClassModulation F
  have hf := bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms φ.property
  rwa [modulatedExponentialDecaySubmodule_singleton_zero] at hf

/-- The character-weighted coset integral is smooth on the logarithmic norm line. -/
private theorem orbitalCharacterAverage_contDiff (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ContDiff ℝ (∞) (fun x : ℝ ↦ ∫ h : C₁,
      (χ (orbitalNormSection x * h.val) : ℂ) * φ.val (orbitalNormSection x * h.val)
        ∂normOneIdeleClassTamagawaMeasure F) := by
  let c : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hc : Continuous c :=
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hcr : RightInverse c (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let eQ := normQuotientEquiv (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
    c hc hcr
  let e : (C𝔽 ⧸ C₁) ≃ₜ* Multiplicative ℝ := eQ.trans positiveRealLogEquiv
  have he (x : ℝ) : (e (QuotientGroup.mk (orbitalNormSection x))).toAdd = x := by
    change (positiveRealLogEquiv (ideleClassNorm F (orbitalNormSection x))).toAdd = _
    rw [positiveRealLogEquiv_apply, orbitalNormSection_norm, Units.val_mk0,
      Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  let f₀ : SchwartzBruhat C𝔽 := ⟨φ.val, orbitalCompactSupport_mem_schwartz φ⟩
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_characterEquiv (G := C𝔽) χ
  have hK : IsCompact (C₁ : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : (normOneIdeleClassTamagawaMeasure F).Regular :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  let f₁ := schwartzBruhatCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (P f₀)
  let : CommGroup (C𝔽 ⧸ C₁) := QuotientGroup.Quotient.commGroup C₁
  let : T2Space (C𝔽 ⧸ C₁) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (C𝔽 ⧸ C₁) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨T, hT⟩ := schwartzBruhat_realCoordinate_equiv (G := C𝔽 ⧸ C₁) e
  let b : 𝓢(ℝ, ℂ) := T.symm f₁
  have hB : T b = f₁ := T.apply_symm_apply f₁
  have hb (x : ℝ) : b x = ∫ h : C₁, (χ (orbitalNormSection x * h.val) : ℂ) *
      φ.val (orbitalNormSection x * h.val) ∂normOneIdeleClassTamagawaMeasure F := by
    let q : C𝔽 ⧸ C₁ := QuotientGroup.mk (orbitalNormSection x)
    have hx : (e q).toAdd = x := he x
    calc
      b x = T b q := (congrArg b hx).symm.trans (hT b q).symm
      _ = f₁ q := congrArg (fun g : SchwartzBruhat (C𝔽 ⧸ C₁) ↦ g q) hB
      _ = ∫ h : C₁, (P f₀) (orbitalNormSection x * h.val) ∂normOneIdeleClassTamagawaMeasure F :=
        schwartzBruhatCosetIntegral_mk C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (P f₀) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        exact hP f₀ (orbitalNormSection x * h.val)
  have hb' : (b : ℝ → ℂ) = _ := funext hb
  exact hb' ▸ b.smooth'

/-- The real rescaling and the norm twist preserve smoothness of the coset integral. -/
private theorem orbitalLogProfile_contDiff (χ : PontryaginDual C𝔽) (φ : 𝒟)
    (L t : ℝ) : ContDiff ℝ (∞) (orbitalLogProfile χ φ L t) := by
  let ψ := -(1 : ℂ) / 2 - (t : ℂ) * Complex.I
  let A (x : ℝ) := ∫ h : C₁, (χ (orbitalNormSection x * h.val) : ℂ) *
    φ.val (orbitalNormSection x * h.val) ∂normOneIdeleClassTamagawaMeasure F
  have hprofile : orbitalLogProfile χ φ L t =
      fun x ↦ (L : ℂ) * (A (-L * x) * Complex.exp (ψ * ((-L * x : ℝ) : ℂ))) := by
    funext x
    unfold orbitalLogProfile A
    rw [← integral_mul_const]
    congr 1
    apply integral_congr_ae
    filter_upwards with h
    change φ.val _ * ((χ _ : ℂ) * (((ideleClassNorm F _).val : ℝ) : ℂ) ^ ψ) = _
    rw [orbitalNormSection_mul_norm,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-L * x)).ne'),
      ← Complex.ofReal_log (Real.exp_pos (-L * x)).le, Real.log_exp]
    rw [mul_comm ((-L * x : ℝ) : ℂ) ψ, ← mul_assoc, mul_comm (φ.val _) (χ _ : ℂ)]
  rw [hprofile]
  have hcomp : ContDiff ℝ (∞) (fun x : ℝ ↦ -L * x) := contDiff_const.mul contDiff_id
  exact contDiff_const.mul (((orbitalCharacterAverage_contDiff χ φ).comp hcomp).mul
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hcomp)).cexp))

/-- The rescaled log norm of the Bruhat support contains the support of the average. -/
private theorem orbitalLogProfile_hasCompactSupport (χ : PontryaginDual C𝔽) (φ : 𝒟)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasCompactSupport (orbitalLogProfile χ φ L t) := by
  let r (g : C𝔽) : ℝ := -(Real.log (((ideleClassNorm F g).val : ℝ≥0) : ℝ)) / L
  have hr : Continuous r := by
    have hn : Continuous (fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
    change Continuous (fun g : C𝔽 ↦ -Real.log ((ideleClassNorm F g).val : ℝ) / L)
    exact (hn.log (fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))).ne')).neg.div_const L
  refine HasCompactSupport.intro ((show HasCompactSupport φ.val from φ.property.2).image hr) ?_
  intro x hx
  unfold orbitalLogProfile
  refine mul_eq_zero_of_right _ ?_
  apply integral_eq_zero_of_ae
  filter_upwards with h
  have hφ : φ.val (orbitalNormSection (-L * x) * h.val) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine ⟨_, hmem, ?_⟩
    unfold r
    rw [orbitalNormSection_mul_norm, Real.log_exp]
    field_simp
  simp only [hφ, zero_mul, Pi.zero_apply]

private theorem orbitalLogProfile_schwartz (χ : PontryaginDual C𝔽) (φ : 𝒟)
    {L : ℝ} (hL : 0 < L) (t : ℝ) :
    ∃ f : 𝓢(ℝ, ℂ), ⇑f = orbitalLogProfile χ φ L t :=
  ⟨(orbitalLogProfile_hasCompactSupport χ φ hL t).toSchwartzMap
    (orbitalLogProfile_contDiff χ φ L t), rfl⟩

/-- Weil integration of a test in the real norm coordinate. -/
private theorem orbitalEulerSum_logNorm_integral (σ : ℝ≥0ˣ → C𝔽) (hσ : Continuous σ)
    (hσnorm : RightInverse σ (ideleClassNorm F)) (f : C𝔽 → ℂ)
    (hf : Integrable f (ideleClassTamagawaMeasure F)) :
    (∫ g, f g ∂ideleClassTamagawaMeasure F) = ∫ y : ℝ,
      ∫ h : C₁, f (σ (Units.mk0 (Real.exp y).toNNReal (by positivity)) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let j (p : ℝ≥0ˣ × C₁) := σ p.1 * p.2.val
  have hj : Measurable j :=
    ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
  let p := positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)
  have hmap : p.map j = ideleClassTamagawaMeasure F := classTamagawa_normProduct σ hσ hσnorm
  have hm : AEStronglyMeasurable f (p.map j) := hmap ▸ hf.aestronglyMeasurable
  have hi : Integrable (f ∘ j) p :=
    (integrable_map_measure hm hj.aemeasurable).mp (hmap ▸ hf)
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (y : ℝ) : e y = Units.mk0 (Real.exp y).toNNReal (by positivity) :=
    Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le).symm)
  have hE : positiveRealHaar = volume.map e := by
    unfold positiveRealHaar
    congr 1
    exact funext fun y ↦ (he y).symm
  rw [← hmap, integral_map hj.aemeasurable hm]
  change (∫ z, (f ∘ j) z ∂positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)) = _
  rw [integral_prod (f ∘ j) hi, hE]
  calc
    _ = ∫ y : ℝ, ∫ h : C₁, f (σ (e y) * h.val) ∂normOneIdeleClassTamagawaMeasure F :=
      integral_map_equiv e.toMeasurableEquiv _
    _ = _ := by simp only [he]


/-- Change of scale for the real Fourier integral. -/
private theorem orbitalEulerSum_fourier_scale (A : ℝ → ℂ) {L : ℝ} (hL : 0 < L) (n : ℤ) :
    𝓕 (fun x : ℝ ↦ (L : ℂ) * A (-L * x)) (n : ℝ) =
      ∫ y : ℝ, Complex.exp ((y : ℂ) * ((2 * (Real.pi : ℂ) * (n : ℂ) / L) * Complex.I)) * A y := by
  let g (y : ℝ) := Complex.exp ((y : ℂ) * ((2 * (Real.pi : ℂ) * (n : ℂ) / L) * Complex.I)) * A y
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * (n : ℝ)) * Complex.I) •
      ((L : ℂ) * A (-L * x)) = (L : ℂ) * g (-L * x) := by
    rw [smul_eq_mul, mul_left_comm]
    dsimp only [g]
    congr 3
    push_cast
    field_simp [show (L : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hL.ne']
  simp_rw [h, integral_const_mul]
  rw [Measure.integral_comp_mul_left]
  simp only [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hL), Complex.real_smul, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]


/-- The Fourier samples of the scaled norm-one average are shifted Mellin values. -/
private theorem orbitalEulerSum_profile_fourier (χ : PontryaginDual C𝔽)
    (φ : 𝒟) {L : ℝ} (hL : 0 < L) (t : ℝ) (n : ℤ) :
    𝓕 (orbitalLogProfile χ φ L t) (n : ℝ) = nuclearityTestMellin χ φ
      (-(1 : ℂ) / 2 - (t : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * (n : ℂ) / L) * Complex.I) := by
  let σ : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hσ : Continuous σ :=
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hσnorm : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let b : ℂ := -(1 : ℂ) / 2 - (t : ℂ) * Complex.I
  let d : ℂ := (2 * (Real.pi : ℂ) * (n : ℂ) / L) * Complex.I
  let f (w : ℂ) (g : C𝔽) := φ.val g * ideleClassNormTwist χ w g
  let e (x : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  let A (y : ℝ) := ∫ h : C₁, f b (σ (e y) * h.val) ∂normOneIdeleClassTamagawaMeasure F
  change 𝓕 (fun x : ℝ ↦ (L : ℂ) * A (-L * x)) (n : ℝ) =
    ∫ g, f (b + d) g ∂ideleClassTamagawaMeasure F
  rw [orbitalEulerSum_fourier_scale A hL n, orbitalEulerSum_logNorm_integral σ hσ hσnorm
    (f (b + d))
    ((nuclearityTestMellin_integrable χ φ).1 (b + d))]
  apply integral_congr_ae
  filter_upwards with y
  change Complex.exp ((y : ℂ) * d) * (∫ h : C₁, f b (σ (e y) * h.val)
    ∂normOneIdeleClassTamagawaMeasure F) = ∫ h : C₁, f (b + d) (σ (e y) * h.val)
      ∂normOneIdeleClassTamagawaMeasure F
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with h
  have hN : ideleClassNorm F (σ (e y) * h.val) = e y := by
    rw [map_mul, hσnorm, MonoidHom.mem_ker.mp h.property, mul_one]
  dsimp only [f]
  change Complex.exp ((y : ℂ) * d) * (φ.val _ * ((χ _ : ℂ) *
    (((ideleClassNorm F (σ (e y) * h.val)).val : ℝ) : ℂ) ^ b)) =
    φ.val _ * ((χ _ : ℂ) * (((ideleClassNorm F (σ (e y) * h.val)).val : ℝ) : ℂ) ^ (b + d))
  rw [hN, show ((e y).val : ℝ) = Real.exp y from Real.coe_toNNReal _ (Real.exp_pos y).le]
  have hn : (Real.exp y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'
  rw [Complex.cpow_add _ _ hn, Complex.cpow_def_of_ne_zero hn d,
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
  ring


/-- Paper: §11.3.1.1(2), p. 494, and (11.3.2.5), p. 496.
For one unramified place, the half-shifted Mellin values at the zeros of its
reciprocal Euler factor sum to its norm-one coset contributions.
Deviation: Uses the angular integral and half-shift weight of the repaired formula.
This is the analytic part of the split: decompose the Mellin integral along the
norm fibres and apply Poisson summation in the logarithmic norm coordinate. -/
private theorem orbitalEulerSum_eq_poisson_local (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F))
    (hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    HasSum (fun z : {z : ℂ // (finiteHeckeEulerFactor χ v z)⁻¹ = 0} ↦
      nuclearityTestMellin χ φ (z.val - 1 / 2))
      (∑' n : ℤ, orbitalPlacePoissonTerm χ φ v π n) := by
  obtain ⟨t, ⟨_, ht, hphase⟩, _⟩ := unramifiedHeckeCharacter_existsUnique_phase χ v hχ π hπ
  have ht' : (ideleClassNormTwist χ 0).localValue v =
      (q(v) : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    rw [hχ.localValue_eq π hπ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    exact ht
  let e := orbitalEulerZeroEquiv χ v hχ t ht'
  let L := Real.log (q(v) : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  obtain ⟨f, hf⟩ := orbitalLogProfile_schwartz χ φ hL t
  have hvalues (n : ℤ) : f (n : ℝ) = orbitalPlacePoissonTerm χ φ v π n := by
    rw [show f (n : ℝ) = orbitalLogProfile χ φ L t n from congrFun hf n]
    exact orbitalLogProfile_at_int χ φ v π hπ t hphase n
  have hfourier (n : ℤ) : 𝓕 f (n : ℝ) = nuclearityTestMellin χ φ ((e n).val - 1 / 2) := by
    change 𝓕 (f : ℝ → ℂ) (n : ℝ) = _
    rw [hf, orbitalEulerSum_profile_fourier χ φ hL t n]
    congr 1
    change -(1 : ℂ) / 2 - (t : ℂ) * Complex.I +
      (2 * (Real.pi : ℂ) * (n : ℂ) / (L : ℂ)) * Complex.I = orbitalEulerZero v t n - 1 / 2
    unfold orbitalEulerZero L
    ring
  apply e.hasSum_iff.mp
  have hs := orbitalSchwartz_hasSum f
  simp_rw [hvalues] at hs
  exact hs.congr_fun (fun n ↦ (hfourier n).symm)

/-- Paper: §11.3.1.1(2), p. 494.
Adding the local zero sums counts a shared zero once for each vanishing factor,
which is exactly its multiplicity in the reciprocal Euler product. -/
private theorem orbitalEulerSum_eq_poisson_assemble (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : HeightOneSpectrum (𝓞 F) → ℂ)
    (hs : ∀ v ∈ S, HasSum
      (fun z : {z : ℂ // (finiteHeckeEulerFactor χ v z)⁻¹ = 0} ↦
        nuclearityTestMellin χ φ (z.val - 1 / 2)) (a v)) :
    HasSum (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ S z = 0} ↦
      (orbitalEulerMultiplicity χ S z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2)) (∑ v ∈ S, a v) := by
  classical
  let f : ℂ → ℂ := fun z ↦ nuclearityTestMellin χ φ (z - 1 / 2)
  have hv (v) (hv : v ∈ S) :
      HasSum ({z : ℂ | (finiteHeckeEulerFactor χ v z)⁻¹ = 0}.indicator f) (a v) :=
    hasSum_subtype_iff_indicator.mp (hs v hv)
  have h := hasSum_sum hv
  have he (z : ℂ) :
      (∑ v ∈ S, {z : ℂ | (finiteHeckeEulerFactor χ v z)⁻¹ = 0}.indicator f z) =
        (orbitalEulerMultiplicity χ S z : ℂ) * f z := by
    rw [orbitalEulerMultiplicity_eq_card]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [← Finset.sum_filter]
    simp
  have hglobal : HasSum (fun z : ℂ ↦ (orbitalEulerMultiplicity χ S z : ℂ) * f z)
      (∑ v ∈ S, a v) := h.congr_fun (fun z ↦ (he z).symm)
  apply (hasSum_subtype_iff_of_support_subset (s :=
    {z : ℂ | reciprocalPartialHeckeEulerProduct χ S z = 0}) ?_).mpr hglobal
  intro z hz
  by_contra hn
  have hnone : ∀ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹ ≠ 0 := by
    intro v hv hzv
    exact hn (Finset.prod_eq_zero hv hzv)
  have hzero : orbitalEulerMultiplicity χ S z = 0 := by
    rw [orbitalEulerMultiplicity_eq_card, Finset.filter_eq_empty_iff.mpr hnone]
    rfl
  exact hz (by simp [hzero])

/-- Paper: §11.3.1.1(2), p. 494, and (11.3.2.5), p. 496.
The half-shifted Mellin values at the zeros of the reciprocal Euler product sum,
with multiplicity, to the Poisson contributions of the places over the prime.
Deviation: This is the Poisson evaluation of the spectral expression. A layer
uses all its places, with the angular integral and the half-shift weight. -/
theorem orbitalEulerSum_eq_poisson (χ : PontryaginDual C𝔽) (φ : 𝒟) (p : Vℚ)
    (_hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    let zeros := {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0}
    HasSum (fun z : zeros ↦ (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
      nuclearityTestMellin χ φ (z.val - 1 / 2))
      (∑ v ∈ above(p), ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n) := by
  exact orbitalEulerSum_eq_poisson_assemble F χ φ above(p)
    (fun v ↦ ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n)
    (fun v hv ↦ orbitalEulerSum_eq_poisson_local F χ φ v (_hχ v hv) (π v) (_hπ v hv))

/-- Paper: §11.3.1.1(2), pp. 494–495. If the test is supported at norms
strictly between one and the residue size, every summand at that place vanishes. -/
theorem orbitalPlacePoissonTerm_eq_zero (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (_hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈ Ioo 1 (q(v) : ℝ)})
    (n : ℤ) :
    orbitalPlacePoissonTerm χ φ v π n = 0 := by
  have hz : ∀ h : C₁, φ.val (πclass(v, π) ^ n * h.val) = 0 := by
    intro h
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hm := _hφ hmem
    simp only [Set.mem_setOf_eq] at hm
    have h1 : ideleClassNorm F h.val = 1 := h.2
    have hq : (1 : ℝ) < q(v) := by
      exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.2
        ⟨(Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)).ne', by
          intro h0; exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h0)⟩
    have hn : (((ideleClassNorm F (πclass(v, π) ^ n * h.val)).val : ℝ≥0) : ℝ) =
        (q(v) : ℝ) ^ (-n) := by
      rw [map_mul, map_zpow, ideleClassNorm_ofAdicCompletion, h1, mul_one]
      rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Units.coe_map]
      change ‖π.val‖ ^ n = _
      rw [norm_uniformizer_adicCompletion v _ _hπ, inv_zpow', zpow_neg]
    rw [hn] at hm
    obtain ⟨hm1, hm2⟩ := hm
    rcases lt_trichotomy n 0 with h0 | h0 | h0
    · have : (q(v) : ℝ) ≤ (q(v) : ℝ) ^ (-n) := by
        calc (q(v) : ℝ) = (q(v) : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
          _ ≤ _ := zpow_le_zpow_right₀ hq.le (by omega)
      linarith
    · subst h0; simp at hm1
    · have : (q(v) : ℝ) ^ (-n) ≤ 1 := zpow_le_one_of_nonpos₀ hq.le (by omega)
      linarith
  unfold orbitalPlacePoissonTerm
  simp_rw [hz, zero_mul]
  simp

/-- Paper: §11.3.1.1(2), pp. 494–495. For a fixed compactly supported test
above norm one, only finitely many finite places contribute to the Poisson sum.
Deviation: The vanishing applies to the Poisson terms in (11.3.2.5).
Their identification with masses of geometric kernels requires a separate argument. -/
theorem finite_support_orbitalPlacePoisson (χ : PontryaginDual C𝔽) (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)})
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    {v : V | ∃ n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n ≠ 0}.Finite := by
  let normReal : C𝔽 → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hc : Continuous normReal :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hcomp : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨B, hB⟩ := hcomp.bddAbove_image hc.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F) N).subset ?_
  intro v hv
  change q(v) ≤ N
  by_contra! hNv
  obtain ⟨n, hn⟩ := hv
  apply hn
  apply orbitalPlacePoissonTerm_eq_zero χ φ v (π v) (_hπ v) _ n
  intro g hg
  exact ⟨_hφ hg, (hB ⟨g, hg, rfl⟩).trans_lt (hN.trans (by exact_mod_cast hNv))⟩

/-- Paper: (11.3.2.2), p. 495. The printed weight averages products of the
two translated section indicators over the norm-one fundamental domain and
then sums over nonzero principal ideles.
Deviation: The domain is explicit and the right-hand side is a scalar weight. -/
def orbitalSectionWeight (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽) (xy : I𝔽 × I𝔽) : ℝ :=
  ∑' ξ : Fˣ, ∫ g in E,
    (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
      (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2)
      ∂normOneIdeleTamagawaMeasure F

private theorem local_principalUnits {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] :
    ∃ u : ℕ → Lˣ, Filter.Tendsto u Filter.atTop (nhds 1) ∧ (∀ n, ‖(u n : L)‖ = 1) ∧ ∀ n, u n ≠ 1 := by
  obtain ⟨π, hpos, hlt⟩ := NormedField.exists_norm_lt_one L
  let a (n : ℕ) := π ^ (n + 1)
  have ha (n : ℕ) : ‖a n‖ < 1 := by
    change ‖π ^ (n + 1)‖ < 1
    rw [norm_pow]
    exact pow_lt_one₀ hpos.le hlt n.succ_ne_zero
  have hne (n : ℕ) : 1 + a n ≠ 0 := by
    intro he
    have h := ha n
    rw [show a n = -1 by linear_combination he, norm_neg, norm_one] at h
    exact lt_irrefl _ h
  let u (n : ℕ) := Units.mk0 (1 + a n) (hne n)
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff]
    have hlim : Filter.Tendsto a Filter.atTop (nhds (0 : L)) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).comp (Filter.tendsto_add_atTop_nat 1)
    have h1 : Filter.Tendsto (fun n : ℕ ↦ (1 : L) + a n) Filter.atTop (nhds (1 + 0)) := tendsto_const_nhds.add hlim
    rw [add_zero] at h1
    simpa only [Function.comp_def, u, Units.val_mk0, Units.val_one] using h1
  · intro n
    change ‖1 + a n‖ = 1
    have hlow : (1 : ℝ) ≤ max ‖1 + a n‖ ‖a n‖ := by
      have h := IsUltrametricDist.norm_add_le_max (1 + a n) (-(a n))
      simpa using h
    have hge : (1 : ℝ) ≤ ‖1 + a n‖ := by
      by_contra h
      rw [not_le] at h
      exact absurd (max_lt h (ha n)) (not_lt.mpr hlow)
    have hle : ‖1 + a n‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max (1 : L) (a n)).trans (max_le norm_one.le (ha n).le)
    linarith
  · intro n h
    exact pow_ne_zero _ (norm_pos_iff.mp hpos) (add_eq_left.mp (congrArg Units.val h))


/-- The idele with a unit of norm one at one finite place and 1 elsewhere has idele norm one. -/
private theorem ideleNorm_ofAdicCompletion_of_norm_one (v : V) (u : (v.adicCompletion F)ˣ)
    (hu : ‖(u : v.adicCompletion F)‖ = 1) :
    ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
  classical
  let g := IdeleGroup.ofAdicCompletion (𝓞 F) F v u
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm F g : ℝ≥0) : ℝ) = 1
  rw [((ideleNorm_spec F).1 g).2]
  change (∏ w : InfinitePlace F, ‖(1 : w.Completion)‖ ^ w.mult) *
    ∏ᶠ w, ‖RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v u.val w‖ =
    ((1 : ℝ≥0ˣ) : ℝ)
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul, Units.val_one, NNReal.coe_one]
  rw [finprod_eq_single _ v]
  · rw [RestrictedProduct.mulSingle_eq_same]
    exact hu
  · intro w hw
    rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, norm_one]

/-- Inserting a finite completion into the idele group is continuous. -/
private theorem continuous_ideleGroup_ofAdicCompletion (v : V) :
    Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) := by
  classical
  apply Continuous.units_map
  apply continuous_const.prodMk
  apply continuous_restrictedProduct_of_uniform
  · intro w
    exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : V ↦ u.adicCompletion F) v)
  · filter_upwards [Filter.eventually_cofinite_ne v] with w hw x
    change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
    rw [Pi.mulSingle_eq_of_ne hw]
    exact (w.adicCompletionIntegers F).one_mem

/-- The single-place insertion is injective. -/
private theorem ofAdicCompletion_injective (v : V) {x : (v.adicCompletion F)ˣ}
    (hx : IdeleGroup.ofAdicCompletion (𝓞 F) F v x = 1) : x = 1 := by
  have hv := congrArg (fun d : I𝔽 ↦ d.val.2 v) hx
  have hcoord : (IdeleGroup.ofAdicCompletion (𝓞 F) F v x).val.2 v = x.val := by
    change RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v x.val v = x.val
    exact RestrictedProduct.mulSingle_eq_same ..
  rw [hcoord] at hv
  simp at hv
  exact Units.val_eq_one.mp hv


open scoped Valued in
/-- The norm-one ideles have no isolated point: a sequence of principal units at one
finite place gives ideles of norm one tending to one but never equal to it. -/
private theorem nhdsNE_neBot_normOne (v : V) : Filter.NeBot (nhdsWithin (1 : N𝔽) {1}ᶜ) := by
  classical
  obtain ⟨u, hu_tend, hu_norm, hu_ne⟩ := local_principalUnits (L := v.adicCompletion F)
  have hcont : Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) :=
    continuous_ideleGroup_ofAdicCompletion v
  let φ (n : ℕ) : N𝔽 :=
    ⟨IdeleGroup.ofAdicCompletion (𝓞 F) F v (u n), by
      rw [MonoidHom.mem_ker]
      exact ideleNorm_ofAdicCompletion_of_norm_one v (u n) (hu_norm n)⟩
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_frequently, Filter.frequently_iff]
  intro U hU
  rw [show nhds (1 : N𝔽) = (nhds (1 : I𝔽)).comap (Subtype.val : N𝔽 → I𝔽) from nhds_induced _ _] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  have hpre : (IdeleGroup.ofAdicCompletion (𝓞 F) F v) ⁻¹' W ∈ nhds (1 : (v.adicCompletion F)ˣ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hW)
  obtain ⟨n, hn⟩ := (hu_tend.eventually hpre).exists
  refine ⟨φ n, hWU hn, ?_⟩
  intro hEq
  have h1 : u n = 1 := by
    apply ofAdicCompletion_injective v
    exact congrArg Subtype.val hEq
  exact hu_ne n h1


/-- The norm-one Tamagawa measure gives measure zero to singletons. -/
private theorem normOneIdeleTamagawaMeasure_nullSingleton (v : V) :
    NullSingletonClass (normOneIdeleTamagawaMeasure F) := by
  have htop : IsTopologicalGroup I𝔽 := (ideleGroup_topology F).2.2.1
  have hcl : IsClosed ((ideleNorm F).ker : Set I𝔽) := (ideleGroup_topology F).2.2.2.2.2
  let : IsTopologicalGroup I𝔽 := htop
  let : LocallyCompactSpace I𝔽 := (ideleGroup_topology F).2.1
  let : T2Space I𝔽 := (ideleGroup_topology F).1
  let : LocallyCompactSpace N𝔽 := hcl.locallyCompactSpace
  let : BorelSpace I𝔽 := ⟨rfl⟩
  let : BorelSpace N𝔽 := ⟨by rw [borel_comap]; rfl⟩
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have hbot : Filter.NeBot (nhdsWithin (1 : N𝔽) {1}ᶜ) := nhdsNE_neBot_normOne v
  exact MeasureTheory.Measure.IsHaarMeasure.nullSingletonClass _


/-- A number field has a finite place. -/
private theorem finitePlace_nonempty (F : Type*) [Field F] [NumberField F] :
    Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨m, hm.isPrime, NeZero.ne m⟩⟩

/-- Paper: (11.3.2.2), p. 495. The displayed weight vanishes everywhere.
For each principal multiplier, the first translated section condition forces
the integration variable into a single Haar-null point.
Deviation: The printed weight cannot implement a normalized indentation. -/
theorem orbitalSectionWeight_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (xy : I𝔽 × I𝔽) :
    orbitalSectionWeight E τ xy = 0 := by
  classical
  have hτ : RightInverse τ (ideleNorm F) := _hτ
  obtain ⟨v⟩ := finitePlace_nonempty F
  haveI hns : NullSingletonClass (normOneIdeleTamagawaMeasure F) :=
    normOneIdeleTamagawaMeasure_nullSingleton v
  have hprincipal (ξ : Fˣ) : ideleNorm F (principal ξ) = 1 := by
    have h : principal ξ ∈ (ideleNorm F).ker := (ideleNorm_spec F).2 ⟨ξ, rfl⟩
    simpa using h
  have hterm : ∀ ξ : Fˣ, ∫ g in E,
      (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
        (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2)
        ∂normOneIdeleTamagawaMeasure F = 0 := by
    intro ξ
    let g₀ : N𝔽 := ⟨(principal ξ)⁻¹ * τ (ideleNorm F xy.1) * (xy.1)⁻¹, by
      rw [MonoidHom.mem_ker]
      have hτ' : ∀ t : ℝ≥0ˣ, ideleNorm F (τ t) = t := hτ
      simp only [map_mul, map_inv, hprincipal, hτ', inv_one, one_mul]
      simp⟩
    have hsupp : ∀ᵐ g ∂(normOneIdeleTamagawaMeasure F |>.restrict E),
        (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
          (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2) = 0 := by
      filter_upwards [Measure.ae_ne (normOneIdeleTamagawaMeasure F |>.restrict E) g₀]
        with g hg
      by_cases h1 : principal ξ * g.val * xy.1 ∈ Set.range τ
      · exfalso
        apply hg
        obtain ⟨t, ht⟩ := h1
        have hg1 : ideleNorm F (g : I𝔽) = 1 := MonoidHom.mem_ker.mp g.property
        have hnorm : t = ideleNorm F xy.1 := by
          have h := congrArg (ideleNorm F) ht
          rw [hτ] at h
          simp only [map_mul, hprincipal, hg1, one_mul] at h
          exact h
        have hg' : g.val = (principal ξ)⁻¹ * τ t * (xy.1)⁻¹ := by
          rw [ht]
          group
        apply Subtype.ext
        rw [hg', hnorm]
      · rw [Set.indicator_of_notMem h1, zero_mul]
    rw [integral_eq_zero_of_ae hsupp]
  unfold orbitalSectionWeight
  simp [hterm]

/-- Paper: (11.3.2.1) and (11.3.2.3)–(11.3.2.4), pp. 495–496.
The printed weight gives a zero skew-diagonal integral for any kernel,
including when the cutoff and further indicators are absorbed into it. -/
theorem orbitalSectionWeight_skewIntegral_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (K : I𝔽 × I𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
      let xy := (τ t, principal ξ * g.val * τ t)
      (orbitalSectionWeight E τ xy : ℂ) * K xy
      ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by
  simp [orbitalSectionWeight_eq_zero E τ _hτ]

-- TODO(paper-gap): Theorem 11.3.2.1 (11.3.2.1) cannot use the weight (11.3.2.2).
-- A normalized lift and a shell-by-shell identification with the trace operator
-- are missing. The total skew-diagonal formula of §12.2 does not give these.
-- TODO(paper-gap): The proof of (11.3.2.3)–(11.3.2.5) gives no support bound for
-- a repaired lift, and the original primary indicators cut out the new place
-- once that place enters the index. A separate tail based at S′ and proof of the
-- cutoff limit on the global Paley–Wiener subquotients are needed.

end OrbitalTraces

end RiemannMasullo
