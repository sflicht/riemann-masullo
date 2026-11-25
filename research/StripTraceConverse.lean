import research.StripGramConverse
import research.StripMellinPolynomial

/-!
# The rational component of the finite Gram sum and zeta coefficients

Sample the rightmost point of each prescribed Mellin circle and select a
single site in the outer sum. Uniform boundedness for homogeneous tests
gives polynomial bounds simultaneously for every finite Gram block. The
arithmetic criterion then follows from the finite-block Jensen obstruction.
-/

noncomputable section

open Set Metric MeasureTheory NumberField RiemannMasullo
open scoped Classical BigOperators NumberField.AdeleRing
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL ψ) z
local notation "Z(" χ ")" => {p : ℝ × ℝ // p.1 ∈ Icc (-1 : ℝ) 1 ∧
  0 < order(χ 1, shift(1/2 + p.1, p.2))}
local notation "N(" χ ", " s ", " z ")" => spectralStripMultiplicity 1 s (z).val.1
  (order(χ 1, shift(1/2 + (z).val.1, (z).val.2))).untop₀.toNat
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "raw(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

local notation "point(" j ")" => shift((j).val.2.1,(j).val.2.2.1) + 1/2

/-- The project’s finite Gram formulation of (10.3.2.7) for all compact Bruhat tests
on the rational trivial component, with every finite ambient Gram block. -/
def RationalConvolutionFiniteGramBound {s : ℝ} (hs : 0 ≤ s) (χ : PontryaginDual C₁ → PontryaginDual Cℚ) : Prop :=
  let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
  let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1,z.val.1,z.val.2,m.val),m.isLt⟩
  ∀ φ : BruhatCompactSupport Cℚ, ∃ B : ℝ, ∀ (T : Finset (Z(χ))) (w : Z(χ) → ℂ) (S : Finset (J(χ,s))),
    (∀ z ∈ T, w z ∈ sphere (shift(z.val.1,z.val.2)) (2*Real.exp ((4+s)/2))) →
    ∑ z ∈ T, ‖nuclearityTestMellin (χ 1) φ (w z)‖ *
      ∑ m, ‖u (j z m)‖ * finiteGramCoordinate u (j z m) S ≤ B

private theorem gramCoordinate_nonneg {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ι → H) (i : ι) (S : Finset ι) : 0 ≤ finiteGramCoordinate u i S := by
  unfold finiteGramCoordinate
  split <;> positivity

/-- A singleton outer sum and one fixed point on each Mellin circle suffice
to recover polynomial growth of every coordinate, uniformly in the block. -/
theorem rational_convolution_requires_polynomial_gram {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (h : RationalConvolutionFiniteGramBound hs χ) :
    ∃ (K : ℝ) (p : ℕ), 0 < K ∧ ∀ i : J(χ,s), i.val.1 = 1 → ∀ S : Finset (J(χ,s)),
      let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (raw(χ,j))
      ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|i.val.2.2.1|)^p := by
  let u (i : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs i).toLp (raw(χ,i))
  let j (z : Z(χ)) (m : Fin (N(χ,s,z))) : J(χ,s) := ⟨(1,z.val.1,z.val.2,m.val),m.isLt⟩
  let P := {i : J(χ,s) // i.val.1 = 1} × Finset (J(χ,s))
  let R := 2*Real.exp ((4+s)/2)
  let b (a : P) := a.1.val.val.2.1 + R
  let t (a : P) := a.1.val.val.2.2.1
  let Q (a : P) := ‖u a.1.val‖ * finiteGramCoordinate u a.1.val a.2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ (a : P) : 0 ≤ Q a := mul_nonneg (norm_nonneg _) (gramCoordinate_nonneg ..)
  have hb (a : P) : |b a| ≤ 1+R := by
    have := (a.1.val.mem_strip_order_pos (by norm_num : (0:ℝ) ≤ 1)).1
    exact (abs_add_le ..).trans (add_le_add (abs_le.mpr this) (abs_of_nonneg hR).le)
  let w (z : Z(χ)) := shift(z.val.1+R,z.val.2)
  have hw (z : Z(χ)) : w z ∈ sphere (shift(z.val.1,z.val.2)) R := by
    rw [mem_sphere,dist_eq_norm]
    rw [show w z - shift(z.val.1,z.val.2) = (R:ℂ) by dsimp [w]; push_cast; ring]
    simp [abs_of_nonneg hR]
  have htest (φ : BruhatCompactSupport Cℚ) :
      BddAbove (range (fun a : P ↦ ‖nuclearityTestMellin (χ 1) φ (shift(b a,t a))‖ * Q a)) := by
    obtain ⟨B,hB⟩ := h φ
    refine ⟨B,?_⟩
    rintro _ ⟨a,rfl⟩
    let i := a.1.val
    have hi : i.val.1 = 1 := a.1.property
    let z : Z(χ) := ⟨(i.val.2.1,i.val.2.2.1),by
      simpa only [← hi] using i.mem_strip_order_pos (by norm_num : (0:ℝ) ≤ 1)⟩
    let k : Fin (N(χ,s,z)) := ⟨i.val.2.2.2,by
      change i.val.2.2.2 < spectralStripMultiplicity 1 s i.val.2.1
        (order(χ 1,shift(1/2+i.val.2.1,i.val.2.2.1))).untop₀.toNat
      rw [← hi]; exact i.property⟩
    have hj : j z k = i := by apply Subtype.ext; exact Prod.ext hi.symm rfl
    have hsum := hB {z} w a.2 (fun z _ ↦ hw z)
    simp only [Finset.sum_singleton] at hsum
    have hone := Finset.single_le_sum (s := Finset.univ)
      (f := fun n : Fin (N(χ,s,z)) ↦ ‖u (j z n)‖ * finiteGramCoordinate u (j z n) a.2)
      (fun _ _ ↦ mul_nonneg (norm_nonneg _) (gramCoordinate_nonneg ..)) (Finset.mem_univ k)
    rw [hj] at hone
    exact (mul_le_mul_of_nonneg_left hone (norm_nonneg _)).trans hsum
  obtain ⟨K,hK,p,hbound⟩ := LineModulation.homogeneous_strip_mellin_polynomial
    (show 0 ≤ 1+R by linarith) χ hχ 1 b t Q hb hQ (fun φ _ ↦ htest φ)
  refine ⟨K+1,p,by positivity,fun i hi S ↦ ?_⟩
  have hh := hbound (⟨⟨i,hi⟩,S⟩ : P)
  exact hh.trans (mul_le_mul (by linarith) (pow_le_pow_left₀ (by dsimp [t]; positivity)
    (by dsimp [t]; linarith) p) (by positivity) (by positivity))

/-- For the rational trivial character at positive width, the trivial-component Mellin-weighted
finite Gram assertion is equivalent to polynomial lower bounds on the first
nonzero ordinary zeta coefficient at every zero of absolute height at least one. -/
theorem rational_convolution_finiteGram_iff_coefficients {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) :
    RationalConvolutionFiniteGramBound hs χ ↔
      ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
        analyticOrderAt riemannZeta w = n → b / (2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  constructor
  · intro h
    exact (rational_polynomial_gram_iff_coefficients hs χ hχ hχ1).mp
      (rational_convolution_requires_polynomial_gram hs χ hχ h)
  · rintro ⟨A,b,hb,hcoeff⟩ φ
    exact rational_convolution_finiteGram_bound hb A hcoeff hs χ hχ hχ1 φ

private theorem criticalStrip_of_high_zeta_zero {w : ℂ} (ht : 1 ≤ |w.im|)
    (hz : riemannZeta w = 0) : w.re ∈ Ioo (0:ℝ) 1 := by
  refine ⟨lt_of_not_ge fun h ↦ ?_, lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
  obtain ⟨k,rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h).mp hz
  norm_num at ht

private theorem logCost_le_of_polynomial {x J C K q : ℝ} {p : ℕ}
    (hx : 0 ≤ x) (hC : 0 < C) (hK : 0 < K) (hscale : C*K*5^p ≤ x)
    (hJ : Real.exp J ≤ C*q) (hq : q ≤ K*(10+x)^p) :
    J ≤ (p+1:ℕ) * Real.log (2+x) := by
  let T := 2+x
  have hT : 0 < T := by dsimp [T]; linarith
  have hh : 10+x ≤ 5*T := by dsimp [T]; linarith
  have hs : C*K*5^p ≤ T := hscale.trans (by dsimp [T]; linarith)
  have hb : Real.exp J ≤ T^(p+1) := calc
    _ ≤ C * (K * (10+x)^p) := hJ.trans (mul_le_mul_of_nonneg_left hq hC.le)
    _ ≤ C * (K * (5*T)^p) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hh p) hK.le) hC.le
    _ = (C*K*5^p)*T^p := by rw [mul_pow]; ring
    _ ≤ T^(p+1) := by
      rw [pow_succ, mul_comm (T^p)]
      exact mul_le_mul_of_nonneg_right hs (pow_nonneg hT.le _)
  simpa only [Real.log_exp,Real.log_pow] using Real.log_le_log (Real.exp_pos _) hb

/-- It suffices to control zeroth rows in blocks whose other members are at
different points. Higher rows at a multiple center are never needed. -/
theorem rational_clusterCost_of_offcenter_blocks {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) {K : ℝ} (hK : 0 < K) (p : ℕ)
    (hrows : ∀ i : J(χ,s), i.val.1 = 1 → i.val.2.2.2 = 0 → 2 ≤ |(point(i)).im| →
      ∀ S : Finset (J(χ,s)), i ∈ S → (∀ j ∈ S, j ≠ i → point(j) ≠ point(i)) →
        let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (raw(χ,j))
        ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|i.val.2.2.1|)^p) :
    ∃ E H : ℝ, ∀ w : ℂ, H ≤ |w.im| → riemannZeta w = 0 →
      zetaClusterCost w (1/4) ≤ E * Real.log (2+|w.im|) := by
  obtain ⟨C,hC,hlower⟩ := rational_zeroth_gram_cluster_lower_supported hs
  refine ⟨(p+1:ℕ),max 2 (C*K*5^p),fun w ht hz ↦ ?_⟩
  have h2 : 2 ≤ |w.im| := (le_max_left ..).trans ht
  have hr := criticalStrip_of_high_zeta_zero (by linarith : 1 ≤ |w.im|) hz
  have hne : w ≠ 1 := by rintro rfl; norm_num at h2
  let n := analyticOrderNatAt riemannZeta w
  have hn : analyticOrderAt riemannZeta w = n := (Nat.cast_analyticOrderNatAt (zetaOrder_finite hne)).symm
  have hpos : 0 < n := by
    by_contra! hn0
    have := (analyticOn_riemannZeta w hne).analyticOrderAt_ne_zero.mpr hz
    simp [Nat.eq_zero_of_le_zero hn0] at hn
    exact this hn
  obtain ⟨z,hw,hm⟩ := rational_site_of_zero_order χ hχ1 s hr hpos hn
  let i : J(χ,s) := ⟨(1,z.val.1,z.val.2,0), hpos.trans_le hm.ge⟩
  have hi : shift(i.val.2.1,i.val.2.2.1) + 1/2 = w := hw
  obtain ⟨S,hiS,hsupp,hS⟩ := hlower χ hχ hχ1 i rfl rfl (by rwa [hi])
  let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (raw(χ,j))
  let Q := ‖u i‖ * finiteGramCoordinate u i S
  change Real.exp (zetaClusterCost (shift(i.val.2.1,i.val.2.2.1) + 1/2) (1/4)) ≤ C*Q at hS
  rw [hi] at hS
  have him : i.val.2.2.1 = w.im := by simpa using congrArg Complex.im hi
  have hQ := hrows i rfl rfl (by rwa [hi]) S hiS
    (fun j hj hji ↦ (mem_zetaNeighbors_iff.mp (hsupp j hj hji)).1)
  change Q ≤ K * (10+|i.val.2.2.1|)^p at hQ
  rw [him] at hQ
  exact logCost_le_of_polynomial (p := p) (q := Q) (abs_nonneg w.im) hC hK
    ((le_max_right 2 _).trans ht) hS hQ

/-- Equivalently, only the positions and multiplicities of the other zeros in
each quarter-disk are needed. The finite Gram bound holds precisely when their
multiplicity-weighted logarithmic distance cost is uniformly O(log height). -/
theorem rational_convolution_finiteGram_iff_clusterCost {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) :
    RationalConvolutionFiniteGramBound hs χ ↔
      ∃ E H : ℝ, ∀ w : ℂ, H ≤ |w.im| → riemannZeta w = 0 →
        zetaClusterCost w (1/4) ≤ E * Real.log (2+|w.im|) := by
  constructor
  · intro h
    obtain ⟨K,p,hK,hrows⟩ := rational_convolution_requires_polynomial_gram hs χ hχ h
    exact rational_clusterCost_of_offcenter_blocks hs χ hχ hχ1 hK p
      (fun i hi _ _ S _ _ ↦ hrows i hi S)
  · rintro ⟨E,H,hcost⟩
    apply (rational_convolution_finiteGram_iff_coefficients hs χ hχ hχ1).mpr
    obtain ⟨B,hmean⟩ := zetaCoeff_log_lower_of_clusterCost
    obtain ⟨A,hA⟩ := exists_nat_ge (B+E)
    refine ⟨A,extend_high_zetaCoeff_bound (H := max 1 H) A (fun w ht hz n hn ↦ ?_)⟩
    have h1 : 1 ≤ |w.im| := (le_max_left ..).trans ht
    have hr := criticalStrip_of_high_zeta_zero h1 hz
    have hh := hmean w ⟨hr.1.le,hr.2.le⟩ h1 n hn
    have hc := hcost w ((le_max_right ..).trans ht) hz
    have hne : w ≠ 1 := by rintro rfl; norm_num at h1
    have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta w hne)).mp hn).2
    have hp : 0 < ‖taylorCoeff riemannZeta w n‖ :=
      norm_pos_iff.mpr (div_ne_zero hd (by exact_mod_cast Nat.factorial_ne_zero n))
    have hT : 0 < 2+|w.im| := by positivity
    apply (Real.log_le_log_iff (div_pos zero_lt_one (pow_pos hT _)) hp).mp
    rw [Real.log_div one_ne_zero (pow_ne_zero _ hT.ne'),Real.log_one,Real.log_pow]
    have hL : 0 ≤ Real.log (2+|w.im|) := Real.log_nonneg (by linarith)
    linarith [mul_le_mul_of_nonneg_right hA hL]

/-- A polynomial row bound on blocks with only one jet at the selected
point forces the arithmetic criterion, with all center multiplicities allowed. -/
theorem rational_zeroth_gram_requires_coefficients_of_offcenter_blocks {s : ℝ} (hs : 0 ≤ s)
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) {K : ℝ} (hK : 0 < K) (p : ℕ)
    (hrows : ∀ i : J(χ,s), i.val.1 = 1 → i.val.2.2.2 = 0 → 2 ≤ |(point(i)).im| →
      ∀ S : Finset (J(χ,s)), i ∈ S → (∀ j ∈ S, j ≠ i → point(j) ≠ point(i)) →
        let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (raw(χ,j))
        ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|i.val.2.2.1|)^p) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b/(2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  exact (rational_convolution_finiteGram_iff_coefficients hs χ hχ hχ1).mp <|
    (rational_convolution_finiteGram_iff_clusterCost hs χ hχ hχ1).mpr <|
      rational_clusterCost_of_offcenter_blocks hs χ hχ hχ1 hK p hrows

end MasulloResearch.StripRadial
