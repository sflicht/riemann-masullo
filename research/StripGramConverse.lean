import research.StripInteriorMellin
import research.StripSimpleGram
import research.StripZetaClustering

/-!
# Finite Gram obstructions from nearby zeros

A finite inverse Gram column is a cardinal witness of exactly the indicated
norm. Jensen's formula counts the full multiplicities of the neighbouring
zeros at which such a witness vanishes.
-/

noncomputable section

open Set Metric MeasureTheory NumberField RiemannMasullo
open scoped Classical InnerProductSpace BigOperators NumberField.AdeleRing ComplexConjugate Topology
open MasulloResearch.StripJets

namespace MasulloResearch.StripRadial

/-- The inverse column represents the coefficient functional on its finite
block, with norm equal to the square root of the inverse Gram diagonal. -/
theorem exists_finiteGram_cardinal {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ι → H) (S : Finset ι) {i : ι} (hi : i ∈ S)
    (hind : LinearIndependent ℂ (fun j : S ↦ u j.val)) :
    ∃ q : H, ‖q‖ = finiteGramCoordinate u i S ∧
      ∀ j ∈ S, ⟪q, u j⟫_ℂ = if j = i then 1 else 0 := by
  let k : S := ⟨i,hi⟩
  let v (j : S) := u j.val
  let G := Matrix.gram ℂ v
  let a (j : S) := G⁻¹ j k
  let q := ∑ j, a j • v j
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hind)
  have hinner (j : S) : ⟪q, v j⟫_ℂ = if j = k then 1 else 0 := by
    have h := congrArg (fun M : Matrix S S ℂ ↦ M j k) (G.mul_nonsing_inv hdet)
    have hright : ⟪v j, q⟫_ℂ = (1 : Matrix S S ℂ) j k := by
      simpa only [q,a,inner_sum,inner_smul_right,Matrix.mul_apply,G,Matrix.gram_apply,mul_comm] using h
    rw [← inner_conj_symm q (v j), hright, Matrix.one_apply]
    split <;> simp
  have hdiag : ⟪q,q⟫_ℂ = G⁻¹ k k := by
    change ⟪q, ∑ j, a j • v j⟫_ℂ = _
    simp [inner_sum,inner_smul_right,hinner,mul_ite,a]
  have hnorm : (G⁻¹ k k).re = ‖q‖^2 := hdiag ▸ inner_self_eq_norm_sq (𝕜 := ℂ) q
  refine ⟨q, ?_, fun j hj ↦ ?_⟩
  · simp only [finiteGramCoordinate, hi, dite_eq_left]
    exact (show ‖q‖ = Real.sqrt (G⁻¹ k k).re by rw [hnorm,Real.sqrt_sq (norm_nonneg _)])
  · simpa [v,k,Subtype.ext_iff] using hinner (⟨j,hj⟩ : S)

/-- Every analytic cardinal function which kills the full jets at the other
quarter-disk zeros pays their multiplicity-weighted logarithmic cost. -/
theorem zetaClusterCost_le_log_of_cardinal {ρ : ℂ} {g : ℂ → ℂ} {M : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall ρ (1/4))) (hcenter : g ρ = 1)
    (hM : 1 ≤ M) (hbound : ∀ z ∈ sphere ρ (1/4), ‖g z‖ ≤ M)
    (hvanish : ∀ z ∈ zetaNeighbors ρ, ∀ k < analyticOrderNatAt riemannZeta z,
      iteratedDeriv k g z = 0) :
    zetaClusterCost ρ (1/4) ≤ Real.log M := by
  let R : ℝ := 1/4
  let B := closedBall ρ R
  let D := MeromorphicOn.divisor g B
  let term (z : ℂ) : ℝ := D z * Real.log (R * ‖ρ-z‖⁻¹)
  have hR : 0 < R := by norm_num [R]
  have hB : ρ ∈ B := mem_closedBall_self hR.le
  have hcenter' : g ρ ≠ 0 := hcenter ▸ one_ne_zero
  have hfinite (z : ℂ) (hz : z ∈ B) : analyticOrderAt g z ≠ ⊤ := by
    apply hg.analyticOrderAt_ne_top_of_isPreconnected (x := ρ)
      (convex_closedBall ρ R).isPreconnected hB hz
    simp [(hg ρ hB).analyticOrderAt_eq_zero.mpr hcenter']
  have hD (z : ℂ) (hz : z ∈ B) : D z = (analyticOrderNatAt g z : ℤ) := by
    change MeromorphicOn.divisor g B z = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hg hz,
      ← Nat.cast_analyticOrderNatAt (hfinite z hz), ENat.map_natCast]
    simp
  have hnonneg (z : ℂ) : 0 ≤ term z := by
    by_cases hz : z ∈ B
    · by_cases he : z = ρ
      · simp [term,he]
      have hd : 0 < dist ρ z := dist_pos.mpr (Ne.symm he)
      have hdR : dist ρ z ≤ R := (dist_comm ρ z).trans_le hz
      have hlog := Real.log_nonneg ((one_le_div hd).mpr hdR)
      simpa [term,hD z hz, ← dist_eq_norm, ← div_eq_mul_inv] using
        mul_nonneg (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt g z)) hlog
    · simp [term,D,Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  have hsupp : (Function.support term).Finite :=
    (D.finiteSupport (isCompact_closedBall ..)).subset fun z hz hzero ↦ hz (by simp [term,hzero])
  have hpart : zetaClusterCost ρ R ≤ ∑ z ∈ zetaNeighbors ρ, term z := by
    refine Finset.sum_le_sum fun z hz ↦ ?_
    obtain ⟨hne,hd,_⟩ := mem_zetaNeighbors_iff.mp hz
    have hlog : 0 ≤ Real.log (R / dist z ρ) := Real.log_nonneg ((one_le_div (dist_pos.mpr hne)).mpr hd)
    have hord := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg z hd)).mpr (hvanish z hz)
    rw [← Nat.cast_analyticOrderNatAt (hfinite z hd),Nat.cast_le] at hord
    simpa [term,hD z hd,← dist_eq_norm,dist_comm ρ z,← div_eq_mul_inv,max_eq_right hlog] using
      mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hord) hlog
  have hj := AnalyticOnNhd.circleAverage_log_norm (c := ρ) (R := R) (f := g)
    (by rw [abs_of_pos hR]; exact hg) hcenter'
  rw [abs_of_pos hR, hcenter, norm_one, Real.log_one, add_zero] at hj
  calc
    _ ≤ ∑ z ∈ zetaNeighbors ρ, term z := hpart
    _ ≤ ∑ᶠ z, term z := by
      rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset ∪ zetaNeighbors ρ) (by simp)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right ..) fun z _ _ ↦ hnonneg z
    _ = _ := hj.symm
    _ ≤ Real.log M := by
      apply Real.circleAverage_mono_on_of_le_circle
      · apply MeromorphicOn.circleIntegrable_log_norm
        rw [abs_of_pos hR]
        exact (hg.mono sphere_subset_closedBall).meromorphicOn
      · intro z hz
        rw [abs_of_pos hR] at hz
        by_cases he : g z = 0
        · simpa [he] using Real.log_nonneg hM
        exact Real.log_le_log (norm_pos_iff.mpr he) (hbound z hz)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "site(" j ")" => (((j).val.2.1 : ℝ) : ℂ) + ((j).val.2.2.1 : ℂ) * Complex.I
local notation "point(" j ")" => site(j) + 1/2
local notation "jet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "J(" χ ", " s ")" => SpectralStripJetIndex χ (1/2) 1 s
local notation "ℓ" => logIdeleClassNorm ℚ
local notation "ν(" s ")" => intervalSobolevMeasure (ideleClassTamagawaMeasure ℚ) ℓ (-1) 1 s true

/-- A finite block containing the center and all jets of every other ordinary
zero in the closed quarter-disk. Interior sites retain their full order. -/
theorem exists_rational_neighbor_block {χ : PontryaginDual C₁ → PontryaginDual Cℚ}
    (hχ1 : χ 1 = 1) {s : ℝ} (i : J(χ,s)) (ht : 2 ≤ |(point(i)).im|) :
    ∃ S : Finset (J(χ,s)), i ∈ S ∧ ∀ z ∈ zetaNeighbors (point(i)), ∀ k < analyticOrderNatAt riemannZeta z,
      ∃ j ∈ S, j.val.1 = 1 ∧ point(j) = z ∧ j.val.2.2.2 = k := by
  let Z := zetaNeighbors (point(i))
  have hj (z : Z) (k : Fin (analyticOrderNatAt riemannZeta z.val)) :
      ∃ j : J(χ,s), j.val.1 = 1 ∧ point(j) = z.val ∧ j.val.2.2.2 = k.val := by
    obtain ⟨_,hd,hz⟩ := mem_zetaNeighbors_iff.mp z.property
    have him : z.val.im ≠ 0 := by
      intro he
      have h := (Complex.abs_im_le_norm (z.val-point(i))).trans (mem_closedBall_iff_norm.mp hd)
      rw [Complex.sub_im,he,zero_sub,abs_neg] at h
      linarith
    have hr : z.val.re ∈ Ioo (0:ℝ) 1 := by
      refine ⟨lt_of_not_ge fun h ↦ ?_,lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
      obtain ⟨n,hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h).mp hz
      exact him (by simp [hn])
    have hne : analyticOrderAt riemannZeta z.val ≠ ⊤ := by
      intro h
      have := k.isLt
      simp [analyticOrderNatAt,h] at this
    obtain ⟨p,hpoint,hm⟩ := rational_site_of_zero_order χ hχ1 s hr
      (Nat.zero_le _ |>.trans_lt k.isLt) (Nat.cast_analyticOrderNatAt hne).symm
    exact ⟨⟨(1,p.val.1,p.val.2,k.val),by
      change k.val < _
      exact k.isLt.trans_le hm.ge⟩, rfl,hpoint,rfl⟩
  let j (z : Z) (k : Fin (analyticOrderNatAt riemannZeta z.val)) := (hj z k).choose
  let S := insert i (Z.attach.biUnion fun z ↦ Finset.univ.image (j z))
  refine ⟨S,Finset.mem_insert_self ..,fun z hz k hk ↦ ?_⟩
  let zz : Z := ⟨z,hz⟩
  let kk : Fin (analyticOrderNatAt riemannZeta zz.val) := ⟨k,hk⟩
  exact ⟨j zz kk,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
    ⟨zz,Finset.mem_attach ..,Finset.mem_image.mpr ⟨kk,Finset.mem_univ _,rfl⟩⟩),(hj zz kk).choose_spec⟩

private theorem expJet_at_rational_index {s : ℝ} (hs : 0 ≤ s)
    {χ : PontryaginDual C₁ → PontryaginDual Cℚ} (hχ1 : χ 1 = 1)
    (j : J(χ,s)) (hj : j.val.1 = 1) (b : |(site(j)).re| < 1) :
    (interior_expJet_memLp (F := ℚ) hs (site(j)) b j.val.2.2.2).toLp _ =
      (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j)) := by
  apply Lp.ext
  apply (interior_expJet_memLp (F := ℚ) hs _ b _).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).coeFn_toLp.symm
  rw [hj,hχ1,trivial_spectralZeroJet_eq_expJet]

private theorem exists_finite_rational_mellin {s : ℝ} (hs : 0 ≤ s)
    {χ : PontryaginDual C₁ → PontryaginDual Cℚ} (hχ1 : χ 1 = 1)
    (i : J(χ,s)) (hi : i.val.1 = 1)
    (q : Lp ℂ 2 ν(s)) {D : ℝ}
    (hupper : ∀ (w : ℂ) (hw : |w.re| ≤ 3/4),
      ‖(interior_expJet_memLp (F := ℚ) hs w (hw.trans_lt (by norm_num)) 0).toLp _‖ ≤ D) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall (point(i)) (1/4)) ∧
      (∀ z ∈ closedBall (point(i)) (1/4), ‖g z‖ ≤ D * ‖q‖) ∧
      ∀ (j : J(χ,s)), j.val.1 = 1 → point(j) ∈ closedBall (point(i)) (1/4) →
        iteratedDeriv j.val.2.2.2 g (point(j)) =
          ⟪q,(spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))⟫_ℂ := by
  have hx : Measurable ℓ := Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm ℚ).continuous)).measurable
  obtain ⟨g,han,hb,hd⟩ := exists_translated_mellin_cardinal_data ℓ hx
    (interior_expJet_memLp (F := ℚ) hs) q hupper (point(i)) (rational_strip_jet_order hχ1 i hi).1
  refine ⟨g,han,hb,fun j hj _ ↦ ?_⟩
  have hstrip := (rational_strip_jet_order hχ1 j hj).1
  have hv : |(site(j)).re| < 1 := by
    simp [abs_lt] at hstrip ⊢; constructor <;> linarith [hstrip.1,hstrip.2]
  exact (hd _ hv _).trans (congrArg (fun v ↦ ⟪q,v⟫_ℂ) (expJet_at_rational_index hs hχ1 j hj hv))

private theorem finite_rational_cardinal_cost {s : ℝ} (hs : 0 ≤ s)
    {χ : PontryaginDual C₁ → PontryaginDual Cℚ} (hχ1 : χ 1 = 1)
    (i : J(χ,s)) (hi : i.val.1 = 1) (hk : i.val.2.2.2 = 0)
    (S : Finset (J(χ,s))) (hiS : i ∈ S)
    (hother : ∀ z ∈ zetaNeighbors (point(i)), ∀ k < analyticOrderNatAt riemannZeta z,
      ∃ j ∈ S, j.val.1 = 1 ∧ point(j) = z ∧ j.val.2.2.2 = k)
    (q : Lp ℂ 2 ν(s)) {D : ℝ}
    (hupper : ∀ (w : ℂ) (hw : |w.re| ≤ 3/4),
      ‖(interior_expJet_memLp (F := ℚ) hs w (hw.trans_lt (by norm_num)) 0).toLp _‖ ≤ D)
    (hcard : ∀ j ∈ S, ⟪q,(spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))⟫_ℂ =
      if j = i then 1 else 0) :
    Real.exp (zetaClusterCost (point(i)) (1/4)) ≤ D * ‖q‖ := by
  let ρ := point(i)
  have hρB : ρ ∈ closedBall ρ (1/4) := mem_closedBall_self (by norm_num)
  obtain ⟨g,han,hbound,hjs⟩ := exists_finite_rational_mellin hs hχ1 i hi q hupper
  have hcenter : g ρ = 1 := by
    have h := (hjs i hi hρB).trans (hcard i hiS)
    simpa only [hk,iteratedDeriv_zero,ite_true,eq_self] using h
  have hJ := zetaClusterCost_le_log_of_cardinal (g := g) (ρ := ρ) han
    hcenter (by simpa [hcenter] using hbound ρ hρB)
    (fun z hz ↦ hbound z (sphere_subset_closedBall hz)) (fun z hz k hk' ↦ by
      obtain ⟨j,hjS,hj,hz',hk''⟩ := hother z hz k hk'
      have hne : j ≠ i := fun e ↦ (mem_zetaNeighbors_iff.mp hz).1 (hz'.symm.trans (congrArg (fun j : J(χ,s) ↦ point(j)) e))
      have hjb : point(j) ∈ closedBall ρ (1/4) := by rw [hz']; exact (mem_zetaNeighbors_iff.mp hz).2.1
      have hD := (hjs j hj hjb).trans ((hcard j hjS).trans (ite_eq_right hne))
      simpa only [hk'',hz'] using hD)
  have hcoord : 1 ≤ D * ‖q‖ := by simpa [hcenter] using hbound ρ hρB
  exact (Real.exp_le_exp.mpr hJ).trans_eq (Real.exp_log (zero_lt_one.trans_le hcoord))

/-- On the rational trivial character, the logarithmic neighbour cost of any
high zero is bounded by a single actual finite Gram coordinate of its zeroth
jet. The constant is uniform in height, the center, and the basepoint choice. -/
theorem rational_zeroth_gram_cluster_lower {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ),
      IsSpectralBasepointChoice χ → χ 1 = 1 → ∀ i : J(χ,s),
      i.val.1 = 1 → i.val.2.2.2 = 0 → 2 ≤ |(point(i)).im| →
      ∃ S : Finset (J(χ,s)), i ∈ S ∧
        let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
        Real.exp (zetaClusterCost (point(i)) (1/4)) ≤
          C * (‖u i‖ * finiteGramCoordinate u i S) := by
  let hLp := interior_expJet_memLp (F := ℚ) hs
  have hx : Measurable ℓ := Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm ℚ).continuous)).measurable
  obtain ⟨D,hD,hupper⟩ := expJet_uniform_norm ℓ hLp
  obtain ⟨d,hd,hlower⟩ := expJet_uniform_lower ℓ hx (reciprocal_strip_measure_ne_zero (F := ℚ) s) hLp
  refine ⟨D/d,div_pos hD hd,fun χ hχ hχ1 i hi hk ht ↦ ?_⟩
  let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
  obtain ⟨S,hiS,hother⟩ := exists_rational_neighbor_block hχ1 i ht
  have hInd := spectralStripJet_toLp_linearIndependent χ hχ (1/2) (by norm_num : (0:ℝ) ≤ 1) hs
  obtain ⟨q,hq,hcard⟩ := exists_finiteGram_cardinal u S hiS (hInd.comp _ Subtype.val_injective)
  have he := finite_rational_cardinal_cost hs hχ1 i hi hk S hiS hother q hupper (fun j hj ↦ by
    by_cases e : j = i
    · simpa only [ite_eq_left e] using hcard j hj
    · simpa only [ite_eq_right e] using hcard j hj)
  have hu : d ≤ ‖u i‖ := by
    have hstrip := (rational_strip_jet_order hχ1 i hi).1
    have hb : |(site(i)).re| < 1 := by
      simp [abs_lt] at hstrip ⊢; constructor <;> linarith [hstrip.1,hstrip.2]
    have hij := expJet_at_rational_index hs hχ1 i hi hb
    change (hLp _ hb i.val.2.2.2).toLp _ = u i at hij
    exact (hlower _ hb).trans_eq ((congrArg (fun n ↦ ‖(hLp _ hb n).toLp _‖) hk.symm).trans
      (congrArg norm hij))
  refine ⟨S,hiS,?_⟩
  change Real.exp _ ≤ D/d * (‖u i‖ * finiteGramCoordinate u i S)
  rw [← hq]
  calc _ ≤ D * ‖q‖ := he
       _ = D/d * (d * ‖q‖) := by field_simp
       _ ≤ _ := by gcongr

/-- The exact central order in Jensen's formula contributes a factor of
four to the power of the multiplicity on the quarter-circle. -/
theorem zeta_leadingCoefficient_cluster_identity {ρ : ℂ} (ht : 1 ≤ |ρ.im|)
    {m : ℕ} (hm : analyticOrderAt riemannZeta ρ = m) :
    (4:ℝ)^m * Real.exp (Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) ρ (1/4)) =
      Real.exp (zetaClusterCost ρ (1/4)) * ‖taylorCoeff riemannZeta ρ m‖ := by
  have hne : ρ ≠ 1 := by rintro rfl; norm_num at ht
  have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticOn_riemannZeta ρ hne)).mp hm).2
  have ha : 0 < ‖taylorCoeff riemannZeta ρ m‖ :=
    norm_pos_iff.mpr (div_ne_zero hd (by exact_mod_cast Nat.factorial_ne_zero m))
  rw [zeta_circleAverage_eq_cluster_add_coeff ht hm, Real.exp_add,Real.exp_add,
    Real.exp_log ha,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 1/4)]
  rw [show (1/4 : ℝ) = (4:ℝ)⁻¹ by norm_num, inv_pow]
  field_simp

/-- The quarter-circle mean estimate implies a converse Gram estimate at
every high center, including repeated zeros. Only the zeroth jet is needed.
For simple centers the Taylor coefficient here is the ordinary derivative. -/
theorem rational_zeroth_gram_coefficient_lower {s B : ℝ} (hs : 0 ≤ s)
    (hmean : ∀ w : ℂ, w.re ∈ Icc (0:ℝ) 1 → 1 ≤ |w.im| → -(B * Real.log (2+|w.im|)) ≤
      Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ),
      IsSpectralBasepointChoice χ → χ 1 = 1 → ∀ (i : J(χ,s)) (m : ℕ),
      i.val.1 = 1 → i.val.2.2.2 = 0 → 2 ≤ |(point(i)).im| →
      analyticOrderAt riemannZeta (point(i)) = m → ∃ S : Finset (J(χ,s)), i ∈ S ∧
        let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
        (4:ℝ)^m * (2+|(point(i)).im|)^(-B) ≤
          C * (‖u i‖ * finiteGramCoordinate u i S) * ‖taylorCoeff riemannZeta (point(i)) m‖ := by
  obtain ⟨C,hC,hgram⟩ := rational_zeroth_gram_cluster_lower hs
  refine ⟨C,hC,fun χ hχ hχ1 i m hi hk ht hm ↦ ?_⟩
  obtain ⟨S,hiS,hS⟩ := hgram χ hχ hχ1 i hi hk ht
  refine ⟨S,hiS,?_⟩
  let ρ := point(i)
  have hstrip := (rational_strip_jet_order hχ1 i hi).1
  have h1 : 1 ≤ |ρ.im| := by change 1 ≤ |(point(i)).im|; linarith
  have hM := Real.exp_le_exp.mpr (hmean ρ ⟨hstrip.1.le,hstrip.2.le⟩ h1)
  have hT : 0 < 2+|ρ.im| := by positivity
  rw [show -(B*Real.log (2+|ρ.im|)) = Real.log (2+|ρ.im|)*(-B) by ring,
    ← Real.rpow_def_of_pos hT] at hM
  exact ((mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ (4:ℝ)^m)).trans_eq
    (zeta_leadingCoefficient_cluster_identity h1 hm)).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg _))

/-- For a simple zero, a specific finite Gram block witnesses the reciprocal
derivative obstruction. The fourth-power upper bound holds on every block. -/
theorem rational_simple_gram_two_sided {s B : ℝ} (hs : 0 ≤ s)
    (hmean : ∀ w : ℂ, w.re ∈ Icc (0:ℝ) 1 → 1 ≤ |w.im| → -(B * Real.log (2+|w.im|)) ≤
      Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4)) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual Cℚ),
      IsSpectralBasepointChoice χ → χ 1 = 1 → ∀ i : J(χ,s),
      i.val.1 = 1 → 2 ≤ |i.val.2.2.1| → analyticOrderAt riemannZeta (point(i)) = 1 →
      let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
      let Q (S : Finset (J(χ,s))) := ‖u i‖ * finiteGramCoordinate u i S
      (∃ S : Finset (J(χ,s)), i ∈ S ∧ c*(2+|i.val.2.2.1|)^(-B) ≤ Q S * ‖deriv riemannZeta (point(i))‖) ∧
        ∀ S, Q S ≤ C*(10+|i.val.2.2.1|)^4 / ‖deriv riemannZeta (point(i))‖ := by
  obtain ⟨K,hK,hlo⟩ := rational_zeroth_gram_coefficient_lower hs hmean
  obtain ⟨C,hC,hhi⟩ := rational_simple_gram_coordinate hs
  refine ⟨4/K,C,by positivity,hC,fun χ hχ hχ1 i hi ht hm ↦ ?_⟩
  intro u Q
  obtain ⟨_,_,m,ho,hk⟩ := rational_strip_jet_order hχ1 i hi
  have hm' : m = 1 := by exact_mod_cast ho.symm.trans hm
  have hk' : i.val.2.2.2 = 0 := by omega
  have him : (point(i)).im = i.val.2.2.1 := by simp
  obtain ⟨S,hiS,hS⟩ := hlo χ hχ hχ1 i 1 hi hk' (by rwa [him]) hm
  refine ⟨⟨S,hiS,?_⟩, hhi χ hχ hχ1 i hi ht hm⟩
  change (4:ℝ)^1 * (2+|(point(i)).im|)^(-B) ≤ K * Q S * ‖taylorCoeff riemannZeta (point(i)) 1‖ at hS
  rw [him,pow_one] at hS
  have hc : taylorCoeff riemannZeta (point(i)) 1 = deriv riemannZeta (point(i)) := by simp [taylorCoeff]
  rw [hc] at hS
  calc (4/K) * (2+|i.val.2.2.1|)^(-B) = (4*(2+|i.val.2.2.1|)^(-B))/K := by ring
       _ ≤ _ := (div_le_iff₀ hK).mpr (hS.trans_eq (by ring))

/-- Polynomial bounds on the zeroth Gram rows alone force one polynomial
lower bound for the first nonzero coefficient at every high ordinary zero.
The classical quarter-circle mean is the sole external analytic input. -/
theorem rational_zeroth_gram_requires_coefficients {s B : ℝ} (hs : 0 ≤ s)
    (hmean : ∀ w : ℂ, w.re ∈ Icc (0:ℝ) 1 → 1 ≤ |w.im| → -(B * Real.log (2+|w.im|)) ≤
      Real.circleAverage (fun z ↦ Real.log ‖riemannZeta z‖) w (1/4))
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : IsSpectralBasepointChoice χ)
    (hχ1 : χ 1 = 1) {K : ℝ} (hK : 0 < K) (p : ℕ)
    (hrows : ∀ i : J(χ,s), i.val.1 = 1 → i.val.2.2.2 = 0 → 2 ≤ |(point(i)).im| →
      ∀ S : Finset (J(χ,s)),
        let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
        ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|(point(i)).im|)^p) :
    ∃ (A : ℕ) (b : ℝ), 0 < b ∧ ∀ w : ℂ, 1 ≤ |w.im| → riemannZeta w = 0 → ∀ n : ℕ,
      analyticOrderAt riemannZeta w = n → b / (2+|w.im|)^A ≤ ‖taylorCoeff riemannZeta w n‖ := by
  obtain ⟨C,hC,hlo⟩ := rational_zeroth_gram_coefficient_lower hs hmean
  obtain ⟨N,hN⟩ := exists_nat_ge B
  let H := max 2 (C*K*5^p)
  refine ⟨N+(p+1),extend_high_zetaCoeff_bound (H := H) _ ?_⟩
  intro w ht hz n hn
  have h2 : 2 ≤ |w.im| := (le_max_left ..).trans ht
  have hr : w.re ∈ Ioo (0:ℝ) 1 := by
    refine ⟨lt_of_not_ge fun h ↦ ?_,lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
    obtain ⟨k,rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h).mp hz
    norm_num at h2
  have hne : w ≠ 1 := fun he ↦ hr.2.ne ((congrArg Complex.re he).trans Complex.one_re)
  have hnpos : 0 < n := by
    by_contra! he
    have hzero := (analyticOn_riemannZeta w hne).analyticOrderAt_ne_zero.mpr hz
    simp [Nat.eq_zero_of_le_zero he] at hn
    exact hzero hn
  obtain ⟨v,hv,hm⟩ := rational_site_of_zero_order χ hχ1 s hr hnpos hn
  let i : J(χ,s) := ⟨(1,v.val.1,v.val.2,0), hnpos.trans_le hm.ge⟩
  have hi : point(i) = w := hv
  obtain ⟨S,_,hS⟩ := hlo χ hχ hχ1 i n rfl rfl (by rwa [hi]) (by rwa [hi])
  let T := 2+|w.im|
  let coeff := ‖taylorCoeff riemannZeta w n‖
  have hT : 1 ≤ T := by dsimp [T]; linarith
  have hTp := zero_lt_one.trans_le hT
  let u (j : J(χ,s)) := (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 1) hs j).toLp (jet(χ,j))
  change (4:ℝ)^n * (2+|(point(i)).im|)^(-B) ≤
    C * (‖u i‖ * finiteGramCoordinate u i S) * ‖taylorCoeff riemannZeta (point(i)) n‖ at hS
  rw [hi] at hS
  have hU := hrows i rfl rfl (by rwa [hi]) S
  change ‖u i‖ * finiteGramCoordinate u i S ≤ K * (10+|(point(i)).im|)^p at hU
  rw [hi] at hU
  have hheight : 10+|w.im| ≤ 5*T := by dsimp [T]; linarith
  have hscale : C*K*5^p ≤ T := (le_max_right ..).trans (ht.trans (by dsimp [T]; linarith))
  have hQ : C*(‖u i‖ * finiteGramCoordinate u i S) ≤ T^(p+1) := by
    calc _ ≤ C*(K*((5*T)^p)) := mul_le_mul_of_nonneg_left
           (hU.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hheight p) hK.le)) hC.le
         _ = (C*K*5^p)*T^p := by rw [mul_pow]; ring
         _ ≤ T*T^p := mul_le_mul_of_nonneg_right hscale (pow_nonneg hTp.le _)
         _ = _ := by ring
  have hL : 1/T^N ≤ T^(-B) := by
    calc _ = T^(-(N:ℝ)) := by rw [Real.rpow_neg hTp.le, Real.rpow_natCast,one_div]
         _ ≤ T^(-B) := Real.rpow_le_rpow_of_exponent_le hT (neg_le_neg hN)
  have hx : 1/T^N ≤ T^(p+1)*coeff := hL.trans <|
    (le_mul_of_one_le_left (Real.rpow_nonneg hTp.le _) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4))).trans <|
      hS.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
  change 1/T^(N+(p+1)) ≤ coeff
  rw [pow_add,← div_div]
  exact (div_le_iff₀ (pow_pos hTp _)).mpr (hx.trans_eq (mul_comm ..))

end MasulloResearch.StripRadial
