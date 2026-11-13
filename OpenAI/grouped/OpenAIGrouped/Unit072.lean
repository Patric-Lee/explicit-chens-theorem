import OpenAIGrouped.Unit070
import OpenAIGrouped.Unit071
import OpenAIGrouped.Unit037
import OpenAIGrouped.Unit010
import OpenAIGrouped.Unit058
import OpenAIGrouped.Unit045
import OpenAIGrouped.Unit032
import OpenAIGrouped.Unit044

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedPadding.lean; sha256: 263e66031cf16795aa88727b83bd550b41421a0f70109d75b317896b8c604cba -/
section Source2880
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedPadding
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots
open InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy
open HeckeDetectorPhysicalSelection ConcreteTraceCRT CanonicalQuadraticSieve ActualEisensteinCubic
local notation "O" => HeckeFamily.O

def radialMajorant : 𝓢(ℝ,ℂ) :=
  Classical.choose DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant

theorem radialMajorant_compact : HasCompactSupport (radialMajorant : ℝ→ℂ) :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).1

theorem radialMajorant_nonneg (x : ℝ) : 0≤(radialMajorant x).re :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.1 x

theorem radialMajorant_one (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) : radialMajorant x=1 :=
  (Classical.choose_spec DetectorDictionaryInverseRawRadial.exists_raw_radial_majorant).2.2 x hx

theorem compact_radial_summable (Φ : 𝓢(ℝ,ℂ))
    (hΦ : HasCompactSupport (Φ : ℝ→ℂ)) (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight Φ Y u*‖f u‖^2) := by
  obtain ⟨B,hB⟩ := hΦ.isBounded.exists_norm_le
  let R := ShortDraftLatticeCount.rowNormBall ⌈B*Y⌉₊
  apply (hasSum_sum_of_ne_finset_zero (s:=R) ?_).summable
  intro u hu
  have hz : Φ (‖eisEmbedding u‖^2/Y)=0 := by
    by_contra hn
    have hb := hB _ (subset_tsupport Φ hn)
    have hnB : (Ideal.absNorm (Ideal.span {u}):ℝ)≤B*Y := by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)] at hb
      rw [eisEmbedding_norm_sq_eq_absNorm_span] at hb
      exact (div_le_iff₀ hY).mp hb
    apply hu
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast hnB.trans (Nat.le_ceil (B*Y))
  simp [radialWeight,hz]

theorem radialMajorant_summable (Y : ℝ) (hY : 0<Y) (f : O→ℂ) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*‖f u‖^2) :=
  compact_radial_summable radialMajorant radialMajorant_compact Y hY f

theorem finite_source_le_smoothed {Row : Type*} (rows : Finset Row)
    (row : Row→O) (hinj : Function.Injective row) (f : O→ℂ)
    (Y : ℝ) (hY : 0<Y)
    (hrows : ∀u∈rows,((Ideal.span {row u}).absNorm:ℝ)≤Y) :
    (∑u∈rows,‖f (row u)‖^2)≤smoothedEnergy radialMajorant Y f := by
  have he (u : Row) (hu : u∈rows) :
      ‖f (row u)‖^2=radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 := by
    have hn : ‖eisEmbedding (row u)‖^2/Y∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hY.le,?_⟩
      apply (div_le_one hY).mpr
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    simp [radialWeight,radialMajorant_one _ hn]
  calc
    _=∑u∈rows,radialWeight radialMajorant Y (row u)*‖f (row u)‖^2 :=
      Finset.sum_congr rfl he
    _=∑u∈rows.image row,radialWeight radialMajorant Y u*‖f u‖^2 := by
      rw [Finset.sum_image (fun a _ b _ hab=>hinj hab)]
    _≤∑'u : O,radialWeight radialMajorant Y u*‖f u‖^2 :=
      (radialMajorant_summable Y hY f).sum_le_tsum _
        (fun u _=>mul_nonneg (radialMajorant_nonneg _) (sq_nonneg _))
    _=smoothedEnergy radialMajorant Y f := rfl

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def selectedSource (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (u : O) : ℂ :=
  ∑p∈Fintype.piFinset (fun s:selected=>
      livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
    (star (∏s:selected,primeProfile (F.profile s) (U^(F.widths s)) (F.external s) (p s))/
      fixedBase F.rowData.η F.rowData.m F.rowData.f (∏s:selected,p s))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u

omit [NeZero M] in
theorem selectedSource_norm (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (u : FreeRow) (hu : u∈F.rows) :
    ‖polynomial (F.family u F.label) true W (U^F.r) σ t*F.physicalProduct selected u‖=
      ‖selectedSource F selected W σ t bW u.val‖ :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_norm_initial
    F selected W σ t bW lower hU hW hV hlarge u hu

omit [NeZero M] in
theorem selectedSource_summable
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW Y : ℝ) (hY : 0<Y) :
    Summable (fun u : O=>radialWeight radialMajorant Y u*
      ‖selectedSource F selected W σ t bW u‖^2) :=
  radialMajorant_summable Y hY _

omit [NeZero M] in
theorem selectedSource_energy
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW : ℝ) (lower : Slot→ℝ)
    (hU : 0<U) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 :=
  DetectorDictionaryInverseRawFiberSource.fiber_physical_energy_initial
    F selected W σ t bW lower hU hW hV hlarge

omit [NeZero M] in
theorem fiber_physical_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (W : ℝ→ℂ) (σ t bW ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ) (hW : ∀x,W x≠0 → x≤bW)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ)) (selectedSource F selected W σ t bW) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpad : U≤U^(1+ρ) := by
    calc
      U=U^(1:ℝ) := (Real.rpow_one U).symm
      _≤U^(1+ρ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  calc
    _=∑u∈F.rows,‖selectedSource F selected W σ t bW u.val‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [selectedSource_norm F selected W σ t bW lower hU0 hW hV hlarge u hu]
    _≤_ := finite_source_le_smoothed F.rows (fun u : FreeRow=>u.val)
      Subtype.val_injective _ _ (Real.rpow_pos_of_pos hU0 _)
      (fun u hu=>(F.row_norm u hu).trans hpad)

omit [NeZero M] in
theorem fiber_inverse_le_padded_smoothed
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (n : ℕ) (σ t ρ : ℝ) (lower : Slot→ℝ)
    (hU : 1≤U) (hρ : 0≤ρ)
    (hV : ∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (lower s) (F.upper s))
    (hlarge : ∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) (U^F.r) σ t*
      F.physicalProduct selected u‖^2)≤
      smoothedEnergy radialMajorant (U^(1+ρ))
        (selectedSource F selected ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          F.inverseProfile) σ t (9/4)) :=
  fiber_physical_le_padded_smoothed F selected _ σ t (9/4) ρ lower hU hρ
    (DetectorDictionaryInverseRawFiberSource.fiber_inverse_log_upper F n) hV hlarge

theorem fixed_padding_margins (r z ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : r+2*z<1) (hsecond : 2*r+8*z<3) :
    r+2*z≤(1+ρ)-ρ ∧ 2*r+8*z≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) r z ρ := by
  unfold InverseMoment.MarkedMargins
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

omit [NeZero M] in
theorem fiber_padding_margins
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (ρ : ℝ) (hρ : 0≤ρ)
    (hfirst : F.r+2*(∑s∈selected,F.widths s)<1)
    (hsecond : 2*F.r+8*(∑s∈selected,F.widths s)<3) :
    F.r+2*(∑s∈selected,F.widths s)≤(1+ρ)-ρ ∧
      2*F.r+8*(∑s∈selected,F.widths s)≤3*(1+ρ)-3*ρ ∧
      InverseMoment.MarkedMargins (1+ρ) F.r (∑s∈selected,F.widths s) ρ :=
  fixed_padding_margins _ _ ρ hρ hfirst hsecond

theorem padded_output_budget (U C ρ loss εm : ℝ) (hU : 1≤U) (hC : 0≤C)
    (hbudget : ρ+loss≤εm) : C*U^(1+ρ+loss)≤C*U^(1+εm) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)

end SevenEighths.DetectorDictionaryInverseMarkedPadding

end

end OAI

end Source2880

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceCoefficients.lean; sha256: 2a925836c10d1f75e3061f586e03487fec3a56d2b3671ed6b906736075060a50 -/
section Source2881
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding
local notation "O"=>HeckeFamily.O

def slotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) : ℂ :=
  star (primeProfile V Y ζ P)/fixedBase data.η data.m data.f P

theorem slotCoefficient_character (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(P:Ideal O) :
    slotCoefficient data V Y ζ P=
      idealCoeff (baseCharacter data).inverse P*star (primeProfile V Y ζ P) := by
  rw [slotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,baseCharacter_coeff,
    div_eq_mul_inv,mul_comm]

theorem tuple_coefficient {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      ∏i,slotCoefficient data (V i) (Y i) (ζ i) (P i) := by
  simp only [slotCoefficient,star_prod,map_prod,Finset.prod_div_distrib]

def normalizedSlotCoefficient (data:RowData)(V:ℝ→ℂ)(Y:ℝ)(ζ:ℂ)(C:ℝ)(P:Ideal O) : ℂ :=
  slotCoefficient data V Y ζ P/(C:ℂ)

theorem tuple_coefficient_normalized {ι:Type*}[Fintype ι](data:RowData)
    (V:ι→ℝ→ℂ)(Y:ι→ℝ)(ζ:ι→ℂ)(C:ι→ℝ)(hC:∀i,C i≠0)(P:ι→Ideal O) :
    star (∏i,primeProfile (V i) (Y i) (ζ i) (P i))/
      fixedBase data.η data.m data.f (∏i,P i)=
      (∏i,(C i:ℂ))*∏i,normalizedSlotCoefficient data (V i) (Y i) (ζ i) (C i) (P i) := by
  rw [tuple_coefficient,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedSlotCoefficient]
  field_simp [hC i]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem selectedSource_normalized (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(C:Slot→ℝ)(hC:∀s∈selected,C s≠0)(u:O) :
    selectedSource F selected W σ t bW u=
      (∏s∈selected,(C s:ℂ))*
      ∑p∈Fintype.piFinset (fun s:selected=>livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))),
        (∏s:selected,normalizedSlotCoefficient F.rowData (F.profile s) (U^(F.widths s))
          (F.external s) (C s) (p s))*
        InverseInitialConjugateEnergy.originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,p s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (HeckeDetectorCoefficientTransfer.orientedProfile F.reverse W) σ
            (HeckeDetectorCoefficientTransfer.orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  unfold selectedSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tuple_coefficient_normalized F.rowData (fun s:selected=>F.profile s)
    (fun s:selected=>U^(F.widths s)) (fun s:selected=>F.external s)
    (fun s:selected=>C s) (fun s=>hC s s.property) p]
  rw [Finset.prod_coe_sort selected (fun s=>(C s:ℂ))]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2881

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceDivisors.lean; sha256: 68f5bfbeafb5e46f58d50a239e983b3808cf71b780917eac0e2047ad97e8bda4 -/
section Source2882
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
open InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem tuple_product_squarefree (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Squarefree (∏i,P i) := by
  have hs:∀Q∈Finset.univ.image P,Prime Q := by
    intro Q hQ
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hQ
    exact hP i
  have he:(∏Q∈Finset.univ.image P,Q)=∏i,P i :=
    Finset.prod_image (fun i hi j hj h=>hinj h)
  rw [←he]
  exact InverseInitialExcludedPolynomial.prime_product_squarefree _ hs

omit [DecidableEq ι] in
theorem tuple_product_support (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (_hinj:Function.Injective P) : primeSupport (∏i,P i)=Finset.univ.image P := by
  have hn:(∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>(hP i).ne_zero)
  ext Q
  rw [primeSupport,Multiset.mem_toFinset,mem_normalizedFactors_iff hn,Finset.mem_image]
  constructor
  · rintro ⟨hQ,hd⟩
    obtain ⟨i,hi,hd⟩:=(hQ.dvd_finsetProd_iff P).mp hd
    have he:Q=P i:=associated_iff_eq.mp (hQ.associated_of_dvd (hP i) hd)
    exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hP i,Finset.dvd_prod_of_mem P hi⟩

omit [DecidableEq ι] in
theorem tuple_divisors_eq_subsets (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) :
    idealDivisors (∏i,P i)=Finset.univ.powerset.image (fun J:Finset ι=>∏i∈J,P i) := by
  have hs:=tuple_product_squarefree P hP hinj
  have hf:(idealDivisors (∏i,P i)).filter Squarefree=idealDivisors (∏i,P i) := by
    apply Finset.filter_eq_self.mpr
    intro J hJ
    exact hs.squarefree_of_dvd ((mem_idealDivisors hs.ne_zero).mp hJ)
  rw [←hf,squarefree_divisors_eq_image _ hs.ne_zero,tuple_product_support P hP hinj,
    Finset.powerset_image,Finset.image_image]
  congr 1
  funext J
  exact Finset.prod_image (fun i hi j hj h=>hinj h)

omit [Fintype ι] in
theorem tuple_subset_product_injective (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P) : Function.Injective (fun J:Finset ι=>∏i∈J,P i) := by
  let:∀i,(P i).IsMaximal:=fun i=>(Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  exact FirstCauchyArithmetic.family_product_injective P hinj

theorem sum_tuple_divisors (P:ι→Ideal O)(hP:∀i,Prime (P i))
    (hinj:Function.Injective P)(f:Ideal O→ℂ) :
    (∑j∈idealDivisors (∏i,P i),f j)=∑J∈Finset.univ.powerset,f (∏i∈J,P i) := by
  rw [tuple_divisors_eq_subsets P hP hinj,Finset.sum_image
    (fun J hJ K hK he=>tuple_subset_product_injective P hP hinj he)]

theorem originalTotal_slot_subsets (S:Finset (Ideal O))
    (P:ι→Ideal O)(hP:∀i,Prime (P i))(hinj:Function.Injective P)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    originalTotalPolynomial S (∏i,P i) η a W Z r z u=
      ∑J∈Finset.univ.powerset,
        originalFixedPolynomial S (∏i,P i) (∏i∈J,P i) η a W Z r z u := by
  rw [originalTotalPolynomial_eq_sectors S (tuple_product_squarefree P hP hinj)
    η a W hZ r z (fun _=>0),sum_tuple_divisors P hP hinj]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2882

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceTuples.lean; sha256: e6d953d30f31423f02a84c99092d4a527f2c5d59c3f5969c23df03df6659f02f -/
section Source2883
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

abbrev Tuple (L:ι→Finset (Ideal O)) := ∀i,↥(L i)
abbrev Assigned (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:↥J,↥(L i.val)
abbrev Remaining (L:ι→Finset (Ideal O))(J:Finset ι) := ∀i:{i:ι // i∉J},↥(L i.val)

def joinTuple (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(y:Remaining L J) : Tuple L :=
  (Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm (x,y)

theorem sum_tuple_split (L:ι→Finset (Ideal O))(J:Finset ι)(f:Tuple L→ℂ) :
    (∑q:Tuple L,f q)=∑x:Assigned L J,∑y:Remaining L J,f (joinTuple L J x y) := by
  rw [←(Equiv.piEquivPiSubtypeProd (fun i=>i∈J) (fun i=>↥(L i))).symm.sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_tuple_original (L:ι→Finset (Ideal O))(f:(ι→Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈Fintype.piFinset L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,Fintype.mem_piFinset.mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,Fintype.mem_piFinset.mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem tuple_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Function.Injective (fun i=>(q i).val) := by
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (q i).property (by simpa only [he] using (q j).property)

theorem original_selected_subset_sum (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
  calc
    _ = ∑q:Tuple L,∑J∈Finset.univ.powerset,(∏i,coeff i (q i).val)*
        originalFixedPolynomial S (∏i,(q i).val) (∏i∈J,(q i).val) η a W Z r z u := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [originalTotal_slot_subsets S _ (fun i=>hprime i _ (q i).property)
        (tuple_injective L hdis q) η a W Z r z hZ u,Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem original_selected_grouped (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,∑y:Remaining L J,
      (∏i,coeff i (joinTuple L J x y i).val)*
        originalFixedPolynomial S (∏i,(joinTuple L J x y i).val)
          (∏i∈J,(joinTuple L J x y i).val) η a W Z r z u := by
  rw [original_selected_subset_sum S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  exact sum_tuple_split L J _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2883

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceProducts.lean; sha256: 6c055681b8f5a0e7d1f0a98a8c487c98473e20537cbc93c13da82d76fbe5b8a2 -/
section Source2884
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge InverseInitialOverlap
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J) : Ideal O :=
  ∏i:↥J,(x i).val

def remainingIdeal (L:ι→Finset (Ideal O))(J:Finset ι)(y:Remaining L J) : Ideal O :=
  ∏i:{i:ι // i∉J},(y i).val

omit [Fintype ι] in
@[simp] theorem joinTuple_assigned (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:↥J) : joinTuple L J x y i.val=x i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
@[simp] theorem joinTuple_remaining (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(i:{i:ι // i∉J}) : joinTuple L J x y i.val=y i := by
  simp [joinTuple,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

omit [Fintype ι] in
theorem joinTuple_assigned_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i∈J,(joinTuple L J x y i).val)=assignedIdeal L J x := by
  rw [←Finset.prod_coe_sort J (fun i=>(joinTuple L J x y i).val)]
  simp only [joinTuple_assigned,assignedIdeal]

theorem joinTuple_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J) :
    (∏i,(joinTuple L J x y i).val)=assignedIdeal L J x*remainingIdeal L J y := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>(joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

theorem joinTuple_coefficient_product (L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(y:Remaining L J)(coeff:ι→Ideal O→ℂ) :
    (∏i,coeff i (joinTuple L J x y i).val)=
      (∏i:↥J,coeff i.val (x i).val)*(∏i:{i:ι // i∉J},coeff i.val (y i).val) := by
  have he := (Fintype.prod_subtype_mul_prod_subtype (fun i=>i∈J)
      (fun i=>coeff i (joinTuple L J x y i).val)).symm
  simp only [joinTuple_assigned,joinTuple_remaining] at he
  convert he using 1
  try simp only [assignedIdeal,remainingIdeal]
  congr 2
  ext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem assignedIdeal_ne_zero (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J) : assignedIdeal L J x≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi=>(hprime i.val _ (x i).property).ne_zero)

theorem residual_join (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    residual (∏i,(joinTuple L J x y i).val) (assignedIdeal L J x)=remainingIdeal L J y := by
  rw [joinTuple_product,InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]

theorem original_selected_grouped_products (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*
      ∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
        originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
          (assignedIdeal L J x) η a W Z r z u := by
  rw [original_selected_grouped S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [joinTuple_coefficient_product,joinTuple_product,joinTuple_assigned_product]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2884

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceOverlap.lean; sha256: 034fef443692274439aa3697ca5dc608d6c469de82a887e590f6bf895d29f54c -/
section Source2885
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingResidual (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)(a:Ideal O→ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,star ((∏i:{i:ι // i∉J},coeff i.val (y i).val)*
    (moebius (remainingIdeal L J y):ℂ))*
    conjugatedResidual S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) η a W Z r z G u

theorem assigned_remaining_squarefree (L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(y:Remaining L J) :
    Squarefree (assignedIdeal L J x*remainingIdeal L J y) := by
  rw [←joinTuple_product]
  exact tuple_product_squarefree _ (fun i=>hprime i _ (joinTuple L J x y i).property)
    (tuple_injective L hdis _)

theorem assigned_source_eq_remainingResidual (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    (∑y:Remaining L J,(∏i:{i:ι // i∉J},coeff i.val (y i).val)*
      originalFixedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
        (assignedIdeal L J x) η a W Z r z u)=
    (moebius (assignedIdeal L J x):ℂ)*(Z^(-G):ℝ)*η (assignedIdeal L J x)^2*
      (idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z G u) := by
  unfold remainingResidual
  simp only [star_sum,star_mul,star_star,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [originalFixedPolynomial_eq_conjugatedResidual S
    (assigned_remaining_squarefree L hprime hdis J x y) (dvd_mul_right _ _) η a W hZ r z G,
    InverseInitialOverlap.residual,quotient_mul_cancel (assignedIdeal_ne_zero L hprime J x)]
  ring

theorem original_selected_overlap (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(coeff:ι→Ideal O→ℂ)
    (η:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)
    (hZ:0<Z)(u:O) :
    (∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η a W Z r z u)=
    ∑J∈Finset.univ.powerset,∑x:Assigned L J,
      (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
      (Z^(-G J):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
      star (remainingResidual S L J x coeff η a W Z r z (G J) u) := by
  rw [original_selected_grouped_products S L hprime hdis coeff η a W Z r z hZ u]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  rw [assigned_source_eq_remainingResidual S L hprime hdis J x coeff η a W Z r z (G J) hZ u]
  ring

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2885

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialExcludedFourier.lean; sha256: 989f63e9d0f99ae54f71ef76f66d8044510787920c531fe385f1bea6439ecf0e -/
section Source2886
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedForcing
theorem original_tuples_excluded_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) hPE F hF hFE hsub η hη (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialExcludedFourier

end

end OAI

end Source2886

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceRemaining.lean; sha256: c92017f2ec708cc2ffad6850290abf8861f0fef1823988ac12a3e2e40b49fc00 -/
section Source2887
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic
open InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simpa only [he] using (y j).property)

theorem remaining_moebius (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using prime_product_moebius
    (fun i=>(y i).val) (fun i=>hprime i.val _ (y i).property)
    (remaining_injective L hdis J y) Finset.univ

def remainingPolynomial (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=>star (W v)) Z r z G u

theorem remainingResidual_eq_polynomial (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

theorem sum_tuple_pi (L:ι→Finset (Ideal O))
    (f:(∀i∈(Finset.univ:Finset ι),Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i _=>(q i).val))=
      ∑q∈(Finset.univ:Finset ι).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i (Finset.mem_univ i),
    Finset.mem_pi.mp hq i (Finset.mem_univ i)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i _=>(q i).val,Finset.mem_pi.mpr (fun i hi=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ:Finset {i:ι // i∉J}).pi (fun i=>L i.val),
        (∏i∈(Finset.univ:Finset {i:ι // i∉J}).attach,
          star (coeff i.val.val (q i.val i.property)))*
        residualNormalizedPolynomial S
          (assignedIdeal L J x*survivingProduct Finset.univ q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_tuple_pi]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  simp only [survivingProduct,remainingIdeal]
  rw [Finset.prod_attach _ (fun i=>star (coeff i.val (q i).val)),
    Finset.prod_attach _ (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2887

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceEnergy.lean; sha256: 4df72f0535b2c5ebcfcde58809d8428ca265f29c488efb43d00e677bcf71fc38 -/
section Source2888
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedMass (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ) : ℝ :=
  ‖∏i:↥J,coeff i.val (x i).val‖*Z^(-G)

def assignedTerm (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
    (Z^(-G):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
    star (remainingResidual S L J x coeff η (fun _=>1) W Z r z G u)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMass_nonneg (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ)(hZ:0<Z) : 0≤assignedMass L J x coeff Z G :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem assignedTerm_norm_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    ‖assignedTerm S L J x coeff η W Z r z G u‖≤
      assignedMass L J x coeff Z G*‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
  have hμ:‖(moebius (assignedIdeal L J x):ℂ)‖=1 := by simp [hj.2.1.moebius_eq]
  have hrow:‖idealRowHom u (assignedIdeal L J x)‖^2≤1 := by
    have hh:=admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass:=assignedMass_nonneg L J x coeff Z G hZ
  have he:‖η (assignedIdeal L J x)‖^2≤1:=pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTerm,remainingResidual_eq_polynomial S L hprime hdis]
  simp only [norm_mul,norm_pow,norm_star,norm_neg,norm_one,one_pow,one_mul,
    hμ,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G*‖η (assignedIdeal L J x)‖^2*
    ‖idealRowHom u (assignedIdeal L J x)‖^2*
    ‖remainingPolynomial S L J x coeff η W Z r z G u‖≤_
  calc
    _≤assignedMass L J x coeff Z G*1*1*
      ‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
      gcongr
    _=_:=by ring

theorem assignedTerm_energy_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (assignedMass L J x coeff Z G)^2*
      ∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (assignedTerm_norm_le S L hprime hdis J x coeff η hj hη W Z r z G hZ u) 2)
    (hw u)
  convert hh using 1 ; ring

theorem assigned_family_energy (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z G*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle Finset.univ rows w hw
    (fun x u=>assignedTerm S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh:=Real.sqrt_le_sqrt (assignedTerm_energy_le S L hprime hdis J x coeff η
    (hj x) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

theorem original_energy_of_remaining (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)(hZ:0<Z)
    (rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u‖^2)≤
      (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff Z (G J))^2*E := by
  have heq (u:O) :
      (∑q:Tuple L,(∏i,coeff i (q i).val)*
        originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u)=
      ∑J∈Finset.univ.powerset,∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap S L hprime hdis coeff η (fun _=>1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J:Finset ι) :
      Real.sqrt (∑u∈rows,w u*‖∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
    have hm:0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _=>assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb:=assigned_family_energy S L hprime hdis J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2))≤
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _=>mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ) (Real.sqrt_nonneg _))
    have hh:=Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u=>∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _≤(∑J∈Finset.univ.powerset,
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _=>hroot J)
    _=_:=by rw [←Finset.sum_mul,mul_pow,Real.sq_sqrt hE]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2888

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseAssignedCount.lean; sha256: ff0fae6ecac5980ebd9fc640416a319d8778960b705e387642b6a3958b1f5e3d -/
section Source2889
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount
local notation "O" => ActualEisensteinCubic.O

def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K

theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)

theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

theorem slots_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : σ → Ideal O → ℂ) (ha : ∀ i ∈ J, ∀ I ∈ L i, ‖a i I‖ ≤ 1)
    (T : Finset (J → Ideal O)) (hT : T ⊆ assignedTuples (fun i : J => L i)) :
    (∑ q ∈ T, ‖assignedCoefficient (fun i : J => a i) q‖) * U^(-(∑ i ∈ J, ell i)) ≤
      assignedConstant K b := by
  simpa only [Finset.sum_coe_sort] using
    restricted_normalized_mass_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI) (fun i : J => a i)
      (fun i I hI => ha i i.property I hI) T hT

theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

theorem slots_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples (fun i : J => L i)).card : ℝ) ≤
      assignedConstant K b * U^(∑ i ∈ J, ell i) := by
  simpa only [Finset.sum_coe_sort] using
    assigned_card_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI)

theorem assignedTuples_eq_empty {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (i : ι) (hi : L i = ∅) :
    assignedTuples L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (mem_assignedTuples L q).mp hq i
  simp only [hi, Finset.notMem_empty] at h

theorem assignedTuples_card_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (L : ι → Finset (Ideal O)) : (assignedTuples L).card = 1 := by
  simp [assignedTuples]

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI

end Source2889

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceMass.lean; sha256: e279abef4a100fc2722c69ef7c7705c078e43cd92a2250cfed50480857595708 -/
section Source2890
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily DetectorDictionaryInverseAssignedCount
local notation "O"=>HeckeFamily.O

private theorem sum_tuple_real {ι:Type*}[Fintype ι](L:ι→Finset (Ideal O))
    (f:(ι→Ideal O)→ℝ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈assignedTuples L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,(mem_assignedTuples L q).mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,(mem_assignedTuples L _).mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (L:ι→Finset (Ideal O))(J:Finset ι)(hJ:J.card≤K)(ell:ι→ℝ)
    (hL:∀i∈J,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i∈J,∀P∈L i,‖coeff i P‖≤1) :
    (∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤assignedConstant K b := by
  have he:=assigned_sum_normalized_le K hb hU (by simpa using hJ)
    (fun i:↥J=>ell i) (fun i:↥J=>L i)
    (fun i P hP=>hL i i.property P hP)
    (fun i:↥J=>coeff i) (fun i P hP=>hc i i.property P hP)
  rw [←sum_tuple_real] at he
  simp only [assignedMass,assignedCoefficient,Finset.sum_coe_sort] at he ⊢
  convert he using 1
  congr 1
  ext x
  simp

theorem all_assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(L:ι→Finset (Ideal O))(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1) :
    (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤
      (2:ℝ)^K*assignedConstant K b := by
  calc
    _≤∑J∈(Finset.univ:Finset ι).powerset,assignedConstant K b := by
      apply Finset.sum_le_sum
      intro J hJ
      exact assignedMass_sum_le K hb hU L J ((Finset.card_le_univ J).trans hK) ell
        (fun i _=>hL i) coeff (fun i _=>hc i)
    _=(2:ℝ)^Fintype.card ι*assignedConstant K b := by
      simp
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hK)
      (assignedConstant_pos K hb).le

theorem original_energy_with_assigned_count (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(r z:ℝ)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W U r z (∑i∈J,ell i) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      InverseInitialConjugateEnergy.originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W U r z u‖^2)≤
      ((2:ℝ)^K*assignedConstant K b)^2*E := by
  have hU0:0<U:=zero_lt_one.trans_le hU
  refine (original_energy_of_remaining S L hp hdis coeff η hj hη W U r z
    (fun J=>∑i∈J,ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _=>Finset.sum_nonneg
      (fun x _=>assignedMass_nonneg L J x coeff U (∑i∈J,ell i) hU0)))
  exact all_assignedMass_sum_le K hb hU hK L ell hL coeff hc

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2890

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceReindex.lean; sha256: ca4452a61ad755586df40bed019e4cc773a1d594066e186b3c8cb765f589ecf9 -/
section Source2891
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialPoissonBridge InverseInitialConjugateEnergy InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingIndexEquiv (J:Finset ι) : {i:ι // i∉J} ≃ ↥(Finset.univ\J) where
  toFun i:=⟨i.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  invFun i:=⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem remaining_product_attach {A:Type*}[CommMonoid A]
    (J:Finset ι)(f:{i:ι // i∉J}→A) :
    (∏i,f i)=∏i∈(Finset.univ\J).attach,f ⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩ := by
  exact ((remainingIndexEquiv J).symm.prod_comp f).symm

def remainingPi (L:ι→Finset (Ideal O))(J:Finset ι)(q:Remaining L J) :
    ∀i∈Finset.univ\J,Ideal O := fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).val

theorem sum_remaining_original (L:ι→Finset (Ideal O))(J:Finset ι)
    (f:(∀i∈Finset.univ\J,Ideal O)→ℂ) :
    (∑q:Remaining L J,f (remainingPi L J q))=∑q∈(Finset.univ\J).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp hq i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he ⟨i,(Finset.mem_sdiff.mp hi).2⟩)
  · intro q hq
    refine ⟨remainingPi L J q,Finset.mem_pi.mpr (fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_original_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ\J).pi L,(∏i∈(Finset.univ\J).attach,star (coeff i.val (q i.val i.property)))*
        residualNormalizedPolynomial S (assignedIdeal L J x*survivingProduct (Finset.univ\J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_remaining_original]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  unfold remainingIdeal survivingProduct remainingPi
  rw [remaining_product_attach J (fun i=>star (coeff i.val (q i).val)),
    remaining_product_attach J (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2891

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceFiber.lean; sha256: a2f745369681aec2717770a6bdf19a95740bc03e8fd35930c147b1d7eb8f1aca -/
section Source2892
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer
open InverseInitialConjugateEnergy
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)
    (P:Ideal O) : ℂ := slotCoefficient F.rowData (F.profile s) (U^(F.widths s)) (F.external s) P

omit [NeZero M] in
theorem fiberLists_prime (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(s:selected)(P:Ideal O)(hP:P∈fiberLists F selected s) : Prime P := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1

omit [NeZero M] in
theorem fiberLists_disjoint (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s)) :
    ((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hp:=livePrime_data M H (F.profile s) (lower s) (F.upper s) (U^(F.widths s))
    (Real.rpow_pos_of_pos hU _) (hV s s.property) P hP
  have hq:=livePrime_data M H (F.profile t) (lower t) (F.upper t) (U^(F.widths t))
    (Real.rpow_pos_of_pos hU _) (hV t t.property) P hQ
  rcases hsep s s.property t t.property (fun he=>hst (Subtype.ext he)) with h|h <;>
    linarith [hp.2.2.1,hp.2.2.2,hq.2.2.1,hq.2.2.2]

omit [NeZero M] in
theorem selectedSource_tuple (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(u:O) :
    selectedSource F selected W σ t bW u=
      ∑q:Tuple (fiberLists F selected),(∏s:selected,fiberCoefficient F s (q s).val)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,(q s).val) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  rw [sum_tuple_original (fiberLists F selected) (fun q=>
    (∏s:selected,fiberCoefficient F s (q s))*originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,q s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u)]
  unfold selectedSource
  apply Finset.sum_congr rfl
  intro q hq
  rw [tuple_coefficient]
  rfl

omit [NeZero M] in
theorem selectedSource_overlap (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(hU:0<U)
    (hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected))
    (u:O) :
    selectedSource F selected W σ t bW u=
      ∑J∈(Finset.univ:Finset selected).powerset,∑x:Assigned (fiberLists F selected) J,
        assignedTerm
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (fiberLists F selected) J x (fun s=>fiberCoefficient F s)
          (fixedBase F.rowData.η F.rowData.m F.rowData.f)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) (∑s∈J,F.widths s) u := by
  rw [selectedSource_tuple]
  exact original_selected_overlap _ (fiberLists F selected) (fiberLists_prime F selected)
    hdis (fun s=>fiberCoefficient F s) _ (fun _=>1) _ U F.r _
    (fun J=>∑s∈J,F.widths s) hU u

omit [NeZero M] in
theorem fiberAssigned_admissible (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s))
    (J:Finset selected)(x:Assigned (fiberLists F selected) J) :
    CanonicalQuadraticSieve.Admissible (assignedIdeal (fiberLists F selected) J x) := by
  have hdis:=fiberLists_disjoint F selected lower hU hV hsep
  have hp (s:↥J):Prime (x s).val:=fiberLists_prime F selected s.val _ (x s).property
  have hinj:Function.Injective (fun s:↥J=>(x s).val) := by
    intro s t he
    apply Subtype.ext
    by_contra hst
    exact Finset.disjoint_left.mp (hdis (Finset.mem_univ s.val) (Finset.mem_univ t.val) hst)
      (x s).property (by simpa only [he] using (x t).property)
  have hs (s:↥J):CanonicalQuadraticSieve.Supported (x s).val := by
    by_contra hn
    have hd:=livePrime_data M H (F.profile s.val) (lower s.val) (F.upper s.val)
      (U^(F.widths s.val)) (Real.rpow_pos_of_pos hU _) (hV s.val s.val.property)
      (x s).val (x s).property
    exact base_nonzero_prime F.rowData (x s).val (hp s)
      ((hlarge s.val s.val.property).trans_le hd.2.2.1)
      (fixedBase_zero_unsupported F.rowData.η F.rowData.m F.rowData.f
        F.rowData.lambda_dvd F.rowData.two_dvd (x s).val hn)
  have hprod (T:Finset ↥J):CanonicalQuadraticSieve.Supported (∏s∈T,(x s).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert s T hsT ih =>
      rw [Finset.prod_insert hsT]
      exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs s,ih⟩
  exact ⟨(hprod Finset.univ).1,tuple_product_squarefree _ hp hinj,(hprod Finset.univ).2⟩

omit [NeZero M] in
theorem fiberBase_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)(P:Ideal O) :
    ‖fixedBase F.rowData.η F.rowData.m F.rowData.f P‖≤1 := by
  rw [←baseCharacter_coeff]
  exact idealCoeff_norm_le_one _ _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2892

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceDeleted.lean; sha256: 24e3ccf48202d7da725a84207d394857a6d5978d3e115aae242b6f73fd88acc1 -/
section Source2893
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open InverseInitialMarkedDictionary
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

theorem deletedBase_zero_unsupported (data:RowData)(I:Ideal O)(hI:¬Supported I) :
    idealCoeff (deletedBase data) I=0 := by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,baseCharacter_coeff,
    fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd I hI]
  split_ifs <;> rfl

theorem deletedBase_eq_of_ne_zero (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) :
    idealCoeff (deletedBase data) I=fixedBase data.η data.m data.f I := by
  unfold deletedBase excluded at hI ⊢
  rw [idealCoeff_excludePrimes,baseCharacter_coeff] at hI ⊢
  split_ifs with h
  · rfl
  · exact False.elim (hI (by simp [h]))

def deletedSelectedSource (data:RowData)(M:Ideal O)[NeZero M]
    (H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O) : ℂ :=
  ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
    (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
      idealCoeff (deletedBase data) (∏i,p i))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter Supported)
      (∏i,p i) (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
      (twistedProfile W σ freq) Z r (∑i,ell i) u

theorem deleted_physical_slots_norm_initial (data:RowData)(u:NonzeroElement)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(a b ell:ι→ℝ)(ζ:ι→ℂ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤bW)(hV:∀i x,V i x≠0→x∈Set.Icc (a i) (b i))
    (hlarge:∀i,((deletedBase data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖deletedSelectedSource data M H W V Z r σ freq bW b ell ζ u.val‖ := by
  let L:=fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A:=fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p:ι→Ideal O)(hp:p∈Fintype.piFinset L)(_ha:A p≠0):
      idealCoeff (deletedBase data) (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hd:=livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
    exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ _ hd.1.ne_zero
      (ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨p i,hd.1⟩
        ((hlarge i).trans_le hd.2.2.1))
  have he:=indexed_conjugate_mark_norm (Fintype.piFinset L) (fun p=>∏i,p i) A
    (idealCoeff (deletedBase data)).toMonoidHom
    ((data.character u).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)))
    u.val (actual_deleted_row data u) W Z r (∑i,ell i) σ freq hZ
    (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial ((data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset L,A p*star (idealRowHom u.val (∏i,p i)))‖=_
  rw [he]
  unfold deletedSelectedSource
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  rfl

theorem marked_fixed_deletion (data:RowData)(rows:Finset NonzeroElement)
    (W:ℝ→ℂ)(X σ t bW:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤bW)
    (mark:NonzeroElement→ℂ) :
    (∑u∈rows,‖polynomial (data.character u) true W X σ t*mark u‖^2)≤
      ((IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P)).card:ℝ)*
      ∑j∈IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P),∑u∈rows,
        ‖polynomial ((data.character u).excludePrimes (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data))) true W
          (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  simpa only [one_mul] using InverseInitialExcludedEnergy.marked_family rows data.character
    (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) W X σ t bW hX hW mark
    (fun _=>1) (fun _ _=>zero_le_one)

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2893

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceArithmetic.lean; sha256: f3e64234b166647219fcae5df614885e057ef129c99b85b755576191d129a467 -/
section Source2894
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem tuple_supported (L:ι→Finset (Ideal O))(hs:∀i,∀P∈L i,Supported P)(q:Tuple L) :
    Supported (∏i,(q i).val) := by
  have hh (T:Finset ι):Supported (∏i∈T,(q i).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi]
      exact (supported_mul_iff _ _).mpr ⟨hs i _ (q i).property,ih⟩
  exact hh Finset.univ

theorem tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Admissible (∏i,(q i).val) :=
  ⟨(tuple_supported L hs q).1,tuple_product_squarefree _ (fun i=>hp i _ (q i).property)
    (tuple_injective L hdis q),(tuple_supported L hs q).2⟩

def remainingFromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) : Remaining L J :=
  fun i=>⟨t i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp ht i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩

theorem remainingIdeal_fromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    remainingIdeal L J (remainingFromPi L J t ht)=survivingProduct (Finset.univ\J) t := by
  unfold remainingIdeal
  rw [remaining_product_attach]
  rfl

theorem remaining_tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(t:∀i∈Finset.univ\J,Ideal O)
    (ht:t∈(Finset.univ\J).pi L) :
    Admissible (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_admissible L hp hs hdis _

theorem remaining_tuple_coprime (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    Pairwise (Function.onFun IsCoprime (fun i:↥(Finset.univ\J)=>t i.val i.property)) := by
  intro i j hij
  have hiP:=hp i.val _ (Finset.mem_pi.mp ht i.val i.property)
  have hjP:=hp j.val _ (Finset.mem_pi.mp ht j.val j.property)
  let:(t i.val i.property).IsMaximal:=(Ideal.isPrime_of_prime hiP).isMaximal hiP.ne_zero
  let:(t j.val j.property).IsMaximal:=(Ideal.isPrime_of_prime hjP).isMaximal hjP.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  dsimp only at he
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val)
    (fun hh=>hij (Subtype.ext hh))) (Finset.mem_pi.mp ht i.val i.property)
      (by rw [he];exact Finset.mem_pi.mp ht j.val j.property)

omit [DecidableEq ι] in
theorem tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(q:Tuple L) : outside E (∏i,(q i).val) := by
  intro P hP hd
  obtain ⟨i,hi,hdi⟩:=((hE P hP).dvd_finsetProd_iff (fun i=>(q i).val)).mp hd
  exact hout i _ (q i).property P hP hdi

theorem remaining_tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(J:Finset ι)(x:Assigned L J)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    outside E (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_outside L E hE hout _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2894

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialInputRadial.lean; sha256: 27f303928101330b5ec21efbaddb384e402bf5abeb0387fb813935667b4ad493 -/
section Source2895
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialInputRadial
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT
open InverseInitialConjugateEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_energy_summable (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(Y:ℝ)(hY:0<Y):
    Summable (fun u:O=>Φ (‖eisEmbedding u‖^2/Y)*
      (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)):=by
  let c:Finset ι→ℂ:=fun S=>a*supportMobius (fun i=>Ideal.span {p i}) S*
    secondInputCoefficient p hg Ψ j 1 1 test S
  have he (u:O):a*inputConjugateRow p hg pool Ψ j 1 1 test u=
      star (∑S∈pool.powerset,star (c S)*finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u):=by
    simp only [inputConjugateRow,supportConjugateSum,Finset.mul_sum,star_sum,star_mul,star_star,c]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  simp_rw [he,norm_star]
  exact finiteSquarefreeRow_smoothed_mean_square_summable (fun i=>Ideal.span {p i}) hg
    pool.powerset id (fun S=>star (c S)) Φ Y hY

theorem finite_rows_le_input_norm (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)
    (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (Y:ℝ)(hY:0<Y)(rows:Finset O)(hrows:∀u∈rows,‖eisEmbedding u‖^2≤Y):
    (∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)≤
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)‖:=by
  have hs:=input_energy_summable p hg pool Ψ j test a Φ Y hY
  have hr:=Complex.hasSum_re hs.hasSum
  have hfin:(∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)=
      ∑u∈rows,(Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)).re:=by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hone _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr (hrows u hu)⟩]
    simp only [one_mul,Complex.ofReal_re]
  rw [hfin]
  apply (hr.summable.sum_le_tsum rows (fun u _=>?_)).trans
  · rw [hr.tsum_eq]
    exact Complex.re_le_norm _
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hΦ _) (sq_nonneg _)

end SevenEighths.InverseInitialInputRadial

end

end OAI

end Source2895

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialTotalRows.lean; sha256: 8f0d9b43992bcf5de5640f543fba63babf97ca5fea1cfc86cf42e9fc027e368a -/
section Source2896
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalRows
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_rows_fourier_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(θ:ℝ),
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalEnergy.original_input_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨InverseClippingProfiles.momentOrder (4*J),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y θ
  have hZp:1<Z:=hZ₀.trans_le hZ
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot
    (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)) hdis hHs hPs
    (by intro i hi P hP;simpa only [norm_mul,FourierBridge.logPhase_norm,mul_one] using hac i hi P hP)
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent 1 θ le_rfl hbcap
  have hr:=InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ Ψ
    (assignedElement assigned qelem)
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P))) (childLogTest W θ) Z D)
    ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos (by linarith) _) rows hrows
  apply hr.trans
  simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,pow_mul,pow_two,mul_pow] using he

end SevenEighths.InverseInitialTotalRows

end

end OAI

end Source2896

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapHeight.lean; sha256: bb71fe1932b6a02cb11923bedfea4b5313238438f369d48e164da1f286edfae2 -/
section Source2897
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapHeight
open InverseInitialOverlapFourier InverseMoment JointLogSeparation

theorem twisted_polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(θ:ℝ),∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density (frequencyTwist g θ) xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ k t‖^2)≤C*E*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨C,hC,hboundMoment⟩ := frequencyTwist_fourier_moment J g
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro θ κ inst xj φ E hE hφ hbound
  have hint:=AnalyticBridge.schwartz_fourier_one_plus_integrable (frequencyTwist g θ) J
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density (frequencyTwist g θ) xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density (frequencyTwist g θ) xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density (frequencyTwist g θ) xj t‖ := by
    rw [show b t=density (frequencyTwist g θ) xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h,density_norm]
      using hint
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C*(1+‖θ‖)^(J+(volume:Measure ℝ).integrablePower) := by
    simpa only [hbnorm,h,density_norm]
      using hboundMoment θ
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_pow,←pow_mul,Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapHeight

end

end OAI

end Source2897

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOverlapEnergy.lean; sha256: 47a0b4f8f2d98822d59081c2d763c4315dedf739bc2e94a61d4ef7c40ca03b51 -/
section Source2898
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapEnergy
open InverseInitialOverlapFourier InverseMoment

theorem polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density g xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density g xj t*φ k t‖^2)≤C*E := by
  obtain ⟨C,hC,hint⟩ := density_moment g J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro κ inst xj φ E hE hφ hbound
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density g xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density g xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density g xj t‖ := by
    rw [show b t=density g xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h]
      using (hint xj).1
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C := by
    simpa only [hbnorm,h]
      using (hint xj).2
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapEnergy

end

end OAI

end Source2898

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialMarkedInputEnergy.lean; sha256: 963b1507663c7b0dddcbc3522d1409c129228c5822443a7e37e35e3af3b93ab5 -/
section Source2899
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialMarkedInputEnergy
open InverseMoment InverseInitialOverlapFourier InverseInitialOverlapEnergy
open InverseInitialRayAttachment InverseInitialArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem marked_input_integrable (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=>density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*supportMobius (fun i=>Ideal.span {p i}) A*
      Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)*
      wFresh (primeProductNorm p A/Z^D))
  convert hh using 1
  funext t
  unfold initialTest childLogTest
  ring

theorem marked_input_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(rows:Finset Eis)
      (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
      (wFresh:ℝ→ℂ)(Z D xj E:ℝ),0≤E→
      (∀t,(∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑u∈rows,‖∫t:ℝ,density g xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
            (childLogTest wFresh t) Z D) u)‖^2)≤C*E := by
  obtain ⟨C,hC,htransfer⟩ := polynomial_measure_energy g J
  refine ⟨C,hC,?_⟩
  intro F Ψ j rows I L a y wFresh Z D xj E hE henergy
  let ψ : Eis→ℝ→ℂ := fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
    (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
      (childLogTest wFresh t) Z D) u
  let φ : rows→ℝ→ℂ := fun u t=>ψ u.val t
  have hh := htransfer xj φ E hE
    (fun u=>marked_input_integrable p hg g F Ψ j u.val I L a y wFresh Z D xj)
    (fun t=>by
      exact (Finset.sum_coe_sort rows (fun u=>‖ψ u t‖^2)).le.trans (henergy t))
  exact (Finset.sum_coe_sort rows
    (fun u=>‖∫t:ℝ,density g xj t*ψ u t‖^2)).symm.le.trans hh

end SevenEighths.InverseInitialMarkedInputEnergy

end

end OAI

end Source2899

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialTotalFourier.lean; sha256: ddde1532380e794d6583eb2d58ebf6ad8c84e9b1a4e672ca9f09eee1b3cace23 -/
section Source2900
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalFourier
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
theorem original_fourier_energy_bound
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(xj θ:ℝ),
      (∑u∈rows,‖∫t:ℝ,density (frequencyTwist g θ) xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalRows.original_input_rows_fourier_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g J
  refine ⟨J+(volume:Measure ℝ).integrablePower,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y xj θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=>InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=>by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      exact henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y t)
  apply (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans
  apply ht.trans
  have hh:0≤C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)):=by positivity
  have he:=mul_le_mul_of_nonneg_right (show Cm≤Cm+1 by linarith) hh
  convert he using 1 <;> simp only [pow_mul,pow_two,mul_pow] <;> ring

end SevenEighths.InverseInitialTotalFourier

end

end OAI

end Source2900

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialOriginalHeight.lean; sha256: 1c330c524ea647b44df477aa7411602129b1724586a5131d84c694fd31c890ef -/
section Source2901
namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace SevenEighths.InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds FourierBridge
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

theorem logSchwartz_child (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    CubicReflectionKernel.logSchwartz (childLogTest W θ) a b ha
      ((child_support W θ).trans hs) (child_smooth W a b ha hs hW θ)=
    frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) θ:=by
  ext x
  simp only [CubicReflectionKernel.logSchwartz_apply,childLogTest,
    frequencyTwist_apply,Real.log_exp]
  ring

end SevenEighths.InverseInitialOriginalHeight

end

end OAI

end Source2901

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialInputReindex.lean; sha256: 16fecbeeb100ee0efd4833931deccf23e1e4dff5daba7c8ce83434c20bf34c1d -/
section Source2902
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=>L i.val) (fun i:I=>a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=>primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=>L i.val) (fun i:{i:σ//i∉J}=>a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=>primeSlot (L i) (a i) A)).symm

end SevenEighths.InverseInitialInputReindex

end

end OAI

end Source2902

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialResidualTupleEnergy.lean; sha256: f3ac466186ec68b827c4050f80c02589a0fa30f63538086c606d84197a836b5b -/
section Source2903
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualTupleEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_tuple_energy
    (Woriginal W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let _p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let _hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
    ∀(lo hi:σ→ℝ)(jlo jhi:ℝ),
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc jlo jhi→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (lo i) (hi i))→
      (∀v:σ→ℝ,∀yj yc:ℝ,(∀i∈all\assigned,v i∈Set.Icc (lo i) (hi i))→
        yj∈Set.Icc jlo jhi→0<yc→Woriginal (yj*yc/(∏i∈all\assigned,v i))≠0→W yc=1)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
      tupleColumns (originalOutside (originalSource Z r bo) (reflectionExcludedPrimes q))
        ((all\assigned).pi L) (fun t=>j*survivingProduct (all\assigned) t) j⊆F→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalFourier.original_fourier_energy_bound
    (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo)
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan lo hi jlo jhi hjratio hL hcoeff hFresh hP hcopTuple hPE hsub θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hdisPool:(all:Set σ).PairwiseDisjoint (fun i=>poolList F (L i)):=by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro P hPi hPk
    exact (Finset.disjoint_left.mp (hdis hi hk hik))
      (Finset.mem_filter.mp hPi).2 (Finset.mem_filter.mp hPk).2
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK
    (fun i=>poolList F (L i)) Hslot (fun i P=>coeff i P.val) hdisPool hHs
    (fun i hi P hP=>hPs i hi P.val (Finset.mem_filter.mp hP).2)
    (fun i hi P hP=>hac i hi P.val (Finset.mem_filter.mp hP).2)
    qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    (fun i P=>Real.log (slotRatio Z z i P.val)) (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) θ
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:Ideal.span {primaryGenerator j}=Ideal.span {assignedElement assigned qelem}:=
    (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1.trans hspan.symm
  have hid (u:O):
      (∑t∈(all\assigned).pi L,(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo) θ)
        (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ (elementCharacter χ)
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) (fun i=>poolList F (L i))
            (fun i P=>coeff i P.val*logPhase (-t) (Real.log (slotRatio Z z i P.val))))
            (childLogTest W t) Z D) u):=by
    have hh:=InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj.1 hP hcopTuple hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z lo hi hsum jlo jhi hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=>hFresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F hFa (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2) hsub
    rw [hh,InverseInitialOriginalHeight.logSchwartz_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryGenerator j) (assignedElement assigned qelem) hgj]
  simpa only [hid] using he

end SevenEighths.InverseInitialResidualTupleEnergy

end

end OAI

end Source2903

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialUniformFresh.lean; sha256: 2c60133faf21d1937236b50075859a4a5c097a8c450037543f9c05472644c6c3 -/
section Source2904
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialUniformFresh

theorem exists_uniform_fresh (K:ℕ)(a b:ℝ)(ha:0<a)(hab:a≤b):
    ∃(W:𝓢(ℝ,ℂ))(A B Bnorm:ℝ),0<A ∧ A≤B ∧ 0≤Bnorm ∧
      HasCompactSupport (W:ℝ→ℂ) ∧ tsupport (W:ℝ→ℂ)⊆Set.Icc A B ∧
      (∀x,‖W x‖≤Bnorm) ∧
      ∀{σ:Type*}[DecidableEq σ](I:Finset σ),I.card≤K→
      ∀(V:ℝ→ℂ),Function.support V⊆Set.Icc a b→
      ∀(y:σ→ℝ)(yj yc:ℝ),(∀i∈I,y i∈Set.Icc (1:ℝ) 2)→
        yj∈Set.Icc (1:ℝ) ((2:ℝ)^K)→0<yc→
        V (yj*yc/(∏i∈I,y i))≠0→W yc=1:=by
  let lo:=a/(2:ℝ)^K
  let hi:=lo+b*(2:ℝ)^K+1
  have hlo:0<lo:=by dsimp [lo];positivity
  have hb:0<b:=ha.trans_le hab
  obtain ⟨W,hWc,hWone,hWs⟩:=InverseSecondChildWindows.positive_cutoff lo hi hlo (by
    dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith)
  refine ⟨W,lo/2,hi+1,(SchwartzMap.seminorm ℝ 0 0) W,half_pos hlo,?_,by positivity,hWc,hWs,
    SchwartzMap.norm_le_seminorm ℝ W,?_⟩
  · dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith
  · intro σ dec I hI V hV y yj yc hy hj hc hn
    have hh:=InverseInitialOverlapFresh.overlap_column_interval I (fun _=>1) (fun _=>2) y
      a b 1 ((2:ℝ)^K) yj yc ha hab (by intros;norm_num) hy (by norm_num) hj hc (hV hn)
    simp only [Finset.prod_const,one_pow,mul_one,div_one] at hh
    apply hWone
    refine ⟨hh.1,?_⟩
    have hp:(2:ℝ)^I.card≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hI
    have hup:yc≤b*(2:ℝ)^K:=hh.2.trans (mul_le_mul_of_nonneg_left hp hb.le)
    dsimp [hi]
    linarith

end SevenEighths.InverseInitialUniformFresh

end

end OAI

end Source2904

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialResidualPool.lean; sha256: ff3226c303060df6da85c90eecb93c30d5cb398f288c1e26f0e7b4d549c79d4d -/
section Source2905
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialResidualPool
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "O"=>ActualEisensteinCubic.O

theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩

end SevenEighths.InverseInitialResidualPool

end

end OAI

end Source2905

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialResidualUniformEnergy.lean; sha256: f320fadc23cf79019777f5aa3b6a9e1576e5fccab40aec9e5c28337ca21e2ceb -/
section Source2906
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualUniformEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:Function.support (W:ℝ→ℂ)⊆Set.Icc A B:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialResidualTupleEnergy.original_residual_tuple_energy
    Woriginal W ao bo hao hso hWo A B 1 hA le_rfl hs (W.smooth ⊤) Φ hΦ hone Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hfloor,hcover⟩:=InverseInitialResidualPool.exists_original_complete_pool
    q Z r bo cap Btree hZp (zero_le_one.trans hBtree) ((all\assigned).pi L)
    (fun t=>j*survivingProduct (all\assigned) t) j hP (fun t _=>dvd_mul_right j _) hPE
  exact henergy Z hZ Dpool hfloor all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan (fun _=>1) (fun _=>2) 1 ((2:ℝ)^K) hjratio hL hcoeff
    (hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso)
    hP hcopTuple hPE hcover θ

end SevenEighths.InverseInitialResidualUniformEnergy

end

end OAI

end Source2906

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialMarkedAssignedGeometry.lean; sha256: 39ef7061ab2fb5b2d40952f1f84537806b5134169fbf0f9f3b1c5b8f2cb38f1a -/
section Source2907
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialMarkedAssignedGeometry
open HeckeFamily ConcretePrimeRowBridge
open DetectorDictionaryInverseMarkedReference InverseInitialQuotientGeometry
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

 def assignedGenerator (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(i:ι):O:=
  if h:i∈J then idealGenerator (x ⟨i,h⟩).val else 1

omit [Fintype ι] in
 theorem assignedGenerator_mem (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):assignedGenerator L J x i=idealGenerator (x ⟨i,hi⟩).val:=by
  simp only [assignedGenerator,dite_eq_left hi]

omit [Fintype ι] in
 theorem assignedGenerator_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):Ideal.span {assignedGenerator L J x i}=(x ⟨i,hi⟩).val:=by
  rw [assignedGenerator_mem L J x i hi,span_idealGenerator]

omit [Fintype ι] in
 theorem assignedGenerator_ne_zero (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (hne:∀i∈J,∀P∈L i,P≠0)(i:ι)(hi:i∈J):assignedGenerator L J x i≠0:=by
  rw [assignedGenerator_mem L J x i hi]
  exact idealGenerator_ne_zero _ (hne i hi _ (x ⟨i,hi⟩).property)

omit [Fintype ι] in
 theorem assignedElement_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J):
    Ideal.span {assignedElement J (assignedGenerator L J x)}=assignedIdeal L J x:=by
  rw [assignedElement,FiniteGaussPhase.span_finset_prod,←Finset.prod_coe_sort]
  unfold assignedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  exact assignedGenerator_span L J x i.val i.property

omit [Fintype ι] in
 theorem assignedGenerator_window_live (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(ell:ι→ℝ)(W:ι→ℝ→ℂ)
    (hW:∀i∈J,∀P∈L i,W i ((P.absNorm:ℝ)/U^(ell i))≠0):
    ∀i∈J,W i ((Ideal.absNorm (Ideal.span {assignedGenerator L J x i}):ℝ)/U^(ell i))≠0:=by
  intro i hi
  rw [assignedGenerator_span L J x i hi]
  exact hW i hi _ (x ⟨i,hi⟩).property

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_product (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ):
    (Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell)=
      ∏i:↥J,((x i).val.absNorm:ℝ)/U^(ell i.val):=by
  simp only [assignedIdeal,map_prod,Nat.cast_prod,Finset.prod_div_distrib,
    ←Real.rpow_sum_of_pos hU,Finset.sum_coe_sort,assignedCenter]

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_interval (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ)(K:ℕ)(hK:J.card≤K)
    (hL:∀i∈J,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2):
    ((Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell))∈Set.Icc (1:ℝ) ((2:ℝ)^K):=by
  rw [assigned_ratio_product L J x U hU ell]
  constructor
  · have hh:=Finset.prod_le_prod₀ (s:=Finset.univ)
      (f:=fun _i:↥J=>(1:ℝ)) (g:=fun i=>((x i).val.absNorm:ℝ)/U^(ell i.val))
      (fun _ _=>zero_le_one) (fun i _=>(hL i.val i.property _ (x i).property).1)
    simpa only [Finset.prod_const_one] using hh
  · calc
      _≤∏_i:↥J,(2:ℝ):=Finset.prod_le_prod₀
        (fun i _=>(zero_le_one.trans (hL i.val i.property _ (x i).property).1))
        (fun i _=>(hL i.val i.property _ (x i).property).2)
      _=(2:ℝ)^J.card:=by simp
      _≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hK

end SevenEighths.InverseInitialMarkedAssignedGeometry

end

end OAI

end Source2907

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialMarkedReserve.lean; sha256: 80b2747c502a06196d92003f14cf587dfc08fddcd462865a171d5a82976b038d -/
section Source2908
namespace OAI

namespace SevenEighths.InverseInitialMarkedReserve

theorem exists_reserve (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0<gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤gap/50 ∧
      0<τ ∧ τ≤gap/50 ∧ 0<π ∧ 0<eps ∧ 0<loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤r')(hhi:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end SevenEighths.InverseInitialMarkedReserve

end OAI

end Source2908

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceSourceEnergy.lean; sha256: 72a58db1108aaaf0473ef1bf9e36c257f1ae1059057eb10f8e4806c26481d76d -/
section Source2909
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
local notation "O"=>HeckeFamily.O

private theorem assigned_admissible {ι:Type}[Fintype ι][DecidableEq ι]
    (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J):Admissible (assignedIdeal L J x) := by
  apply tuple_admissible (fun i:↥J=>L i.val)
    (fun i=>hp i.val) (fun i=>hs i.val) _ x
  intro i hi j hj hij
  exact hdis (Finset.mem_univ _) (Finset.mem_univ _)
    (fun he=>hij (Subtype.ext he))

theorem original_source_energy
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (gap eps π eta τ loss:ℝ)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hetagap:eta≤gap/50)
    (hτ:0<τ)(hτgap:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∀q:ℕ,q≠0→∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      r+2*(∑i,ell i)≤m-2*gap→2*r+8*(∑i,ell i)≤3*m-2*gap→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  obtain ⟨degree,henergy⟩:=InverseInitialResidualUniformEnergy.original_residual_uniform_energy
    (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
    DetectorDictionaryInverseMarkedPadding.radialMajorant
    DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
    DetectorDictionaryInverseMarkedPadding.radialMajorant_one
    2 gap eps π eta τ loss (by norm_num) hgap heps hπ heta hetaone hetagap hτ hτgap hloss K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero m r hm hmcap hD hfirst hsecond hparent rows hrows θ
  have hUone:1<U:=hU₀.trans_le hU
  have hUpos:0<U:=zero_lt_one.trans hUone
  have hscale (i:ι):0<U^(ell i):=Real.rpow_pos_of_pos hUpos _
  have hnorm (i:ι)(P:Ideal O)(hP:P∈L i):(P.absNorm:ℝ)≤2*U^(ell i):=
    (div_le_iff₀ (hscale i)).mp (hratio i P hP).2
  let E:ℝ:=C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2
  have hE:0≤E:=by dsimp [E];positivity
  have hres (J:Finset ι)(x:Assigned L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomial (originalSource U r bo) L J x coeff χ
        (childLogTest W θ) U r (∑i,ell i) (∑i∈J,ell i) u‖^2)≤E := by
    have hJ:J.card≤K:=(Finset.card_le_univ J).trans hK
    have hH (i:ι):1≤2*U^(ell i) := by
      have hh:=Real.one_le_rpow hUone.le (hell i)
      linarith
    have hprod (T:Finset ι):
        (∏i∈T,2*U^(ell i))≤U^((∑i∈T,ell i)+eta) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUpos,
        Real.rpow_add hUpos]
      rw [mul_comm (U^(∑i∈T,ell i))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
      exact (pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ T).trans hK)).trans hpow
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible L hp hs hdis J x
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P)) hdis
      (fun i _=>hH i) (fun i _=>hnorm i)
      (fun i _ P hP=>by simpa using hc i P hP)
      (assignedGenerator L J x) ell (fun _=>1) (fun _=>2) primeW
      (fun i _=>hell i)
      (assignedGenerator_ne_zero L J x (fun i _ P hP=>(hp i P hP).ne_zero))
      (fun i _=>hprimeW i) (assignedGenerator_window_live L J x U ell primeW (fun i _=>hlive i))
      (conjugateIdealCharacter χ)
      (fun u=>by simpa [elementCharacter,conjugateIdealCharacter] using hχ (Ideal.span {u}))
      hperiod hzero (r+(∑i,ell i)-2*(∑i∈J,ell i)) m r hm hmcap (hD J)
      (by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ).trans hpow)
      (by simpa [assignedCenter] using hprod (Finset.univ\J))
      rfl (by simpa [assignedCenter] using hfirst) (by simpa [assignedCenter] using hsecond)
      (by simpa [assignedCenter] using hparent) rows hrows (assignedIdeal L J x) hje
      (assignedElement_span L J x)
      (assigned_ratio_interval L J x U hUpos ell K hJ (fun i _=>hratio i))
      (fun i _=>hp i) (fun i _ P hP _=>hratio i P hP)
      (remaining_tuple_admissible L hp hs hdis J x)
      (remaining_tuple_coprime L hp hdis J)
      (remaining_tuple_outside L (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
        hout J x) (-θ)
    simpa only [one_mul,remainingPolynomial_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp hdis ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (assigned_admissible L hp hs hdis) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2909

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferencePaddedEnergy.lean; sha256: e42a888cc31fdd5ca02bbd99fca6ee3d64d8844efaffd9c1067bda0e94e38981 -/
section Source2910
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure Filter
local notation "O"=>HeckeFamily.O

theorem padded_source_energy
    (W:ℝ → ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃eta:ℝ,0<eta ∧ ∃degree:ℕ,∀q:ℕ,q≠0 → ∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
    ∀(L:ι → Finset (Ideal O))(ell:ι → ℝ)(coeff:ι → Ideal O → ℂ),
      (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
      (∀i,∀P∈L i,Supported P) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L) →
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,‖coeff i P‖≤1) →
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P) →
    ∀(primeW:ι → ℝ → ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0) →
    ∀χ:Ideal O →*ℂ,(∀I,‖χ I‖≤1) →
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ)) →
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I →
        conjugateIdealCharacter χ I=0) →
    ∀r rr:ℝ,0≤r → r-eta≤rr → rr≤r →
      r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U rr bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U rr (∑i,ell i) u‖^2)≤
      C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨ρ,gap,eta,τ,π,eps,loss,hρ,hρmax,hρε,hgap,hgapρ,heta,hetamax,hetagap,
    hτ,hτgap,hπ,heps,hloss,hcost⟩:=InverseInitialMarkedReserve.exists_reserve εm hεm
  obtain ⟨degree,henergy⟩:=original_source_energy W ao bo hao hab hsW hW
    gap eps π eta τ loss hgap heps hπ heta (by linarith) hetagap hτ hτgap hloss K
  have hev:∀ᶠU:ℝ in atTop,(2:ℝ)^K≤U^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩:=eventually_atTop.mp hev
  refine ⟨eta,heta,degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  refine ⟨C,max U₀ Uscale,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero r rr hr hrlo hrhi hfirst hsecond rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hs0:0≤∑i,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hG (J:Finset ι):0≤∑i∈J,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hGmax (J:Finset ι):(∑i∈J,ell i)≤∑i,ell i:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)
  have hcap (J:Finset ι):
      0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤rr+(∑i,ell i)-2*(∑i∈J,ell i) ∧
      rr+2*(∑i,ell i)≤1+ρ-2*gap ∧
      2*rr+8*(∑i,ell i)≤3*(1+ρ)-2*gap ∧ rr+(∑i,ell i)+7*eta≤2 :=
    InverseInitialMarkedReserve.shifted_capacity ρ gap eta r rr _ _ hρ hρmax hgapρ
      heta hetamax hr hs0 (hG J) (hGmax J) hrlo hrhi hfirst hsecond
  have hbase:=hcap ∅
  have hrows':∀u∈rows,‖eisEmbedding u‖^2≤U^(1+ρ) := by
    intro u hu
    refine (hrows u hu).trans ?_
    calc U=U^(1:ℝ):=(Real.rpow_one U).symm
         _≤U^(1+ρ):=Real.rpow_le_rpow_of_exponent_le hUone.le (by linarith)
  have hh:=henergy U hU0 (hscale U ((le_max_right _ _).trans hU)) hK L ell coeff hell hp hs
    hdis hratio hc hout primeW hprimeW hlive χ hχ hperiod hzero (1+ρ) rr
    hbase.1 hbase.2.1 (fun J=>(hcap J).2.2.1) hbase.2.2.2.1 hbase.2.2.2.2.1
    hbase.2.2.2.2.2 rows hrows' θ
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hUone.le
  linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2910

/- Original source: OAI/NumberTheory/DirichletL/Detector/DetectorMomentGates.lean; sha256: e14ccde841c8d8d70ced51d66d5089c41a9d1ab93e56961a9aaf419e6937a88f -/
section Source2911
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentPeriod (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℕ:=
  ∏j:Sum Bool (RayQuotient.Characters M H),
    (baseCharacter (sourceMomentData M H hH S hS η j)).period

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

theorem sourceMomentPeriod_ne_zero (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    sourceMomentPeriod M H hH S hS η≠0:=by
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>Nat.ne_of_gt (Character.period_pos _))

theorem sourceMomentPeriod_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    Ideal.span {(sourceMomentPeriod M H hH S hS η:O)}≤
      (baseCharacter (sourceMomentData M H hH S hS η j)).modulus:=by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have hd:(baseCharacter (sourceMomentData M H hH S hS η j)).period∣
      sourceMomentPeriod M H hH S hS η:=Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨n,hn⟩:=hd
  rw [hn,Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Character.period_mem _)

theorem sourceMomentConductorBound_pos (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    0<sourceMomentConductorBound M H hH S hS η:=by
  unfold sourceMomentConductorBound
  positivity

theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_deleted_base_gates (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    let q:=sourceMomentPeriod M H hH S hS η
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    ∀j:Sum Bool (RayQuotient.Characters M H),
      let χ:=(baseCharacter (sourceMomentData M H hH S hS η j)).excludePrimes
        (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (∀x,‖elementCharacter (idealCoeff χ).toMonoidHom x‖≤1) ∧
      FactorsModulo (fixedBaseConductor (deletedPeriod q))
        (elementCharacter (idealCoeff χ).toMonoidHom):=by
  dsimp only
  let q:=sourceMomentPeriod M H hH S hS η
  have hq:q≠0:=sourceMomentPeriod_ne_zero M H hH S hS η
  refine ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,?_⟩
  intro j
  exact (deleted_physical_base_gates _ q hq (sourceMomentPeriod_le M H hH S hS η j)).2.2

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2911

/- Original source: OAI/NumberTheory/DirichletL/Detector/DetectorMomentFiberGates.lean; sha256: 6e5374af596fc8f2ba7daf95b8ed1b024df28d5955c86fae1d4b95431451f1b9 -/
section Source2912
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_large_eventually
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→
      ∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,∀s:Slot,
        ((baseCharacter (B.fiber bin j J K hne).rowData).modulus.absNorm:ℝ)<
          1*(Z^d)^((B.fiber bin j J K hne).widths s):=by
  filter_upwards [sourceMoment_large_eventually M H hH S hS η ell hell] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hw bin j J K hne s
  change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s)
  rw [hdata,hw,one_mul]
  exact hZ.2 d hd j s

theorem sourceMoment_fiber_support {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    {Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ}
    (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i)
    (hprofile:B.profile=(fun _=>(F.W:ℝ→ℂ)))(hupper:B.upper=(fun _=>2))
    (bin:B.Bin)(j:Sum Bool (RayQuotient.Characters M H))
    (J K:Fin (HeckeDetectorWitnessRows.dyadicLength U))
    (hne:(B.fiberRows bin j J K).Nonempty):
    ∀s x,(B.fiber bin j J K hne).profile s x≠0→
      x∈Set.Icc 1 ((B.fiber bin j J K hne).upper s):=by
  intro s x hx
  change B.profile s x≠0 at hx
  change x∈Set.Icc 1 (B.upper s)
  rw [hprofile] at hx
  rw [hupper]
  exact F.complex_support hx

end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2912

/- Original source: OAI/NumberTheory/DirichletL/Detector/DetectorMomentPrimeGeometry.lean; sha256: d56137ee520fdc699bb8a3990fe0a876fbf007094000bdb7cd5b5c392332ab03 -/
section Source2913
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem sourceMoment_physical_scale (Z d ell : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(ell/d)=Z^ell := by
  rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]

theorem sourceMoment_separation_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hinj : Function.Injective ell) :
    ∀ᶠ Z : ℝ in atTop, 1≤Z ∧ ∀d : ℝ,0<d→∀s t : Slot,s≠t→
      2*(Z^d)^(ell s/d)<1*(Z^d)^(ell t/d) ∨
      2*(Z^d)^(ell t/d)<1*(Z^d)^(ell s/d) := by
  have hs : ∀ᶠ Z : ℝ in atTop,∀s t : Slot,s≠t→
      2*Z^(ell s)<1*Z^(ell t) ∨ 2*Z^(ell t)<1*Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro s
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : s=t
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h he))
    rcases lt_or_gt_of_ne (fun h=>he (hinj h)) with hlt|hlt
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell s) (ell t)
        (by norm_num) hlt] with Z hZ _
      exact Or.inl hZ
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell t) (ell s)
        (by norm_num) hlt] with Z hZ _
      exact Or.inr hZ
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro d hd s t hst
  simp only [sourceMoment_physical_scale Z d _ (by linarith) hd.ne']
  exact hs s t hst

theorem sourceMoment_fixedBase_norm_one (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    ‖fixedBase data.η data.m data.f P‖=1 := by
  rw [←baseCharacter_coeff]
  exact PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
    (baseCharacter data) P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hlarge)

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖≤1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re)≤1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re≤0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ)≤1)

theorem sourceMoment_tuple_quotient {ι : Type*} [Fintype ι]
    (data : RowData) (A : ι→ℂ) (p : ι→Ideal O) :
    star (∏s,A s)/fixedBase data.η data.m data.f (∏s,p s)=
      ∏s,star (A s)/fixedBase data.η data.m data.f (p s) := by
  rw [map_prod,star_prod,Finset.prod_div_distrib]

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0<U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem sourceMoment_live_denominator {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0<U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0<U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖≤1 := by
  rw [norm_div,norm_star,sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=>norm_nonneg _)
    (fun s _=>sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

theorem sourceMoment_capacity_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hell : ∀s,0≤ell s) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      (∀s,1≤2*(Z^d)^(ell s/d)) ∧ ∀selected : Finset Slot,
      (∏s:selected,2*(Z^d)^(ell s/d))≤
        (Z^d)^((∑s:selected,ell s/d)+ε) := by
  have ht := (tendsto_rpow_atTop (show 0<ε/200 by positivity)).eventually
    (eventually_ge_atTop ((2:ℝ)^Fintype.card Slot))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with Z ht hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hd0 : 0<d := by linarith
  have hz0 : 0<Z := zero_lt_one.trans_le hZ
  have hu0 : 0<Z^d := Real.rpow_pos_of_pos hz0 _
  have hu1 : 1≤Z^d := Real.one_le_rpow hZ hd0.le
  refine ⟨?_,?_⟩
  · intro s
    have hh : 1≤(Z^d)^(ell s/d) := Real.one_le_rpow hu1 (div_nonneg (hell s) hd0.le)
    linarith
  · intro selected
    have hf : (2:ℝ)^selected.card≤(2:ℝ)^Fintype.card Slot :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ selected)
    have hp : (2:ℝ)^selected.card≤(Z^d)^ε := by
      rw [←Real.rpow_mul hz0.le]
      exact (hf.trans ht).trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
      ←Real.rpow_sum_of_pos hu0,Real.rpow_add hu0]
    calc
      _ ≤ (Z^d)^ε*(Z^d)^(∑s:selected,ell s/d) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu0.le _)
      _ = _ := mul_comm _ _

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_prime_geometry_eventually
    {Δ : ℝ} {D : Parameters.HighData Δ} (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=>D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1≤2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s))≤
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ)≤2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖≤1 := by
  filter_upwards [sourceMoment_separation_eventually D.ell D.slots_injective,
    sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0<d := by linarith
  have hu : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact sourceMoment_live_disjoint M H F (fun s=>D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1≤2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s))≤(Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=>hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=>livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=>livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=>hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ)≤2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖≤1
        rw [hprofile,hwidths]
        exact sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) (fun s:selected=>B.external s) hu (fun s=>hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.ProbeHighRowFamily

end

end OAI

end Source2913

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferencePrimeGates.lean; sha256: aed901c0afa3c508a1ca3f907ef07e2143c4489f7c5635785d2b75a4a9faa2a8 -/
section Source2914
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O

theorem deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0<ell s) :
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem deleted_source_live_prime {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact ProbeHighRowFamily.sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2914

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceShift.lean; sha256: 5d9a952130fa1a9fc44adcf3f01363d910a93bdb48c27102e9e22ab45b33d091 -/
section Source2915
namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter IdealMobiusDivisorSum
open DetectorDictionaryInverseRawInitialGates
local notation "O"=>HeckeFamily.O

def shiftedExponent (_data:RowData)(U r:ℝ)(j:Ideal O) : ℝ :=
  r-Real.logb U (j.absNorm:ℝ)

theorem marked_shift_eventually (data:RowData)(eta:ℝ)(heta:0<eta) :
    ∀ᶠU:ℝ in atTop,1<U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0<U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

theorem shifted_padding_capacities (r r' ell ρ gap eta:ℝ)
    (hr:0≤r)(hell:0≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3)
    (hgap:2*gap≤ρ)(hgap₃:2*gap≤3*ρ) :
    -eta≤r' ∧ r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧ r'+ell<1 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem shifted_source_box (r r' ell G eta:ℝ)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGell:G≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(_heta:0≤eta)(hetaSmall:eta≤1/7) :
    -2≤r'+ell-2*G ∧ r'+ell+7*eta≤2 := by
  constructor <;> linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2915

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceDeletedEnergy.lean; sha256: 863a349427c1d7aef0d480a89ee40abd6708c4e9add6cec8fe00f3426e3199d7 -/
section Source2916
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=>HeckeFamily.O

theorem deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=>livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=>livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem deleted_source_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι≤K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0≤ell i) → (∀i,(ζ i).re≤1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=>livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)<U^(ell i)) →
    ∀r:ℝ,0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=>F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2)≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hUp:0<U:=zero_lt_one.trans hUone
  have hjshift: r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=>livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=>star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖≤1:=
    deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=>deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=>by rw [hqset];exact (hg i P hP).2.1)
    (fun _=>F.W) (fun _=>F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2916

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedUniform.lean; sha256: 23c29fa13356192fa68b824104c30b0f37c3b759aaefc2dccf2f434d622aba7a -/
section Source2917
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.DetectorDictionaryInverseMarkedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeDetectorRawFiber

private theorem clipped_one_zero (W : ℝ→ℂ) : clippedTest W 1 0=W := by
  funext x
  simp [clippedTest,childLogTest,logPhase]

theorem family_mode_integrable (χ : Character) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    Integrable (fun v : ℝ=>familyDensity scaled reverse n U tstar r σ t 1 v*
      (polynomial χ true (childLogTest referenceWindow v) D 0 0*A)) := by
  simpa only [familyDensity,zero_add,mul_assoc] using
    (polynomial_mode_integrable χ true (logSource scaled reverse n U tstar r σ t)
      referenceWindow (13/4) 1 0 D hD
      (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)).mul_const A

theorem family_polynomial_fourier (χ : Character) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    polynomial χ true (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A=
      ∫v : ℝ,familyDensity scaled reverse n U tstar r σ t 1 v*
        (polynomial χ true (childLogTest referenceWindow v) D 0 0*A) := by
  have h:=polynomial_clipped_fourier χ true
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow (13/4) 1 0 D (by norm_num) hD
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy)
  rw [clipped_one_zero] at h
  rw [h,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  simp only [familyDensity,logSource_eq_logSchwartz,zero_add,mul_assoc]

theorem moving_finite_energy (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type*}(rows : Finset ι)
      (χ : ι→Character)(A : ι→ℂ)(D E : ℝ),0<D→0≤E→
    (∀v : ℝ,(∑u∈rows,‖polynomial (χ u) true (childLogTest referenceWindow v) D 0 0*A u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀scaled reverse : Bool,∀n : ℕ,n≤2→∀U : ℝ,0<U→
    ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈rows,‖polynomial (χ u) true
      (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A u‖^2)
      ≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro ι rows χ A D E hD hE href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  have hb:=polynomial_clipped_energy rows χ true A W (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t) (W.smooth ⊤)
    referenceWindow (13/4) 1 0 D E J (by norm_num) hD hE
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy) href
  rw [clipped_one_zero] at hb
  simp only [norm_zero,add_zero,one_pow,mul_one] at hb
  have hm:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  apply hb.trans
  calc
    _≤E*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hE
    _= _:=by rw [mul_pow,←pow_mul];ring_nf

theorem logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) :
    logTest W n=(HeckeDetectorRowwisePolynomial.logProfile^[n]) W := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [logTest,Function.iterate_succ_apply',←ih]

section Fiber
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_inverse_source
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) (σ t : ℝ) :
    (inverseSourceSchwartz false false n U tstar F.r σ t : ℝ→ℂ)=
      twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t := by
  funext x
  simpa only [Bool.false_eq_true,ite_false,HeckeDetectorCoefficientTransfer.orientedProfile,
    logTest_eq_iterate,Fiber.inverseProfile] using
    inverseSourceSchwartz_apply false false n U tstar F.r σ t x

theorem fiber_inverse_polynomial
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (u : FreeRow) :
    polynomial (F.family u F.label) true
      (inverseSourceSchwartz false false n U tstar F.r σ t) (U^F.r) 0 0*
        F.physicalProduct selected u=
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u := by
  rw [fiber_inverse_source,polynomial_twistProfile]

theorem fiber_inverse_fourier
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (hU : 0<U) (u : FreeRow) :
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u=
      ∫v : ℝ,familyDensity false false n U tstar F.r σ t 1 v*
        (polynomial (F.family u F.label) true (childLogTest referenceWindow v) (U^F.r) 0 0*
          F.physicalProduct selected u) := by
  rw [←fiber_inverse_polynomial]
  exact family_polynomial_fourier _ _ false false n U tstar F.r σ t _
    (Real.rpow_pos_of_pos hU _)
end Fiber

theorem fiber_inverse_energy_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,C,hC,hb⟩:=moving_finite_energy J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ t
  have hh:=hb F.rows (fun u=>F.family u F.label) (F.physicalProduct selected)
    (U^F.r) E (Real.rpow_pos_of_pos hU _) hE href false false n hn U hU tstar F.r σ hσ t
  simpa only [fiber_inverse_polynomial] using hh

theorem fiber_inverse_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+height)^K := by
  obtain ⟨K,C,hC,hb⟩:=fiber_inverse_energy_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ height t _ ht
  apply (hb F selected hU E hE href n hn σ hσ t).trans
  have hnorm : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  gcongr

theorem fiber_inverse_height_budget (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀A epsInternal : ℝ,0≤A→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤(A*U^(1+epsInternal))*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)
      ≤C*A*U^(1+epsInternal)*(1+height)^K := by
  obtain ⟨K,C,hC,hb⟩:=fiber_inverse_height_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU A epsInternal hA
    href n hn σ hσ height t hheight ht
  simpa only [mul_assoc] using hb F selected hU (A*U^(1+epsInternal))
    (mul_nonneg hA (Real.rpow_nonneg hU.le _)) href n hn σ hσ height t hheight ht

end SevenEighths.DetectorDictionaryInverseMarkedUniform

end

end OAI

end Source2917

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedPhysicalRows.lean; sha256: 6f99894c98554f1016e9b14143ea1e7efca109f1d96edad87cb5d1a55c83e6f4 -/
section Source2918
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorPhysicalSelection
open InverseInitialPhysicalSlots InverseInitialRawDictionary InverseInitialDetectorSource
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open InverseInitialExcludedPeriod CanonicalRowCompletion IdealMobiusDivisorSum InverseMoment
local notation "O"=>HeckeFamily.O

 def actualRow (u:FreeRow):NonzeroElement:=⟨u.val,u.property.1⟩

 theorem actualRow_injective:Function.Injective actualRow:=by
  intro u v he
  exact Subtype.ext (congrArg (fun w:NonzeroElement=>w.val) he)

 theorem actual_rows_sum (rows:Finset FreeRow)(f:NonzeroElement→ℝ):
    (∑u∈rows.image actualRow,f u)=∑u∈rows,f (actualRow u):=
  Finset.sum_image (fun _u _ _v _ h=>actualRow_injective h)

 theorem oriented_child (reverse:Bool)(W:ℝ→ℂ)(v:ℝ):
    orientedProfile reverse (childLogTest W v)=
      childLogTest (orientedProfile reverse W) (orientedFrequency reverse v):=by
  cases reverse
  · rfl
  · exact DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate W v

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem physicalProduct_eq (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(u:FreeRow):
    F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s):=by
  simp only [Fiber.physicalProduct,physical]
  exact (Finset.prod_coe_sort selected _).symm

 theorem fiber_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(σ freq bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H (orientedProfile F.reverse W)
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            σ (orientedFrequency F.reverse freq) bW
            (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hU0:0<U:=zero_lt_one.trans hU
  let mark:NonzeroElement→ℂ:=fun u=>∏s:selected,
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val (F.profile s) (F.upper s)
      (U^(F.widths s)) (F.external s)
  have hw:∀x,orientedProfile F.reverse W x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by cases F.reverse <;> simp [orientedProfile,hz])
  have he:(∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows.image actualRow,‖polynomial (F.rowData.character u) true
        (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq)*mark u‖^2:=by
    rw [actual_rows_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hn:=norm_of_oriented_coefficients (F.family u F.label)
      (F.rowData.character (actualRow u)) F.reverse (F.row_coeff u hu)
      true W (U^F.r) σ freq (Real.rpow_pos_of_pos hU0 _)
    rw [norm_mul,hn,physicalProduct_eq,norm_mul]
    rfl
  rw [he]
  apply (marked_fixed_deletion F.rowData (F.rows.image actualRow)
    (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq) bW
    (Real.rpow_pos_of_pos hU0 _) hw mark).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_rows_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hjpos:0<(j.absNorm:ℝ):=zero_lt_one.trans_le (excluded_divisor_norm F.rowData j hj).1
  have hr:U^(shiftedExponent F.rowData U F.r j)=U^F.r/(j.absNorm:ℝ):=
    by rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 (ne_of_gt hU) hjpos]
  have hn:=deleted_physical_slots_norm_initial F.rowData (actualRow u) M H
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U (shiftedExponent F.rowData U F.r j) σ (orientedFrequency F.reverse freq) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU0 hw (fun s=>hV s s.property)
    (fun s=>hlarge s s.property)
  rw [hr] at hn
  exact congrArg (fun x:ℝ=>x^2) hn

 theorem fiber_child_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(v bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H
            (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            0 0 bW (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hw:∀x,childLogTest W v x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by simp only [childLogTest,hz,zero_mul])
  have hh:=fiber_rows_le_deleted_sources F selected (childLogTest W v) 0 0 bW lower hU hw hV hlarge
  simpa only [oriented_child,orientedFrequency,neg_zero,ite_self] using hh

omit [NeZero M] in
theorem actual_rows_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (u:NonzeroElement)(hu:u∈F.rows.image actualRow):
    ((Ideal.span {u.val}).absNorm:ℝ)≤U:=by
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
  exact F.row_norm v hv

end SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows

end

end OAI

end Source2918

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferenceFiberEnergy.lean; sha256: 43703afe82fd36fc057045e279bd09ff907bf607712b2581b39bf40e52d9a16c -/
section Source2919
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem fiber_reference_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card≤K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0≤F.widths s) → (∀s∈selected,(F.external s).re≤1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)<U^(F.widths s)) →
      0≤F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2)≤C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=>deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=>hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=>hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b≤U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1<U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=>F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=>F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=>u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=>Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2≤U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2≤
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=>Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=>F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
        (fun s:selected=>F.external s) u.val‖^2)≤
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=>F.widths s) (fun s:selected=>F.external s)
      (fun s=>hell s s.property) (fun s=>hext s s.property) hdis'
      (fun s=>hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_)≤_
  calc
    _≤(Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0≤(Tbad.card:ℝ) by positivity]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

end Source2919
