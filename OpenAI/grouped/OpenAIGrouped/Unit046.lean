import OpenAIGrouped.Unit045
import OpenAIGrouped.Unit025
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit008
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit023
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit014

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceCapacity.lean; sha256: bf703b5908f202dcd9765215dfce6950c8e0be9907c1c31d078f434969a83894 -/
section Source1840
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeScale HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sectorConductorFactor (η₀ : Character) : ℕ :=
  η₀.modulus.absNorm*fixedConductorFactor*(M.absNorm*η₀.modulus.absNorm)

lemma initial_sector_modulus (η₀ : Character) (u : FreeRow) (θ : RayQuotient.Characters M H) :
    ((naturalRow η₀ u.val u.property.1).character.product (relativeCharacter M H hH η₀ θ)).modulus.absNorm≤
      sectorConductorFactor M η₀*(Ideal.span {u.val}).absNorm := by
  have hn:=(naturalRow η₀ u.val u.property.1).natural_modulus_bound
  have hs:=relativeCharacter_modulus M H hH η₀ θ
  apply (product_modulus_bound _ _).trans
  apply (Nat.mul_le_mul hn hs).trans_eq
  unfold sectorConductorFactor
  ring

theorem eventually_source_sector_capacity
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (margin : ℝ) (hmargin : 0<margin) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),∀d : ℝ,∀u : FreeRow,
      ((Ideal.span {u.val}).absNorm:ℝ)≤Z^(d-margin)→
      ∀θ : RayQuotient.Characters M H,
      (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
        (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)≤Z^margin := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro label d u hu θ
  have hb : (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
      (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)*((Ideal.span {u.val}).absNorm:ℝ) := by
    exact_mod_cast initial_sector_modulus M H hH (sourceMomentBase M H hH S hS η label) u θ
  apply hb.trans
  calc
    _≤Z^margin*Z^(d-margin) := mul_le_mul (hz label) hu (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

theorem sourceData_fiber_sector_capacity {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : HeckeDetectorBatch.Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      (∀u∈B.rows,ProbeHighRowFamily.rowNorm u≤Z^(d-D.t))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀u∈(B.fiber bin label J K hne).rows,∀θ : RayQuotient.Characters F.modulus ⊤,
      (((naturalRow (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
        u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_sector_capacity F.modulus ⊤ le_top
    F.S F.exclusions.prime η D.t D.t_pos] with Z hz
  intro d a ε tstar T allowance i B hcap bin label J K hne u hu θ
  apply hz label d u ?_ θ
  simp only [HeckeDetectorBatch.Batch.fiber, HeckeDetectorFiberPartition.toFiber,
    HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
  have hmem : u∈B.rows := hu.1
  exact hcap u hmem

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1840

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceInternal.lean; sha256: ceb3cb424caeb79f840031156695189f88ff1db3ab88b170caf07a33382b2e79 -/
section Source1841
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

lemma internalQ_coprime (Q P : Ideal O) (η₀ : Character)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η₀.modulus P) : IsCoprime (internalQ Q η₀) P :=
  (hQP.mul_left hηP).of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

lemma natural_nonzero_base {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O)
    (h : idealCoeff F.character I≠0) : idealCoeff η I≠0 := by
  rw [F.ideal] at h
  exact left_ne_zero_of_mul h

lemma coefficient_forcing_coprime (η₀ : Character) (e : O) (he : elementCoeff η₀ e≠0)
    (Q P : Ideal O) (hQP : IsCoprime Q P) (hPe : P∣Ideal.span {e}) :
    IsCoprime (internalQ Q η₀) P :=
  internalQ_coprime Q P η₀ hQP (CenteredMomentChildRows.old_coefficient_prime_coprime η₀ e he P hPe)

theorem energy_split (η η₀ : Character) (Q : Ideal O) (m A : O)
    (rows : Finset O) (f : O→ℂ) :
    (∑z∈rows,‖f z‖^2)=
      (∑z∈rows.filter (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2)+
      ∑z∈rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z)
      (fun z=>‖f z‖^2)).symm

theorem internal_exceptional_count (η η₀ : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (m A : O) (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀P∈normalizedFactors D,goodLambda∉P ∧ (2:O)∉P ∧
      IsCoprime Q P ∧ IsCoprime η₀.modulus P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P%6=2)
    (Z C M F : ℝ) (hZ : 0<Z) (hC : 0≤C)
    (hDnorm : Z^(F/2)≤(D.absNorm:ℝ))
    (hN : ∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤C*Z^M) :
    ((rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z)).card:ℝ)≤
      768*(6:ℝ)^(normalizedFactors (internalQ Q η₀)).toFinset.card*C^(1/6:ℝ)*Z^((M-2*F)/6) := by
  apply fixed_support_exceptional_count η (internalQ Q η₀) (internalQ_ne_zero Q hQ0 η₀)
    (internalQ_ne_top Q hQ η₀) (inf_le_left.trans hQ72) m A hm hA hmLam hm2
    (rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z))
    (fun z hz=>hrows z (Finset.mem_filter.mp hz).1)
    (fun z hz=>(Finset.mem_filter.mp hz).2) D hD ?_ Z C M F hZ hC hDnorm
    (fun z hz=>hN z (Finset.mem_filter.mp hz).1)
  intro P hP
  obtain ⟨hLam,h2,hQP,hη₀,hη,hv⟩:=hgood P hP
  exact ⟨hLam,h2,internalQ_coprime Q P η₀ hQP hη₀,hη,hv⟩

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem internal_sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 :=
  sector_nonprincipal M H hH F η₀ θ (internalQ Q η₀) R
    (inf_le_left.trans hQM) inf_le_right hR hz hex

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1841

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceSupport.lean; sha256: 72ae3a2f82c6ac5072e7e0529c3160df42f10f213ffbed66668abf7589214806 -/
section Source1842
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary HeckeDetectorRawFiber ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma oriented_moment_nonzero_base (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O, idealCoeff χ I=if reverse then
      conj (idealCoeff ((momentData η).character (momentElement u)) I)
      else idealCoeff ((momentData η).character (momentElement u)) I)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff η I≠0 := by
  intro he
  have hh:=hc I
  rw [momentData_product_raw,idealCoeff_product,he,zero_mul] at hh
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_zero] at hh
  · exact hI hh
  · exact hI hh

lemma fiber_nonzero_initial {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0) : idealCoeff η I≠0 := by
  apply oriented_moment_nonzero_base η (F.family u F.label) u F.reverse ?_ I hI
  simpa only [hdata,momentElement] using F.row_coeff u hu

lemma ideal_nonzero_forcing_coprime (η : Character) (I P : Ideal O)
    (hI : idealCoeff η I≠0) (hP : P∣I) : IsCoprime η.modulus P := by
  have hI0 : I≠0 := by intro h; apply hI; rw [h,map_zero]
  have he : elementCoeff η (idealGenerator I)≠0 := by
    rw [←idealCoeff_span η (idealGenerator_ne_zero I hI0),span_idealGenerator]
    exact hI
  exact CenteredMomentChildRows.old_coefficient_prime_coprime η (idealGenerator I) he P
    (by rwa [span_idealGenerator])

theorem fiber_internal_forcing {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I Q P : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0)
    (hP : P∣I) (hQP : IsCoprime Q P) : IsCoprime (internalQ Q η) P :=
  internalQ_coprime Q P η hQP
    (ideal_nonzero_forcing_coprime η I P (fiber_nonzero_initial F η hdata u hu I hI) hP)

theorem fiber_initial_support_filter {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (s : Finset (Ideal O)) (weight : Ideal O→ℂ) :
    (∑I∈s,idealCoeff (F.family u F.label) I*weight I)=
      ∑I∈s.filter (fun I=>idealCoeff η I≠0),idealCoeff (F.family u F.label) I*weight I := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hIs hnot
  have hzero : idealCoeff (F.family u F.label) I=0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hIs,fiber_nonzero_initial F η hdata u hu I hn⟩)
  rw [hzero,zero_mul]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1842

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceFixedIdeal.lean; sha256: 7814f20f7dae39272b939a7ea392bc6022abcc0757582560c77571a40c21ad22 -/
section Source1843
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1843

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceFreeExceptional.lean; sha256: 4dbb1822fa52e5743cd4a43d77baa773d9c299e554d13496f5a1c9d6d4318b35 -/
section Source1844
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceExceptionalBound (F : ProbeFinalAssembly.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

theorem eventually_source_sector_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u→ rowNorm u≤Z^(d-D.t) →
      ∀θ : RayQuotient.Characters F.modulus ⊤,
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      let χ:=(CenteredMomentNaturalRowSource.naturalRow η₀ u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top η₀ θ)
      χ.residue≠1 ∧ (χ.modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_no_exceptional F η,
    eventually_source_sector_capacity F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos]
    with Z hn hc
  intro label d u hlo hhi θ
  exact ⟨source_retained_sector_nonprincipal F _ u (hn label u hlo) θ,hc label d u hhi θ⟩

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1844

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourcePrimeGate.lean; sha256: 0daa7ed2ef4a8cf0f87966eebbe5c99cf6cdbe6e61948735110c75877515f836 -/
section Source1845
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRowMask CenteredMomentFixedRayInducingTransport
local notation "O" => HeckeFamily.O

def relativeBase (η : Character) (u : FreeRow) : Character :=
  (naturalRow η u.val u.property.1).character.product η.inverse

variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_relativeBase_twists (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : ¬sourceExceptional F η u) :
    ∀θ : RayQuotient.Characters F.modulus ⊤,
      (twistedFamily F.modulus ⊤ le_top (relativeBase η u) θ).residue≠1 := by
  have hn : ¬FixedInducingRow η (internalQ (sourceFixedIdeal F) η) fixedBadMask 1 u.val := by
    intro h
    apply hu
    exact (fixedInducingRow_mul_mask_iff η _ fixedBadMask (idealGenerator 1) 1 u.val
      fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero) one_ne_zero u.property.1
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h
  have hn' : ¬FixedInducingRow (η.product η.inverse) (internalQ (sourceFixedIdeal F) η)
      fixedBadMask 1 u.val :=
    (not_fixedInducingRow_product_iff η η.inverse _ fixedBadMask 1 u.val inf_le_right
      fixedBadMask_ne_zero one_ne_zero u.property.1 (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hn
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal F.modulus ⊤ le_top
    (η.product η.inverse) (relativeBase η u) (internalQ (sourceFixedIdeal F) η)
    fixedBadMask 1 u.val ?_ (inf_le_left.trans (sourceFixedIdeal_le_modulus F)) hn'
  exact product_row_presentation η (naturalRow η u.val u.property.1).character η.inverse
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η u.val u.property.1).element)

lemma relativeBase_modulus (M : Ideal O) [NeZero M] (η : Character) (u : FreeRow) :
    (relativeBase η u).modulus.absNorm≤sectorConductorFactor M η*(Ideal.span {u.val}).absNorm := by
  have hb:=(HeckePrimeScale.product_modulus_bound (naturalRow η u.val u.property.1).character η.inverse).trans
    (Nat.mul_le_mul_right η.modulus.absNorm (naturalRow η u.val u.property.1).natural_modulus_bound)
  have hM : 1≤M.absNorm := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  have hm : η.modulus.absNorm≤M.absNorm*η.modulus.absNorm := by nlinarith
  change (relativeBase η u).modulus.absNorm≤_
  apply hb.trans
  unfold sectorConductorFactor
  calc
    _=(η.modulus.absNorm*fixedConductorFactor*η.modulus.absNorm)*(Ideal.span {u.val}).absNorm := by ring
    _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem eventually_source_relativeBase_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u → rowNorm u≤Z^(d-D.t) →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^d ∧
        ∀θ : RayQuotient.Characters F.modulus ⊤,
          (twistedFamily F.modulus ⊤ le_top (relativeBase η₀ u) θ).residue≠1 := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)≤Z^D.t := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop D.t_pos).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_source_no_exceptional F η,eventually_gt_atTop (0:ℝ)] with Z hc hn hZ
  intro label d u hlo hhi
  refine ⟨?_,source_relativeBase_twists F _ u (hn label u hlo)⟩
  have hb : ((relativeBase (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u).modulus.absNorm:ℝ)≤
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)*rowNorm u := by
    change _≤_*((Ideal.span {u.val}).absNorm:ℝ)
    exact_mod_cast relativeBase_modulus F.modulus _ u
  apply hb.trans
  calc
    _≤Z^D.t*Z^(d-D.t) := mul_le_mul (hc label) hhi (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1845

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourcePrimeBound.lean; sha256: e78551a3707b9a0570397c4c6d4d9338a990d57aaaac539eca4ef46ebece70fd -/
section Source1846
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_physical_slot_bound (F : ProbeFinalAssembly.SourceData D)
    (loss lo hi κ : ℝ) (hloss : 0<loss) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d : ℝ,d≤1 →
      ∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u → rowNorm u≤Z^(d-D.t) →
      ∀P t : ℝ,1≤P → P≤Z → ∀z : ℂ,lo≤1-z.re → 1-z.re≤hi →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ‖normalizedSlot η₀ fixedBadMask 1 u.val (primePool F.modulus ⊤ 2 P)
        (physicalSlotCoefficient η₀ F.W P z) t P‖^2≤
        C*(1+|t|+|z.im|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    F.modulus ⊤ le_top F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    1 1 loss lo hi κ (by norm_num) (by norm_num) hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η
  filter_upwards [eventually_source_relativeBase_gate F η,eventually_ge_atTop Z₀,
    eventually_ge_atTop (1:ℝ)] with Z hgate hZ0 hZ
  intro label d hd u hlo hhi P t hP hPZ z hzlo hzhi
  let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  obtain ⟨hc,hn⟩:=hgate label d u hlo hhi
  have hc' : ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^(1:ℝ) :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hb:=hbound Z P hZ0 hP (by simpa only [Real.rpow_one] using hPZ)
    (relativeBase η₀ u) hc' hn (1-z.re) (t-z.im) hzlo hzhi
  have hconj : (fun y=>conj (F.W y))=(F.W:ℝ→ℂ) := by
    funext y
    rw [F.complex_eq]
    simp
  dsimp only
  rw [physicalSlot_eq_relativeRay F.modulus ⊤ η₀ (naturalRow η₀ u.val u.property.1).character
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η₀ u.val u.property.1).element)
    F.W 2 P t z (zero_lt_one.trans_le hP),hconj,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have habs : |t-z.im|≤|t|+|z.im| := by simpa using (abs_sub_le t 0 z.im)
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1846

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceNaturalPrime.lean; sha256: 042bee61a3aefbb0c7931dc36d11e692bec7a738df7e8d5e18b29c04831ffd3c -/
section Source1847
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma natural_relative_twists {η : Character} {z : O} (F : NaturalRow η z) (hz : z≠0)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) :
    ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue≠1 := by
  have hn : ¬FixedInducingRow (η.product η₀.inverse) (internalQ Q η₀) fixedBadMask 1 z :=
    (not_fixedInducingRow_product_iff η η₀.inverse _ fixedBadMask 1 z inf_le_right
      fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal M H hH
    (η.product η₀.inverse) (F.character.product η₀.inverse) (internalQ Q η₀)
    fixedBadMask 1 z ?_ (inf_le_left.trans hQM) hn
  exact product_row_presentation η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1847

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalFixedRaySourceRayPrime.lean; sha256: e48ee1d132df8f94e972e45e43521a3033e2b6bbbd5301a41fa1ea59a1f7ee9f -/
section Source1848
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end Source1848

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorSlots.lean; sha256: 58d5aec6a4f46360e4d2139835df8e87188c5483cc52b9fad93598a0f8be6314 -/
section Source1849
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel hbeta hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1849

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceAbsoluteEnvelope.lean; sha256: 28b2388af885005ec121e6aca833ef7f60e3ec8ef2c428c497aa47b77ea68aea -/
section Source1850
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceAbsoluteEnvelope
open HeckeFamily CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeHeight CenteredMomentPositiveSummability
open CenteredMomentAbsoluteEnergy QuadraticInitialBound ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_absolute (Q:Finset (Ideal O)) (c:Ideal O→ℂ) (η:Character) (t:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    sourceRestrictedEnergy keep Q c (heightCoeff η t) Φ K≤
      diagonalControl Φ*max 1 K*(∑I∈Q,‖c I‖)^2 := by
  let F:O→ℂ:=fun z=>rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>c I*heightCoeff η t I) z
  let B:ℝ:=∑I∈Q,‖c I‖
  have hB:0≤B:=Finset.sum_nonneg (fun I _=>norm_nonneg _)
  have hF (z:O):‖F z‖≤B:=by
    change ‖rowPolynomial Finset.univ (sourceGenerator Q) (fun I:supportedColumns Q=>c I*heightCoeff η t I) z‖≤∑I∈Q,‖c I‖
    rw [height_source_row η t Q c z]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg (c I)) (rowWeight_norm_le_one_all η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I)
  have hs:=bounded_radial_summable F B hF keep Φ K hK
  have hh:=hs.tsum_le_tsum (g:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left (B^2))
  rw [tsum_mul_left] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg B)).trans_eq (by ring)

end SevenEighths.CenteredMomentSourceAbsoluteEnvelope

end

end OAI

end Source1850

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSquarefreeBlock.lean; sha256: 894fc06b9d3c3d099b963ef8225682af651d413b40efef921ddb05615fbdcc41 -/
section Source1851
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSquarefreeBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

theorem actual_block_from_squarefree_source (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:Ideal O→ℝ,
      (∀L,0≤E₁ L) → (∀L,0≤E₂ L) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₁ L*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤E₂ L*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        B*∑L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨B,hB,hbound⟩:=CenteredMomentSecondRadicalBlock.actual_block_from_masked_source W decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η τ t S β C D hC hD hCD U A hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let coarse (G:Ideal O) (hg:G≠0) (L:Ideal O):ℝ:=
    QuadraticInitialBound.diagonalControl Φ*max 1 H*
      (∑I∈residualPool G hg S,‖if IsCoprime G I ∧ L∣I then β (G*I) else 0‖)^2
  have hcoarse (G:Ideal O) (hg:G≠0) (L:Ideal O):0≤coarse G hg L:=
    mul_nonneg (mul_nonneg (QuadraticInitialBound.diagonalControl_nonneg Φ) (by positivity)) (sq_nonneg _)
  let F₁:Ideal O→ℝ:=fun L=>if Squarefree L then E₁ L else coarse C hC.1 L
  let F₂:Ideal O→ℝ:=fun L=>if Squarefree L then E₂ L else coarse D hD.1 L
  have hF₁ (L:Ideal O):0≤F₁ L:=by dsimp [F₁];split_ifs;exact hE₁ L;exact hcoarse C hC.1 L
  have hF₂ (L:Ideal O):0≤F₂ L:=by dsimp [F₂];split_ifs;exact hE₂ L;exact hcoarse D hD.1 L
  have hsource (G:Ideal O) (hg:G≠0) (L:Ideal O) (χ:RayCharacter) (v:ℝ) (J:ℕ):
      sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool G hg S)
        (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0)
        (heightCoeff (τ χ) v) Φ H≤coarse G hg L*(1+‖v‖)^(2*J):=by
    have hh:=CenteredMomentSourceAbsoluteEnvelope.actual_source_absolute (residualPool G hg S)
      (fun I=>if IsCoprime G I ∧ L∣I then β (G*I) else 0) (τ χ) v
      (nonexceptional η χ Q m A) Φ H hH
    apply hh.trans
    exact le_mul_of_one_le_right (hcoarse G hg L) (one_le_pow₀ (by linarith [norm_nonneg v]))
  have hh:=hbound r hr η τ t S β C D hC hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor F₁ F₂ hF₁ hF₂
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₁,ite_eq_left hs] using hleft L hL hs χ v
      · simpa only [F₁,ite_eq_right hs] using hsource C hC.1 L χ v J₁)
    (by
      intro L hL χ v
      by_cases hs:Squarefree L
      · simpa only [F₂,ite_eq_left hs] using hright L hL hs χ v
      · simpa only [F₂,ite_eq_right hs] using hsource D hD.1 L χ v J₂)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro L hL
  by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
  · simp only [hμ,norm_zero,zero_mul]
  · have hs:=CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hμ
    simp only [F₁,F₂,ite_eq_left hs]

end SevenEighths.CenteredMomentSecondSquarefreeBlock

end

end OAI

end Source1851

/- Original source: OAI/NumberTheory/DirichletL/Moments/MobiusHarmonicMass.lean; sha256: 29f71b4cc9d0e5534ce0fb23c91d5d514b12d0b03b11f5b83d617a26f3bd8f9f -/
section Source1852
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentMobiusHarmonicMass
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentDivisorBoundary CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma shell_mass (Ds:Finset (Ideal O)) (n:ℤ) (hn:n∈selectedShells Ds) :
    (∑D∈shell Ds n,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤256 := by
  have ht:1≤dyadicScale n:=
    (selected_scale_bounds Ds (∑D∈Ds,(Ideal.absNorm D:ℝ))
      (fun D hD _=>Finset.single_le_sum (fun D _=>Nat.cast_nonneg _) hD) n hn).1
  have htp:0<dyadicScale n:=zero_lt_one.trans_le ht
  have hcard:=divisor_dyad_card (shell Ds n) (dyadicScale n) ht
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
  calc
    _≤∑D∈shell Ds n,1/dyadicScale n:=by
      apply Finset.sum_le_sum
      intro D hd
      have hh:=(shell_member_data Ds n D hd).2.2.2.2.1
      exact div_le_div₀ (by norm_num) (moebius_norm_le_one D) htp hh
    _=((shell Ds n).card:ℝ)/dyadicScale n:=by simp [div_eq_mul_inv]
    _≤256:=(div_le_iff₀ htp).mpr hcard

 theorem full_mass_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (Ideal.absNorm D:ℝ)≤Z^B) →
      (∑D∈Ds,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower B δ hB hδ
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Ds hn
  have he:=sum_norm_moebius_shells Ds (fun D=>1/(Ideal.absNorm D:ℝ))
  simp only [mul_one_div] at he
  rw [he]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ):=Finset.sum_le_sum (fun n hn=>shell_mass Ds n hn)
    _=((selectedShells Ds).card:ℝ)*256:=by simp
    _≤(C*Z^δ)*256:=mul_le_mul_of_nonneg_right (hZ.2 Ds hn) (by norm_num)
    _=_:=by ring

 theorem actual_divisorPool_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤Z^B) →
      (∑D∈divisorPool T v,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn
  exact hZ.2 (divisorPool T v) (fun D hd _=>(divisorPool_nonzero_norm T v hv (Z^B) hn D hd).2)

end SevenEighths.CenteredMomentMobiusHarmonicMass

end

end OAI

end Source1852

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondHarmonicBudget.lean; sha256: b320ac4e6038e5d0ef281cf3e65dbf1715dc4ab5c11dafd4ded06351c6ad2044 -/
section Source1853
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentSecondHarmonicBudget
open CenteredMomentSecondWindowBudget CenteredMomentMobiusHarmonicMass
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma paired_divisor (J₁ J₂:ℕ) (t E₁ E₂ n:ℝ) (hn:0≤n) :
    windowBudget J₁ t (E₁/n)*windowBudget J₂ t (E₂/n)=
      (windowBudget J₁ t E₁*windowBudget J₂ t E₂)/n := by
  simp only [windowBudget,Real.sqrt_div' _ hn]
  calc
    _=(Real.sqrt E₁*heightEnvelope t^J₁*profileMoment J₁*
        (Real.sqrt E₂*heightEnvelope t^J₂*profileMoment J₂))/
          (Real.sqrt n*Real.sqrt n):=by ring
    _=_:=by rw [Real.mul_self_sqrt hn]

 theorem actual_divisor_budget (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤Z^B) →
      ∀J₁ J₂:ℕ,∀t E₁ E₂:ℝ,
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
        (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*
          windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))≤
      C*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨C,hC,hbound⟩:=actual_divisorPool_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn J₁ J₂ t E₁ E₂
  have he:(∑L∈divisorPool T v,‖(moebius L:ℂ)‖*
      (windowBudget J₁ t (E₁/(Ideal.absNorm L:ℝ))*windowBudget J₂ t (E₂/(Ideal.absNorm L:ℝ))))=
      (∑L∈divisorPool T v,‖(moebius L:ℂ)‖/(Ideal.absNorm L:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂):=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro L hL
    rw [paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (hZ.2 T v hv hn)
    (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))

end SevenEighths.CenteredMomentSecondHarmonicBudget

end

end OAI

end Source1853

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSummedBlock.lean; sha256: 1abaee4993e1a802daf8ff57b2855aae4b0e984da5f4d77f3afba097e607b025 -/
section Source1854
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSummedBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
theorem actual_block_from_divisor_envelopes (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
        (C D:Ideal O) (hC:Supported C) (hD:Supported D),
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),0<H →
      (∀z:O,0≤(Φ (normValue z/H)).re) → (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool C hC.1 S)
          (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₁/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L → ∀χ:RayCharacter,∀v:ℝ,
        sourceRestrictedEnergy (nonexceptional η χ Q m A) (residualPool D hD.1 S)
          (fun I=>if IsCoprime D I ∧ L∣I then β (D*I) else 0)
          (heightCoeff (τ χ) v) Φ H≤(E₂/(Ideal.absNorm L:ℝ))*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨K,hK,hkernel⟩:=CenteredMomentSecondSquarefreeBlock.actual_block_from_squarefree_source W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=CenteredMomentSecondHarmonicBudget.actual_divisor_budget B δ hB hδ
  refine ⟨max 1 K*Cm,mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t S β C D hC0 hD hCD U A hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hk:=hkernel r hr η τ t S β C D hC0 hD hCD U hτ R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor
    (fun L=>E₁/(Ideal.absNorm L:ℝ)) (fun L=>E₂/(Ideal.absNorm L:ℝ))
    (fun L=>div_nonneg hE₁ (Nat.cast_nonneg _)) (fun L=>div_nonneg hE₂ (Nat.cast_nonneg _))
    hleft hright
  have hs:=hZ.2 Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O))
    (fun J _=>(sectorPool_supported D hD.1 S J).1) (fun J _=>hn J) J₁ J₂ t E₁ E₂
  apply hk.trans
  calc
    _≤K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=mul_le_mul_of_nonneg_left hs hK
    _≤max 1 K*(Cm*Z^δ*(windowBudget J₁ t E₁*windowBudget J₂ t E₂)):=
      mul_le_mul_of_nonneg_right (le_max_right _ _)
        (mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
          (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    _=_:=by ring

end SevenEighths.CenteredMomentSecondSummedBlock

end

end OAI

end Source1854

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondOriginalChildren.lean; sha256: d3c865eca71de39746d2af5330b330e3e1623ae312efdd03a63f246e4bd21d90 -/
section Source1855
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

def sourceRadial (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) (hH:0<H)
    (hΦ:∀z:O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=>by simpa only [normValue_eq_embedding] using hΦ z⟩

theorem actual_block_from_original_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀r:ℝ,0<r →
      ∀(η:Character) (τ:RayCharacter→Character) (t:ℝ) (s:Input ι),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀J:sectorPool D hD.1 S,(Ideal.absNorm (J:Ideal O):ℝ)≤Z^B) →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        C0*Z^δ*(windowBudget J₁ t (core s C Ce Z δ E₁)*windowBudget J₂ t (core s D Ce Z δ E₂)) := by
  obtain ⟨Ce,hCe,hsource⟩:=actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=CenteredMomentSecondSummedBlock.actual_block_from_divisor_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤E):0≤core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=>hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=
      (CenteredMomentWholeDivisorShell.divisorPool_nonzero_norm Finset.univ
        (fun J:sectorPool D hD.1 S=>(J:Ideal O))
        (fun J _=>(sectorPool_supported D hD.1 S J).1) (Z^B) (fun J _=>hn J) L hL).2
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end SevenEighths.CenteredMomentSecondOriginalChildren

end

end OAI

end Source1855

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedNaturalRadial.lean; sha256: b99f7a8df26edbad89d60815c2ef50cfc7103e9d12b6c345750795a140f1c793 -/
section Source1856
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic ConcreteTraceCRT MeasureTheory
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskRadialEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O

lemma profile_support (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) :
    Function.support (V.profile U hU t : ℝ→ℂ)⊆Set.Icc (V.a/max 1 V.b) (max 1 V.b) := by
  by_cases h : 1≤U*V.b
  · rw [V.profile_retained U hU t h]
    exact (retainedProfile_support V.W V.a V.b V.a_pos V.support V.smooth U hU h t).trans
      (fun _ hx=>⟨hx.1,hx.2.trans (le_max_right _ _)⟩)
  · rw [V.profile_zero U hU t (lt_of_not_ge h)]
    simp

def naturalCharacter (η : Character) (z : O) : Character :=
  if h : z≠0 then (naturalRow η z h).character else η

lemma naturalCharacter_eq (η : Character) (z : O) (hz : z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by simp [naturalCharacter,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,∀F : Finset T,
      Shared F (fun i=>b i) (fun i=>M i) C ε := by
  have he (T : Finset α) (F : Finset T) : ∃C : ℝ,0<C ∧ Shared F (fun i=>b i) (fun i=>M i) C ε :=
    actual_radial_shared_energy F (fun i=>b i) (fun i=>M i) (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,∑F : Finset T,C T F
  have hp (T : Finset α) : 0≤∑F : Finset T,C T F:=Finset.sum_nonneg (fun F _=>(hC T F).le)
  refine ⟨B,by have hh : 0≤∑T : Finset α,∑F : Finset T,C T F:=Finset.sum_nonneg (fun T _=>hp T);dsimp [B];linarith,?_⟩
  intro T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild
  have hCB : C T F≤B := by
    have h₁:=Finset.single_le_sum (fun G _=>(hC T G).le) (Finset.mem_univ F)
    have h₂:=Finset.single_le_sum (fun T _=>hp T) (Finset.mem_univ T)
    dsimp [B];linarith
  exact (hb T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

def commonChild (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma common_rawScale (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    rawScale L a (commonData (withHeight s τ v) C R B).X₁ 0=
      s.X₁/(Ideal.absNorm (B.val (Sum.inr 0)*CenteredMomentDivisorRectangle.selectedPlain L a 0):ℝ) := by
  simp only [rawScale,commonData,withHeight,map_mul,Nat.cast_mul,div_div]

theorem common_allocated_normalized (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (hRC : R*C≠0) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (hV₁ : V₁.W=s.W₁) (hV₂ : V₂.W=s.W₂) (z : O) (hz : z≠0) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a d.W₁ d.W₂ d.X₁ d.X₂=
      (((clippedScale (rawScale L a d.X₁ 0)):ℂ)^(Complex.I*v)*
       ((clippedScale (rawScale L a d.X₂ 1)):ℂ)^(Complex.I*v))*
       (polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₁.profile _ (rawScale_pos L a d.X₁ d.X₁_pos 0) v) (clippedScale (rawScale L a d.X₁ 0)) 0 0*
        polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₂.profile _ (rawScale_pos L a d.X₂ d.X₂_pos 1) v) (clippedScale (rawScale L a d.X₂ 1)) 0 0*
        ∏i∈liveIndices L a,naturalSlot (excluded (naturalCharacter τ z) (R*C))
          (d.slots i) (heightCoefficient (d.coefficient i) v) (d.P i)) := by
  dsimp only
  rw [naturalCharacter_eq τ z hz]
  have hh:=allocated_normalized τ z hz (R*C) hRC L a V₁ V₂
    (commonData (withHeight s τ v) C R B).slots
    (commonData (withHeight s τ v) C R B).coefficient
    (commonData (withHeight s τ v) C R B).P
    (commonData (withHeight s τ v) C R B).P_pos v
    (commonData (withHeight s τ v) C R B).X₁ (commonData (withHeight s τ v) C R B).X₂
    (commonData (withHeight s τ v) C R B).X₁_pos (commonData (withHeight s τ v) C R B).X₂_pos
  simpa only [hV₁,hV₂,commonData,withHeight] using hh

theorem allocated_radial_bound (b M : α→ℝ) (C₀ ε : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (hb : Shared (liveIndices D a) b M C₀ ε)
    (η : Character) (R : Ideal O) (hR : R≠0) (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hprime : ∀i,∀I∈pool i,Prime I) (hP : ∀i,0<P i)
    (hβ : ∀i,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (r : Radial) (hkeep : ∀z,r.keep z → z≠0) (E : ℝ) (hE : 0≤E)
    (hchild : ∀D₁∈(CompletedGauss.primeSupport R).powerset,
      ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
      radialEnergy (fun z=>child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂
        hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale≤E) :
    radialEnergy (fun z=>allocatedPositiveRow η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂) r.keep r.profile r.scale≤
        C₀*(Ideal.absNorm R.radical:ℝ)^ε*E := by
  have hh:=hb (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₁ 0)) (clippedScale (rawScale D a X₂ 1))
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    pool (fun i=>heightCoefficient (β i) t) P r.keep r.profile r.scale E
    (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)
    (by positivity) (by positivity) (profile_support V₁ _ _ t) (profile_support V₂ _ _ t)
    (fun i _=>hprime i) (fun i _=>hP i)
    (fun i _ I hi=>by rw [heightCoefficient_norm _ _ _ (hprime i I hi).ne_zero];exact hβ i I hi)
    (fun i _ I hi hn=>hs i I hi (left_ne_zero_of_mul hn)) r.scale_pos r.nonneg hE hchild
  rw [←primeSupport_product_radical R hR]
  convert hh using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · dsimp only
    rw [allocated_normalized η z (hkeep z hz) R hR D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂,
      naturalCharacter_eq η z (hkeep z hz)]
    have hphase (U : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
      positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
    simp only [excluded,norm_mul,hphase,one_mul]
  · rfl

theorem natural_child_summable (η : Character) (R : Ideal O)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆CompletedGauss.primeSupport R)
    (hD₂ : D₂⊆CompletedGauss.primeSupport R) (J : Finset α) (r : Radial) :
    Summable (fun z=>if r.keep z then
      ‖child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J‖^2*
        (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) := by
  have hn (S : Finset (Ideal O)) (hS : S⊆CompletedGauss.primeSupport R) :
      (0:ℝ)<Ideal.absNorm (∏I∈S,I) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hI=>(support_prime R I (hS hI)).ne_zero)))
  obtain ⟨PB,hPB,hbound⟩:=slots_bounded (liveIndices D a\J) pool (fun i=>heightCoefficient (β i) t) P
  exact pair_radial_summable (naturalCharacter η)
    (fun z=>∏i∈liveIndices D a\J,naturalSlot (naturalCharacter η z) (pool i) (heightCoefficient (β i) t) (P i))
    (fun _=>0) (fun _=>0)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
    (by positivity) (by positivity) (div_pos (by unfold clippedScale;positivity) (hn D₁ hD₁))
    (div_pos (by unfold clippedScale;positivity) (hn D₂ hD₂))
    (profile_support V₁ _ _ t) (profile_support V₂ _ _ t) (fun z=>hbound (naturalCharacter η z))
    r.keep r.profile r.scale r.scale_pos

omit [DecidableEq α] in
lemma common_nonzero (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←(Finset.mem_filter.mp B.property).2]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

lemma child_energy_eq_radial (s : Data α) (r : Radial) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r D a=
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.X₁ s.X₂) r.keep r.profile r.scale+
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.Y₁ s.Y₂) r.keep r.profile r.scale := by
  have hx:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  have hy:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  unfold childEnergy radialEnergy
  rw [←hx.tsum_add hy]
  apply tsum_congr
  intro z
  unfold Radial.weight
  split_ifs <;> ring

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

theorem actual_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ CommonBound b M C₀ ε := by
  obtain ⟨C₀,hC₀,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  let d:=commonData (withHeight s τ v) C R B
  have hRC : R*C≠0:=mul_ne_zero hR (common_nonzero s C B)
  have hb:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (liveIndices L a)
  have hc:= (commonSlots s C B).controls
  have hβ : ∀i,∀I∈d.slots i,‖d.coefficient i I‖≤M i := by
    intro i I _
    exact (hc.1 i I).trans (hMs i)
  have hs : ∀i,∀I∈d.slots i,d.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*d.P i := by
    intro i I _ hn
    exact (hc.2 i I hn).trans (mul_le_mul_of_nonneg_right (hhi i) (s.P_pos i).le)
  have hl:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.X₁ d.X₂ d.X₁_pos d.X₂_pos r hkeep E₁ hE₁ hleft
  have hr:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos r hkeep E₂ hE₂ hright
  rw [child_energy_eq_radial]
  have hh:=add_le_add hl hr
  rw [←mul_add] at hh
  simpa only [d,commonData,withHeight,hV₁,hV₂] using hh

lemma nonexceptional_nonzero (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A z : O)
    (hz : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A z) : z≠0 := hz.1

theorem uniform_initial_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀T : Finset α,CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε := by
  have he (T : Finset α) : ∃C₀ : ℝ,0<C₀ ∧ CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε :=
    actual_common_radial_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let C₀ : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨C₀,by dsimp [C₀];linarith,?_⟩
  intro T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  have hCB : C T≤C₀ := by
    have hh:=Finset.single_le_sum (fun T _=>(hC T).le) (Finset.mem_univ T)
    dsimp [C₀];linarith
  exact (hb T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (add_nonneg hE₁ hE₂))

lemma common_raw_same_product (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let d:=commonData (withHeight s τ v) C R B
    rawScale L a d.X₁ 0*rawScale L a d.X₂ 1=rawScale L a d.Y₁ 0*rawScale L a d.Y₂ 1 :=
  raw_same_product L a _ _ _ _ (commonData (withHeight s τ v) C R B).same_product.symm

theorem original_nonexceptional_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀(η : Character) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m A : O)
      (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
      (hΦ : ∀z : O,0≤(Φ (CenteredMomentSectorLocalization.normValue z/H)).re),
    let r:=CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A) Φ H hH hΦ

    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C₀,hC₀,hb⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ η χ Q m A Φ H hH hΦ r
    E₁ E₂ hE₁ hE₂ hleft hright
  exact hb s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r
    (fun _ hz=>hz.1) E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentAllocatedNaturalRadial

end

end OAI

end Source1856

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorNatural.lean; sha256: 3052492c63a843f8495c3ab12572dcc689c86e7f29c8c8033968723c34491d50 -/
section Source1857
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ),Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,Cs,hCs,hslot⟩ := natural_slot_product M H hH F W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨S,Cp,hCp,hplain⟩ := global_positive_scale a₀ b₀ ha₀
  refine ⟨J,S,Cp^4*3^8*Cs,by positivity,?_⟩
  intro η₀
  filter_upwards [hslot η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ A hAF
  let E := Cs*(1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hE : 0≤E := by dsimp [E]; positivity
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0≤B₁ := apply_nonneg _ _
  have hB₂ : 0≤B₂ := apply_nonneg _ _
  let B := Cp^2*(B₁*B₂)*Qbound^2*3^4*Real.sqrt E
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (z : O) (hkeep : r.keep z) :
      ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖≤B := by
    have hn := hz z hkeep
    have heq := naturalCharacter_eq η z hn
    have hnon : (naturalCharacter η z).residue≠1 := by
      rw [heq]
      exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η
        (naturalRow η z hn).character (internalQ Q η₀) fixedBadMask 1 z
        (by simpa only [one_mul] using (naturalRow η z hn).element) (hex z hkeep)
    have h₁ : ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0‖≤Cp*B₁*Qbound*3^2 := by
      have he := hplain W₁ hs₁ _ hnon X₁ 0 hX₁
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₁)) (show (0:ℝ)≤9 by norm_num))
    have h₂ : ‖polynomial (naturalCharacter η z) false W₂ X₂ 0 0‖≤Cp*B₂*Qbound*3^2 := by
      have he := hplain W₂ hs₂ _ hnon X₂ 0 hX₂
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₂)) (show (0:ℝ)≤9 by norm_num))
    have hs := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η z hn (naturalRow η z hn)
      (by simpa only [heq] using hmod z hkeep) Q hQM (hex z hkeep) A hAF
    rw [←heq] at hs
    have hsroot := (Real.le_sqrt (norm_nonneg _) hE).mpr hs
    rw [norm_mul,norm_mul]
    apply (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
      hsroot (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B,B₁,B₂]
    norm_num only [abs_zero,add_zero]
    ring
  have he := radial_bound_on_keep _ r B hB hpoint
  apply he.trans_eq
  dsimp [B,E,B₁,B₂]
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hE]
  ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1857

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorCoefficients.lean; sha256: de7c2ac7511c1a50f24d0b253deef640784a05eb5ad453057ef04276af713617 -/
section Source1858
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

 theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0<B ∧ ∀(ν : Character)(P σ v t : ℝ),0<P → lo≤σ → σ≤hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I‖≤B ∧
      (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1858

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorShared.lean; sha256: b1e89fd7b41c636c99b1fd83a1546fddb81092be65b77666dfe20483ba8ded90 -/
section Source1859
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem masked_natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0*
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0*
        ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) ε hε
  refine ⟨J,S,Cd*C,mul_pos hCd hC,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hp (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) : Prime I :=
    (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i hi) (hσhi i hi) I (hp i hi I hI).ne_zero
  have he := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    W₁ W₂ X₁ X₂ a₀ b₀ a₀ b₀ (fun i=>primePool M H b (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    (fun i=>Z^(w i)) r.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ hs₁ hs₂ hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE ?_
  · rw [primeSupport_product_radical R hR] at he
    exact he.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ A hA
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    exact hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
      W₁ W₂ hs₁ hs₂ _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
      (F\A) Finset.sdiff_subset

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1859

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorSource.lean; sha256: d7b505fbb626c2bc1ad81892b580693d31d02a6decdfa8b6f7a1d90bb5e5a90e -/
section Source1860
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem original_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := masked_natural_pair_slots M H hH (Finset.univ : Finset α)
    W a b ha hWs hW a₀ b₀ ε ha₀ hb₀ hε Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨n,T₀,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a₀ b₀ ha₀ S
  refine ⟨4*n+J,T₀,C*Ct^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hexbase (z : O) (hk : r.keep z) :
      ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z := by
    intro hh
    apply hex z hk
    exact (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η (internalQ Q η₀)
      fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero (hz z hk)
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh
  let V₁ := CenteredMomentLattice.normPowerProfile W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t
  let V₂ := CenteredMomentLattice.normPowerProfile W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hZ θ w σ v t T (fun i _=>hw i) (fun i _=>hwL i)
    (fun i _=>hσlo i) (fun i _=>hσhi i) hT (fun i _=>hv i)
    η Q r Qbound R hR hQM hQbound hz hexbase hmod hQ V₁ V₂ hv₁ hv₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale =
    radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false V₁ X₁ 0 0*
      polynomial (excluded (naturalCharacter η z) R) false V₂ X₂ 0 0*
      ∏i,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
      r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · simp only [hk,ite_true]
      rw [original_positive_normalized (naturalRow η z (hz z hk)) R hR W₁ W₂
        a₀ b₀ a₀ b₀ ha₀ ha₀ hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
        _ _ _ (fun i=>Real.rpow_pos_of_pos hZ0 _) t X₁ X₂ hX₁ hX₂]
      rw [norm_mul,norm_mul,positive_height_phase_norm X₁ t hX₁,
        positive_height_phase_norm X₂ t hX₂,one_mul,one_mul,naturalCharacter_eq η z (hz z hk)]
    · simp only [hk,ite_false]
  rw [hid]
  apply he.trans
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ *
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    have hheight : (1+‖t‖)^(4*n)≤(1+|t|+T)^(4*n) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Real.norm_eq_abs]
      linarith
    calc
      _ ≤ (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(1+‖t‖)^n*
        (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)*(1+‖t‖)^n))^2 := hh
      _ = (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
          rw [Nat.mul_comm 4 n,pow_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)
  have hd := diagonalControl_nonneg r.profile
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
      ((Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n))*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i,w i)) := by gcongr
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1860

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloor.lean; sha256: 69eab25845a0e57d2bb465b616def835953a1fecb61249a6f83ab6e52e29cfc7 -/
section Source1861
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (L Lslot loss lo hi κ bΦ : ℝ) (hL : 0≤L) (hbΦ : 0≤bΦ) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(R : Ideal O),R≠0 → Q≤M →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
    ∀(m q ρ : ℝ),0≤m → 0≤q → m+q≤ρ → ρ≤L → r.scale=Z^m →
      (η.modulus.absNorm:ℝ)≤Z^q →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
         (1+|t|+T)^degree*Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := original_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ ε ha₀ hb₀ hε (L+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨J,S,C*Fc^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ),eventually_ge_atTop (1:ℝ)] with Z hZ hconst hZ1
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r R hR hQM hz hex hsΦ
    m q ρ hm hq hρ hρL hscale hη W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  have hmod (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Fc*bΦ*Z^ρ := by
    have hn := hz z hk.1
    rw [naturalCharacter_eq η z hn]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ hk.2)
    have he := (naturalRow η z hn).modulus_power_bound Z q m bΦ hZ0 hbΦ hη hrow
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hFc.le hbΦ)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hcap (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    apply (hmod z hk).trans
    calc
      _ ≤ Z*Z^L := mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hρL)
        (Real.rpow_nonneg hZ0.le _) hZ0.le
      _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_one]; ring
  have he := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r'
    (Fc*bΦ*Z^ρ) R hR hQM (by positivity) (fun z hk=>hz z hk.1)
    (fun z hk=>hex z hk.1) hcap hmod W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r'.keep r'.profile r'.scale =
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [hid] at he
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ1 hm)] at he
  rw [hscale]
  apply he.trans_eq
  have hzpow : Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))=Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    norm_num
    ring
  calc
    _ = (C*Fc^4*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
      (1+|t|+T)^J)*(Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))) := by ring
    _ = _ := by rw [hzpow]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1861

/- Original source: OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorState.lean; sha256: d92e43317ba957bfacda742d91ce8447be88e3245535ee5ad3a8a00ffa539927 -/
section Source1862
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity) hbeta hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤_
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI

end Source1862

/- Original source: OAI/NumberTheory/DirichletL/Energy/Bands.lean; sha256: a61844ac79dfb06cdbce70a09bdc62671b15ad25ded96a3069fc657909e20324 -/
section Source1863
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def length (Z X:ℝ):ℝ:=Real.logb Z (max 1 X)

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

def ZeroAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

lemma zeroAt_of_zeroBound (Q:Ideal O)(a b bΦ Bmask L M ε Z Z₀:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:ZeroBound Q a b bΦ Bmask M ε degree S C Z₀)(hZ:Z₀≤Z):
    ZeroAt Q a b bΦ Bmask L M ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ _ _
  exact h Z hZ s hQ hs p t X₁ X₂ hX₁ hX₂

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem exists_positive_bottom (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε)(hLs:0≤Lslot)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
          (ε/16) ε κ Z η₀ Q degree S C:=by
  have hs (T:Finset α):=CenteredMomentRayMaskedFloor.exists_positive_floor (α:=T)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask ε Lslot lo hi κ
    ha hb hbΦ hmask hε hLs hbeta hκ
  choose J S C hC hbound using hs
  let S₀:Finset (ℕ×ℕ):=Finset.univ.biUnion S
  let C₀:ℝ:=1+∑T:Finset α,C T
  have hC₀:0<C₀:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
    dsimp [C₀];linarith
  refine ⟨∑T:Finset α,J T,S₀,C₀,hC₀,?_⟩
  intro η₀
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr (fun T=>hbound T η₀)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hslots:6*κ*(∑i,w i)≤s.width:=by
    linarith [length_nonneg Z X₁ hZ1,length_nonneg Z X₂ hZ1]
  have hh:=hZ T θ w σ v t height hw hwL hσlo hσhi hheight hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hsub:S T⊆S₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hpc:p.control (S T)≤p.control S₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hc:C T≤C₀:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
      (Finset.mem_univ T)
    dsimp [C₀];linarith
  have hj:J T≤∑T:Finset α,J T:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hpow:(1+|t|+height)^(J T)≤(1+|t|+height)^(∑T:Finset α,J T):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=p.control_nonneg S₀
  have hpt:=p.control_nonneg (S T)
  apply hh.trans
  gcongr
end SevenEighths.CenteredMomentEnergyBands

end

end OAI

end Source1863

/- Original source: OAI/NumberTheory/DirichletL/Energy/InputParentCapacity.lean; sha256: 8bd3b0868304b7b35f1eb9779dd0ce9c899585b0e5ca62acaea6aca632c33b85 -/
section Source1864
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X) := by
  by_cases hx:1≤X
  · rw [length,max_eq_right hx,max_eq_right (Real.logb_nonneg hZ hx)]
  · have hh:X≤1:=le_of_not_ge hx
    have hl:Real.logb Z X≤0 := by
      simpa using Real.logb_le_logb_of_le hZ hX hh
    rw [length,max_eq_left hh,Real.logb_one,max_eq_left hl]

theorem postmask_length (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)=length Z X-min (Real.logb Z D) (length Z X) := by
  have hp:0<max 1 X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd:0<D:=zero_lt_one.trans_le hD
  rw [length_eq_max_log Z _ hZ (div_pos hp hd),Real.logb_div hp.ne' hd.ne']
  change max 0 (length Z X-Real.logb Z D)=_
  by_cases h:Real.logb Z D≤length Z X
  · rw [min_eq_left h,max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),sub_self]

lemma postmask_length_le (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)≤length Z X := by
  rw [postmask_length Z X D hZ hD]
  have hm:0≤min (Real.logb Z D) (length Z X):=
    le_min (Real.logb_nonneg hZ hD) (length_nonneg Z X hZ)
  linarith

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem input_reference_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (s.Y₁*s.Y₂*∏i,s.P i)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [s.same_product]
  exact input_affine_capacity s Z κ M hZ hcap

theorem original_slot_logs (s:Input ι)(Z:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hw:∀i,0≤w i)(hP:∀i,s.P i=Z^(w i)):
    (∀i,1≤s.P i) ∧ (∀i,Real.logb Z (s.P i)=w i) := by
  constructor
  · intro i;rw [hP i];exact Real.one_le_rpow hZ.le (hw i)
  · intro i;rw [hP i,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem original_exponent_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hP:∀i,s.P i=Z^(w i))
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,w i)≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  apply input_affine_capacity s Z κ M hZ
  simpa only [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI

end Source1864

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedCapacitySource.lean; sha256: f6a029a6917d90762b176e121dd8d8ec6d72f32b0ee89889ba6548e1af82c454 -/
section Source1865
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem frozen_reduction_log (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)
    (Z:ℝ)(hZ:1<Z)(hne:frozenCoefficient B.val C R s.ν s.W s.P≠0):
    Real.logb Z (rawReduction B.val s.P)-Real.logb Z (C.absNorm:ℝ)≤
      -(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha:0<min 1 s.lower:=lt_min zero_lt_one s.lower_pos
  have hh:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower s.upper s.lower_pos s.slot_support hne).1
  have hl:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hh
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow] at hl
  nlinarith

theorem inherited_affine_parent (s:Input ι)(C _R:Ideal O)(B:actualAllocations s.pools C)
    (Z κ M:ℝ)(hZ:1<Z)(hκ:1/6≤κ)(hP:∀i,1≤s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤M := by
  have hp:=CenteredMomentEnergyInputParentCapacity.input_affine_capacity s Z κ M hZ hcap
  have hs:=CenteredMomentAllocatedChildCapacity.common_slot_logs_le s C B Z hZ hP
  have hh:=mul_le_mul_of_nonneg_left hs (by linarith:0≤6*κ-1)
  linarith

theorem actual_main_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (child s C R0 B τ t)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ t S β C₂ D₂ hC₂ hD₂ U R rows W
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) n≠0):
    Real.logb Z (volume (child s C R0 B τ t)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        2*sigma+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by
    unfold mainCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ t S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (child s C R0 B τ t)) a Z (cost*(τ.modulus.absNorm:ℝ)) n
    (mul_pos hcost hq) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_main_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hmod
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  rw [common_volume] at hg
  rw [Real.logb_mul hcost.ne' hq.ne'] at hg
  dsimp only at hr
  rw [common_volume]
  linarith

theorem actual_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(child s C R0 B τ t).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (child s C R0 B τ t).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (twiceChild s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=twice_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedCapacitySource

end

end OAI

end Source1865

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstChildLower.lean; sha256: 90227d0e3bf00fb500fcf3e470b5feb4bfa3a5f27a44935243003cb631b0b21a -/
section Source1866
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

theorem twice_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s C R B τ t).pools (Q^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=twiceChild s C R B τ t Q k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hp:=child_lower (child s C R B τ t) (Q^k) (R*C) (pow_ne_zero k hQ)
    Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hnorm:(Q.absNorm:ℝ)>0:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have he:Real.logb Z ((Q^k).absNorm:ℝ)=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ):=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
  simpa only [he,twiceChild] using hp

theorem removed_width_cap (L c w:ℝ):
    (2/3:ℝ)*(c+w)+(2/3:ℝ)*max (L-c-w) 0≥(2/3:ℝ)*L:=by
  have h:=le_max_left (L-c-w) 0
  linarith

theorem paired_removed_width_cap (L c₁ w₁ c₂ w₂:ℝ):
    ((c₁+w₁)+(c₂+w₂))/3+
      (max (L-c₁-w₁) 0+max (L-c₂-w₂) 0)/3≥(2/3:ℝ)*L:=by
  have h₁:=le_max_left (L-c₁-w₁) 0
  have h₂:=le_max_left (L-c₂-w₂) 0
  linarith

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI

end Source1866

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondInputGates.lean; sha256: 2fcbc7b8aa9904099aa04b89cc26e5729db519a4fb062690c3d84e5f9dd960c0 -/
section Source1867
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def exponent (A D P q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (A+P+ε) q))

structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0<K
  volume_cap : volume s≤Z^B
  source_nonneg : 0≤sourceRadius s
  source_cap : sourceRadius s≤Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤Z^B
  puncture_cap : (R.absNorm:ℝ)≤Z^B
  nominal_pos : 0<nominal s K
  nominal_cap : nominal s K≤Z^B
  frequency_pos : 0<frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤Z^B

theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal O)
    (hz:∀I:Ideal O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

theorem eventually_twice_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)→
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D P q ξ:ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0)→
    Ready (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ (exponent A D P q ε ξ):=by
  filter_upwards [eventual_twice_caps N b b₁ b₂ ε hb hb₁ hb₂ hε,
    eventual_live_puncture N b b₁ b₂ ε hb hb₁ hb₂ hε] with Z hc hp
  refine ⟨hc.1,?_⟩
  intro ι _ s hs he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hV hKi hRN hυ hlive
  have hh:=hc.2 s hs he C R B τ t hB Q hQ k hslot Bp υ v K A D ξ hK hV hKi
  have hr:=hp.2 s hs he C R seed B τ t hB Q hQ k hslot Bp υ v A P hz₁ hz₂ hV hRN hlive
  have h₁:A+ε≤exponent A D P q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:A+P+ε≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤exponent A D P q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hc.1.le h
  refine ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hh.1.trans (hpow h₁),hh.2.1,hh.2.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hr.trans (hpow h₃),hh.2.2.2.1,
    hh.2.2.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI

end Source1867

/- Original source: OAI/NumberTheory/DirichletL/Dictionary/InverseUniformScale.lean; sha256: 098fc23b098230b54672519ea49eaceb98c4ddd3460c9f33ccfacf1672faa868 -/
section Source1868
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification

def scaleCLM : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (-1/2:ℝ) • ContinuousLinearMap.id ℝ (𝓢(ℝ,ℂ))-
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ=>x)).comp (SchwartzMap.derivCLM ℝ ℂ)

lemma scaleCLM_apply (W : 𝓢(ℝ,ℂ)) (x : ℝ) : scaleCLM W x=scaleProfile W x := by
  simp only [scaleCLM,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    SchwartzMap.derivCLM_apply,Complex.real_smul,scaleProfile]
  push_cast
  ring

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI

end Source1868

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalStability.lean; sha256: f5750202f0b4cc1ddd15abe8c863e2bf6c6c7f4a78cc41a5df9863d939f06c21 -/
section Source1869
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedProfile CenteredMomentAllocatedNaturalSource
open EisensteinSchwartzPoisson CenteredMomentLattice

def sourcePlain (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) : Plain :=
  ⟨W,a,b,ha,hs,W.smooth ⊤⟩

theorem sourcePlain_support (a b:ℝ) (ha:0<a) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (U:ℝ) (hU:0<U) (t:ℝ) :
    Function.support ((sourcePlain a b ha W hs).profile U hU t:ℝ→ℂ)⊆
      Set.Icc (a/max 1 b) b := by
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    exact retainedProfile_support W a b ha hs (W.smooth ⊤) U hU hret t
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simp

theorem plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S ((sourcePlain a b ha W hs).profile U hU t)≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨n,T,C,hC,hsource⟩ := normPowerProfile_source_control a b ha S
  refine ⟨n,T,(max 1 b)^(S.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs U hU t
  have hp:=sourceControl_nonneg T W
  by_cases hret:1≤U*b
  · rw [Plain.profile_retained _ U hU t hret]
    have hd:=normPowerProfile_dilated_finite W a b (max 1 b) (clipDilation U)
      ha (le_max_left _ _) (clipDilation_ge_one U hU) (clipDilation_le b U hU hret)
      hs (W.smooth ⊤) t S
    exact hd.trans ((mul_le_mul_of_nonneg_left (hsource W hs t) (by positivity)).trans_eq (by dsimp only [sourceControl]; ring))
  · rw [Plain.profile_zero _ U hU t (lt_of_not_ge hret)]
    simpa only [sourceControl,map_zero] using
      (show 0≤(max 1 b)^(S.sup Prod.snd)*C*sourceControl T W*(1+‖t‖)^n by positivity)

theorem scale_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control DetectorDictionaryInverseUniform.scaleCLM S

theorem scale_source_support (a b:ℝ) (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    Function.support (DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)⊆Set.Icc a b := by
  have he:(DetectorDictionaryInverseUniform.scaleCLM W:ℝ→ℂ)=
      HeckeInverseAmplification.scaleProfile W :=
    funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)
  rw [he]
  exact HeckeInverseAmplification.scaleProfile_support W a b hs

theorem fourier_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ)) W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))) S

def logWindowMultiply : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ)).restrictScalars ℝ

theorem logWindowMultiply_apply (W:𝓢(ℝ,ℂ)) (x:ℝ) :
    logWindowMultiply W x=CenteredMomentReflectedAnnuli.logWindow x*W x := by
  change (SchwartzMap.smulLeftCLM ℂ
    (CenteredMomentReflectedAnnuli.logWindowSchwartz:ℝ→ℂ) W) x=_
  rw [SchwartzMap.smulLeftCLM_apply_apply
    CenteredMomentReflectedAnnuli.logWindowSchwartz.hasTemperateGrowth]
  rfl

theorem logWindow_source_control (S:Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      sourceControl S (logWindowMultiply W)≤C*sourceControl T W :=
  schwartzCLM_finite_seminorm_control logWindowMultiply S

theorem window_fourier_twist_source_control (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀t:ℝ,
      sourceControl S (FourierTransform.fourierCLM ℝ (𝓢(ℝ,ℂ))
        (logWindowMultiply (JointLogSeparation.frequencyTwist W t)))≤
      C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=fourier_source_control S
  obtain ⟨S₂,C₂,hC₂,h₂⟩:=logWindow_source_control S₁
  obtain ⟨n,T,C₃,hC₃,h₃⟩:=frequencyTwist_source_control S₂
  refine ⟨n,T,C₁*C₂*C₃,by positivity,?_⟩
  intro W t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left
    ((h₂ _).trans (mul_le_mul_of_nonneg_left (h₃ W t) hC₂.le)) hC₁.le).trans_eq (by dsimp only [sourceControl]; ring))

theorem scaled_plain_profile_source_control (a b:ℝ) (ha:0<a) (S:Finset (ℕ×ℕ)) :
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),
      ∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀U:ℝ,∀hU:0<U,∀t:ℝ,
      sourceControl S (DetectorDictionaryInverseUniform.scaleCLM
        ((sourcePlain a b ha W hs).profile U hU t))≤
        C*sourceControl T W*(1+‖t‖)^n := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩:=scale_source_control S
  obtain ⟨n,T,C₂,hC₂,h₂⟩:=plain_profile_source_control a b ha S₁
  refine ⟨n,T,C₁*C₂,by positivity,?_⟩
  intro W hs U hU t
  exact (h₁ _).trans ((mul_le_mul_of_nonneg_left (h₂ W hs U hU t) hC₁.le).trans_eq (by ring))

end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI

end Source1869

/- Original source: OAI/NumberTheory/DirichletL/Energy/Profiles.lean; sha256: 7bf50954f7b7f7c960e59270564daebf6d878af2ed25565e9d56f3e94607be9e -/
section Source1870
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

def lower (a b:ℝ):ℕ→ℝ
  | 0=>a
  | n+1=>lower a b n/max 1 b

lemma lower_pos (a b:ℝ)(ha:0<a)(n:ℕ):0<lower a b n:=by
  induction n with
  | zero=>exact ha
  | succ n ih=>exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):𝓢(ℝ,ℂ):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply (W:𝓢(ℝ,ℂ))(j:Fin 2):
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support (a b:ℝ)(W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(j:Fin 2):
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

def step (a b:ℝ)(ha:0<a)(W:Test a b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Test (a/max 1 b) b where
  profile:=derivativeChoice ((sourcePlain a b ha W.profile W.support).profile U hU t) j
  support:=derivativeChoice_support _ _ _ (sourcePlain_support a b ha W.profile W.support U hU t) j

theorem step_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀U:ℝ,∀hU:0<U,∀t:ℝ,∀j:Fin 2,
      sourceControl S (step a b ha W U hU t j).profile≤
        C*sourceControl T W.profile*(1+‖t‖)^n:=by
  obtain ⟨n₀,T₀,C₀,hC₀,h₀⟩:=plain_profile_source_control a b ha S
  obtain ⟨n₁,T₁,C₁,hC₁,h₁⟩:=scaled_plain_profile_source_control a b ha S
  refine ⟨n₀+n₁,T₀∪T₁,C₀+C₁,add_pos hC₀ hC₁,?_⟩
  intro W U hU t j
  have hT₀:sourceControl T₀ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : T₀⊆T₀∪T₁)) W.profile
  have hT₁:sourceControl T₁ W.profile≤sourceControl (T₀∪T₁) W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : T₁⊆T₀∪T₁)) W.profile
  have hH:1≤1+‖t‖:=by linarith [norm_nonneg t]
  have hR:=sourceControl_nonneg (T₀∪T₁) W.profile
  by_cases hj:j=0
  · have hh:=h₀ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_left hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_right hC₁.le) hT₀ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_right _ _)) (by positivity) (by positivity)
  · have hh:=h₁ W.profile W.support U hU t
    change sourceControl S (if j=0 then _ else _)≤_
    rw [ite_eq_right hj]
    apply hh.trans
    exact mul_le_mul
      (mul_le_mul (le_add_of_nonneg_left hC₀.le) hT₁ (sourceControl_nonneg _ _)
        (add_pos hC₀ hC₁).le)
      (pow_le_pow_right₀ hH (Nat.le_add_left _ _)) (by positivity) (by positivity)

inductive Path (a b:ℝ)(ha:0<a)(T:ℝ)(W:Test a b):
    (n:ℕ)→Test (lower a b n) b→Prop
  | base : Path a b ha T W 0 W
  | next {n:ℕ}{V:Test (lower a b n) b}
      (path:Path a b ha T W n V)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2)(ht:‖t‖≤T):
      Path a b ha T W (n+1) (step _ b (lower_pos a b ha n) V U hU t j)

theorem path_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀V:Test (lower a b d) b,Path a b ha T W d V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  induction d generalizing S with
  | zero=>
    refine ⟨0,S,1,zero_lt_one,?_⟩
    intro W T hT V hpath
    cases hpath
    simp
  | succ d ih=>
    obtain ⟨ns,Rs,Cs,hCs,hs⟩:=step_control (lower a b d) b (lower_pos a b ha d) S
    obtain ⟨np,R,Cp,hCp,hp⟩:=ih Rs
    refine ⟨np+ns,R,Cs*Cp,mul_pos hCs hCp,?_⟩
    intro W T hT V hpath
    cases hpath with
    | next old U hU t j ht=>
      rename_i V
      have h1:=hs V U hU t j
      have h2:=hp W T hT V old
      have hR:=sourceControl_nonneg R W.profile
      have h3:(1+‖t‖)^ns≤(1+T)^ns:=pow_le_pow_left₀ (by positivity) (by linarith) ns
      apply h1.trans
      apply (mul_le_mul (mul_le_mul_of_nonneg_left h2 hCs.le) h3 (by positivity) (by positivity)).trans_eq
      rw [pow_add]
      ring

lemma lower_antitone (a b:ℝ)(ha:0<a):Antitone (lower a b):=by
  apply antitone_nat_of_succ_le
  intro n
  exact div_le_self (lower_pos a b ha n).le (le_max_left _ _)

lemma support_at_depth (a b:ℝ)(ha:0<a)(d n:ℕ)(hn:n≤d)
    (V:Test (lower a b n) b):
    Function.support (V.profile:ℝ→ℂ)⊆Set.Icc (lower a b d) b:=by
  intro x hx
  exact ⟨(lower_antitone a b ha hn).trans (V.support hx).1,(V.support hx).2⟩

theorem paths_upto_control (a b:ℝ)(ha:0<a)(d:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃R:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:Test a b,∀T:ℝ,0≤T→∀k:ℕ,k≤d→∀V:Test (lower a b k) b,
      Path a b ha T W k V→
      sourceControl S V.profile≤C*sourceControl R W.profile*(1+T)^n:=by
  choose J R C hC hbound using fun k:Fin (d+1)=>path_control a b ha k.val S
  let Rs:Finset (ℕ×ℕ):=Finset.univ.biUnion R
  let Cs:ℝ:=1+∑k,C k
  have hCs:0<Cs:=by
    have hh:=Finset.sum_nonneg (fun k (_:k∈(Finset.univ:Finset (Fin (d+1))))=>(hC k).le)
    dsimp [Cs];linarith
  refine ⟨∑k,J k,Rs,Cs,hCs,?_⟩
  intro W T hT k hk V hpath
  let l:Fin (d+1):=⟨k,by omega⟩
  have he:=hbound l W T hT V hpath
  have hR:R l⊆Rs:=by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hi⟩
  have hcontrol:sourceControl (R l) W.profile≤sourceControl Rs W.profile:=
    Seminorm.le_def.mp (Finset.sup_mono hR) W.profile
  have hconst:C l≤Cs:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>(hC j).le)
      (Finset.mem_univ l)
    dsimp [Cs];linarith
  have hdegree:J l≤∑j,J j:=Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin (d+1))))=>Nat.zero_le _) (Finset.mem_univ l)
  have hRpos:=sourceControl_nonneg Rs W.profile
  apply he.trans
  exact mul_le_mul (mul_le_mul hconst hcontrol (sourceControl_nonneg _ _) hCs.le)
    (pow_le_pow_right₀ (by linarith) hdegree) (by positivity) (by positivity)

open CenteredMomentSectorLocalization in
lemma annulus_support : Function.support (fun x:ℝ=>(annulus x:ℂ))⊆Set.Icc (1/4:ℝ) 1:=by
  intro x hx
  have hn:annulus x≠0:=by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

lemma annulusTemplate_apply (x:ℝ):annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI

end Source1870

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularMajorant.lean; sha256: cb7993964732415f9b8a13fd409b6b9ef3fb2576efa47098107ab7c497cf4944 -/
section Source1871
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def weight (x:ℝ):ℝ:=cutoff (x/2)*(1-cutoff (4*x))

lemma weight_bounds (x:ℝ):0≤weight x ∧ weight x≤1:=by
  have h₁:=cutoff_bounds (x/2)
  have h₂:=cutoff_bounds (4*x)
  unfold weight
  constructor
  · exact mul_nonneg h₁.1 (sub_nonneg.mpr h₂.2)
  · exact (mul_le_mul_of_nonneg_left (sub_le_self _ h₂.1) h₁.1).trans
      (by simpa only [mul_one] using h₁.2)

lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0:=by
  rw [weight,cutoff_one (4*x) (by linarith),sub_self,mul_zero]

lemma weight_zero_high (x:ℝ)(hx:2≤x):weight x=0:=by
  rw [weight,cutoff_zero (x/2) (by linarith),zero_mul]

lemma weight_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):weight x=1:=by
  rw [weight,cutoff_one (x/2) (by linarith),cutoff_zero (4*x) (by linarith)]
  norm_num

lemma weight_support:Function.support weight⊆Set.Icc (1/8:ℝ) 2:=by
  intro x hx
  exact ⟨(lt_of_not_ge (fun h=>hx (weight_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hx (weight_zero_high x h))).le⟩

lemma weight_smooth:ContDiff ℝ ∞ weight:=by
  have hc:ContDiff ℝ ∞ cutoff:=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact (hc.comp (contDiff_id.div_const 2)).mul
    (contDiff_const.sub (hc.comp (contDiff_const.mul contDiff_id)))

def profile:𝓢(ℝ,ℂ):=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x:ℝ=>(weight x:ℂ))⊆Set.Icc (1/8:ℝ) 2 from by
      intro x hx
      apply weight_support
      intro hz
      apply hx
      change (weight x:ℂ)=0
      rw [hz]
      rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp weight_smooth)

lemma profile_apply (x:ℝ):profile x=(weight x:ℂ):=rfl
lemma profile_nonneg (x:ℝ):0≤(profile x).re:=(weight_bounds x).1
lemma profile_le_one (x:ℝ):(profile x).re≤1:=(weight_bounds x).2
lemma profile_zero:profile 0=0:=by rw [profile_apply,weight_zero_low 0 (by norm_num)];rfl
lemma profile_one (x:ℝ)(hx:1/4≤x)(hx':x≤1):profile x=1:=by
  rw [profile_apply,weight_one x hx hx'];rfl

lemma scaled_majorant (H q:ℝ)(hH:0<H)(hlo:H/4≤q)(hhi:q≤H):
    (profile (q/H)).re=1:=by
  rw [profile_one (q/H) ((le_div_iff₀ hH).mpr (by linarith))
    ((div_le_one hH).mpr hhi)]
  rfl

def bands (H:ℝ):Finset ℤ:=indices (H/8) (2*H)

lemma bands_scale (H:ℝ)(hH:0<H)(j:ℤ)(hj:j∈bands H):
    H/8≤dyadicScale j ∧ dyadicScale j≤8*H:=by
  have h:=(mem_indices_iff_scale (H/8) (2*H) (by positivity) (by positivity) j).mp hj
  constructor
  · exact h.1
  · linarith [h.2]

lemma bands_card (H:ℝ)(hH:0<H):((bands H).card:ℝ)≤7:=by
  have h:=indices_card_bound (H/8) (2*H) (by positivity) (by linarith)
  have he:(2*H)/(H/8)=16:=by field_simp;ring
  rw [he,show (16:ℝ)=(2:ℝ)^4 by norm_num,Real.logb_pow] at h
  norm_num [Real.logb_self_eq_one] at h
  change ((indices (H/8) (2*H)).card:ℝ)≤7
  exact_mod_cast h

lemma weighted_partition (H q:ℝ)(hH:0<H):
    (profile (q/H)).re=(∑j∈bands H,dyadicWeight j q)*(profile (q/H)).re:=by
  by_cases h:weight (q/H)=0
  · simp only [profile_apply,Complex.ofReal_re,h,mul_zero]
  · have hx:=weight_support h
    have hq:q∈Set.Icc (H/8) (2*H):=⟨by linarith [(le_div_iff₀ hH).mp hx.1],
      (div_le_iff₀ hH).mp hx.2⟩
    rw [bands,dyadic_partition_on_interval (H/8) (2*H) q (by positivity) hq]
    exact (one_mul _).symm

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI

end Source1871

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularEnergy.lean; sha256: 6f5ad12d32d3ab1dc8472661eb5997e0a3910456cd650d2f32930b846981e843 -/
section Source1872
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentFirstAnnularMajorant CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentSmoothedWindowEnergy
local notation "O"=>HeckeFamily.O

variable {α:Type*}

lemma dyadic_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2):=by
  have hs:=gaussEnergy_hasSum_re S a ha c CenteredMomentEnergyProfiles.annulusTemplate.profile
    (dyadicScale j) (dyadicScale_pos j)
  simpa only [CenteredMomentEnergyProfiles.annulusTemplate_apply,Complex.ofReal_re,
    dyadicWeight,normValue_eq_embedding,mul_comm] using hs.summable

lemma weighted_summable (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    Summable (fun z:O=>‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  simpa only [normValue_eq_embedding] using (gaussEnergy_hasSum_re S a ha c profile H hH).summable

theorem energy_partition (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re=
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
  have hs:=weighted_summable S a ha c H hH
  have hj (j:ℤ):Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=by
    apply hs.of_nonneg_of_le
    · intro z
      exact mul_nonneg (dyadicWeight_bounds j _).1 (mul_nonneg (sq_nonneg _) (profile_nonneg _))
    · intro z
      exact mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (profile_nonneg _)) (dyadicWeight_bounds j _).2
  have he (z:O):‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re=
      ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re):=by
    rw [←Finset.sum_mul]
    calc
      _=‖gaussPolynomial S a ha c z‖^2*
          ((∑j∈bands H,dyadicWeight j (normValue z))*(profile (normValue z/H)).re):=by
        rw [←weighted_partition H (normValue z) hH]
      _=_:=by ring
  have hsum:=gaussEnergy_hasSum_re S a ha c profile H hH
  rw [←hsum.tsum_eq]
  simp_rw [←normValue_eq_embedding]
  calc
    _ = ∑'z:O, ∑j∈bands H,dyadicWeight j (normValue z)*
        (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re) :=
      tsum_congr he
    _ = _ := Summable.tsum_finsetSum (fun j _=>hj j)

theorem energy_le_dyadic (S:Finset α)(a:α→O)(ha:∀i,Supported (Ideal.span {a i}))
    (c:α→ℂ)(H:ℝ)(hH:0<H):
    (gaussEnergy S a ha c profile H).re≤
      ∑j∈bands H,∑'z:O,dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=by
  rw [energy_partition S a ha c H hH]
  apply Finset.sum_le_sum
  intro j hj
  have hs:=dyadic_summable S a ha c j
  have hdom (z:O):dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)≤
      dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2:=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (sq_nonneg _) (profile_le_one _))
      (dyadicWeight_bounds j _).1
  have hl:Summable (fun z:O=>dyadicWeight j (normValue z)*
      (‖gaussPolynomial S a ha c z‖^2*(profile (normValue z/H)).re)):=
    hs.of_nonneg_of_le (fun z=>mul_nonneg (dyadicWeight_bounds j _).1
      (mul_nonneg (sq_nonneg _) (profile_nonneg _))) hdom
  exact hl.tsum_le_tsum hdom hs

end SevenEighths.CenteredMomentFirstAnnularEnergy

end

end OAI

end Source1872

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularGeometry.lean; sha256: 52496b2a7103d44e416e86bbf3574f0c72d305843aa47af0ced0d39a488ecf6a -/
section Source1873
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentFirstAnnularGeometry
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAnnularEnergy CenteredMomentGaussEnergy CanonicalQuadraticSieve

local notation "O"=>HeckeFamily.O

lemma retained_of_scale_le (j:ℤ)(R:ℝ)(h:dyadicScale j≤R):Retained R j:=by
  refine ⟨dyadicScale j/2, by exact div_pos (dyadicScale_pos j) (by norm_num), by linarith [dyadicScale_pos j], ?_⟩
  apply subset_closure
  change dyadicWeight j (dyadicScale j/2)≠0
  have he:(dyadicScale j/2)/dyadicScale j=(1/2:ℝ):=by
    field_simp [ne_of_gt (dyadicScale_pos j)]
  rw [dyadicWeight,he,annulus,cutoff_one _ (by norm_num)]
  norm_num [cutoff_zero]

lemma bands_retained (H R:ℝ)(hH:0<H)(hR:8*H≤R)(j:ℤ)(hj:j∈bands H):
    Retained R j:=retained_of_scale_le j R ((bands_scale H hH j hj).2.trans hR)

lemma bands_log_cap (H Z A:ℝ)(hH:0<H)(hZ:1<Z)(hcap:8*H≤Z^A)
    (j:ℤ)(hj:j∈bands H):Real.logb Z (dyadicScale j)≤A:=by
  have he:Real.logb Z (Z^A)=A:=Real.logb_rpow (by positivity) (ne_of_gt hZ)
  rw [←he]
  exact Real.logb_le_logb_of_le hZ (dyadicScale_pos j) ((bands_scale H hH j hj).2.trans hcap)

lemma bands_nonempty (H:ℝ)(hH:0<H):(bands H).Nonempty:=by
  by_contra hn
  have he:bands H=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  have hp:=weighted_partition H (H/2) hH
  have hr:(H/2)/H=(1/2:ℝ):=by field_simp
  rw [hr,profile_one _ (by norm_num) (by norm_num),he] at hp
  norm_num at hp

theorem common_bound {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)(hB:0≤B)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  apply (energy_le_dyadic S a ha c H hH).trans
  calc
    _≤∑j∈bands H,B:=Finset.sum_le_sum hb
    _=((bands H).card:ℝ)*B:=by simp
    _≤7*B:=mul_le_mul_of_nonneg_right (bands_card H hH) hB

theorem common_bound_auto {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  obtain ⟨j,hj⟩:=bands_nonempty H hH
  have hB:0≤B:=(tsum_nonneg (fun z=>mul_nonneg (dyadicWeight_bounds j _).1 (sq_nonneg _))).trans (hb j hj)
  exact common_bound S a ha c H B hH hB hb

end SevenEighths.CenteredMomentFirstAnnularGeometry

end

end OAI

end Source1873

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularAmplification.lean; sha256: 8be1689793eebd5b897ded9e1413ce597c7797f6293de94aa021c11df1c6c983 -/
section Source1874
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularAmplification
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_annular_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentAmplificationRadicalChoice.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert hbnd using 1 ; ring

end SevenEighths.CenteredMomentFirstAnnularAmplification

end

end OAI

end Source1874

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularInput.lean; sha256: 90511d6127417660495d03f0d0f19a5dc8581b08547a64d29e829c070a94e820 -/
section Source1875
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal HeckeFamily.O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      ((original (child s C R B τ t) (R*C) seed).coefficient τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end Source1875

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAnnularActiveInput.lean; sha256: d2d5ca37824458061a1340d77320299902146c3a9033437fd26e1429ed696241 -/
section Source1876
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal HeckeFamily.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal HeckeFamily.O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re ((original s R seed).active_gaussEnergy s.η fixedBadMask s.t (volume s) W H)

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end Source1876

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondActiveErrorGates.lean; sha256: af55991af09be9a66e62883aaa15dfed71c355105f2559f6ed880991b4498a37 -/
section Source1877
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondActiveErrorGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstSecondInputGates CenteredMomentFirstAnnularInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι]

def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

lemma active_endpoints (s : Input ι) (b b₁ b₂ : ℝ) (he : Endpoints b b₁ b₂ s) :
    Endpoints b b₁ b₂ (activeInput s) := he

theorem error_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d := errorInput s C R B τ t Q k Bp υ v;
    let H := volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤sourceRadius d ∧ volume d≤geometry N b b₁ b₂*H ∧
      sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC := norm_ge_one C (allocation_ne s C B)
  have hNp : 0<(Q.absNorm:ℝ)^k := pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH : 0<volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) :=
    div_pos (volume_pos s) (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv : volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [errorInput,child_volume _ Q hQ k hslot,active_volume]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne)
      hNp.le).trans_eq (by ring)
  have hc1 := (live_card_le B.val).trans hc
  have hc2 := (live_card_le Bp.val).trans hc1
  have hep := endpoints_child b b₁ b₂ _
    (active_endpoints _ b b₁ b₂ (endpoints_child b b₁ b₂ s he C R B τ t))
    (Q^k) (R*C) Bp υ v
  have hr := radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hpow : b^N≤geometry N b b₁ b₂ := by
    have hp : 1≤b^N := one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh : 1≤b₁*b₂ := by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq (by
    unfold geometry;rw [show 2*N=N+N by omega,pow_add];ring))

theorem eventually_active_error_ready (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type*}[Fintype ι],∀s : Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q : Ideal O),Q≠0 → ∀k : ℕ,
    (∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I) →
    ∀(Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
      (υ : Character)(v K A D P q ξ : ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I : Ideal O,(original (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    Ready (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ
      (exponent A D P q ε ξ) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hVp hKi hRN hυ hlive
  let d := errorInput s C R B τ t Q k Bp υ v
  let G := geometry N b b₁ b₂
  have hg : 1≤G := geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hcap := error_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hB Q hQ k hslot Bp υ v
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  have hd1 : 1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc := norm_ge_one C (allocation_ne s C B)
    have hq : 1 ≤ (Q.absNorm : ℝ)^k := one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hHV : volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤volume s :=
    div_le_self (volume_pos s).le hd1
  have hm := mul_le_mul_of_nonneg_left hHV (zero_le_one.trans hg)
  have hpoly := polynomial_caps G (volume s) (volume d) (sourceRadius d) K Z A D ε ξ
    hg hZ.1 hZ.2.2 (volume_pos s) (volume_pos d) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKi
  obtain ⟨I,hI⟩ := hlive
  have hi := child_column_norm (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hone : 1≤G*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) :=
    (norm_ge_one I hi.1).trans (hi.2.2.trans hcap.2.2.2)
  rw [←mul_div_assoc] at hone
  have hprod : (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤G*volume s := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hone
  have hpunct : (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
    rw [puncture_norm]
    calc
      _≤(R.absNorm:ℝ)*(G*volume s) := by nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg R.absNorm)]
      _≤Z^P*(Z^ε*Z^A) := mul_le_mul hRN
        (mul_le_mul hZ.2.1 hVp (volume_pos s).le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (mul_nonneg (zero_le_one.trans hg) (volume_pos s).le)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
      _=Z^(A+P+ε) := by rw [←Real.rpow_add (zero_lt_one.trans hZ.1),←Real.rpow_add (zero_lt_one.trans hZ.1)];congr 1;ring
  have h₁ : A+ε≤exponent A D P q ε ξ := le_max_left _ _
  have h₂ : 2*A+D+ε+ξ/2≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : A+P+ε≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄ : q≤exponent A D P q ε ξ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y : ℝ} (h : x≤y) : Z^x≤Z^y := Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  exact ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hpoly.1.trans (hpow h₁),hcap.2.1,hpoly.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hpunct.trans (hpow h₃),nominal_pos d K hK,
    hpoly.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hpoly.2.2.2.1,hpoly.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondActiveErrorGates

end

end OAI

end Source1877

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstAmplifiedActiveCapacitySource.lean; sha256: 9a3b6d57e4e6759901998d0bfedb30488679aca2efef366f6509d8885ab0474d -/
section Source1878
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacitySource CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstAnnularInput

theorem active_error_volume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (errorInput s C R B τ t Q k Bp υ v)=
      volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [errorInput,child_volume _ Q hQ k hslot,active_volume,common_volume]
  ring

theorem actual_active_error_source_shift (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(C₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

theorem actual_active_error_source_shift_right (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0<K)(hZ:1<Z)(hcost:0<cost)(ha:0<a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤sigma)
    (hl:sigma/6≤Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0):
    Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)/(D₂.absNorm:ℝ))-
      Real.logb Z (adjustedEnvelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        6*errorRemoval p Z k+delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
        min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
        Real.logb Z fixedPresentationCost-Real.logb Z cost+
        Real.logb Z (4/((fixedFactor:ℝ)*a^2)) := by
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hrad:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:=actual_capacity_shift_reference_right υ v S β C₂ D₂ hC₂ hD₂ hCD₂ U R rows W _
    (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)) a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n
    (by positivity) hrad (volume_pos _) ha hZ hlower hne
  have hr:=actual_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by
    simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg ⊢
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  linarith

end SevenEighths.CenteredMomentFirstAmplifiedActiveCapacitySource

end

end OAI

end Source1878

/- Original source: OAI/NumberTheory/DirichletL/Energy/SlotHeight.lean; sha256: af0d8c1a08386df802a579abcae97d055358cc24a4306446a80cdb278c9b97f1 -/
section Source1879
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0<P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0<P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end SevenEighths.CenteredMomentEnergySlotHeight

end

end OAI

end Source1879
