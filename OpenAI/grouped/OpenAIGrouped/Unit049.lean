import OpenAIGrouped.Unit048
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit047
import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit024
import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit046

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalFixedQDyadic.lean; sha256: 434093965df52f69e4a60198f5495018c79b2bd087e592b3476693eeb1b9fd0f -/
section Source1960
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end Source1960

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalBudget.lean; sha256: 063fa5df481282bcadd20ac10a7efc0c0e474e8be8b1293a8cae4ed82ba46c92 -/
section Source1961
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ):
    profileMass Sprofile s.toData s.toData p p J=
      p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold CenteredMomentFiniteProfileExceptionalCommon.profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor Sprofile s p J Q K:=by
  unfold profileFactor
  have hp:=Profiles.control_nonneg p Sprofile
  positivity

lemma sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact Sprofile s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1961

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalCanonical.lean; sha256: b552e5c8c9ef458509b5b1c1daab36ed7ab9a5b0d04b42421efe1e991675e90a -/
section Source1962
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentCommonExceptionalCanonical
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalSymmetry
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost CenteredMomentCommonExceptionalMass CenteredMomentCommonExceptionalGates
open CenteredMomentExceptionalAsymmetricSource CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_canonical_bound (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) :=by
  obtain ⟨J,hJ⟩:=actual_common_better_side lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hc:=actual_canonical_exceptional_count η₀ χ C D hC U Q hQ hQtop hQ72 hcop hη
    m hm hml hm2 rows hn hex Z Cr M hZ.1 hCr hN
  have hb:=hZ.2 s v p q hslo hshi hvlo hvhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond Ds hDs
  let F:ℝ:=profileMass s.toData v.toData p q J*frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm)
  have hF:0≤F:=div_nonneg (mul_nonneg (mul_nonneg (profileMass_nonneg _ _ _ _ _) (frozenProfile_nonneg _))
    (frozenProfile_nonneg _)) (by positivity)
  let e:ℝ:=2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
    (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)
  let f:ℝ:=(M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6
  have hz:=zero_lt_one.trans hZ.1
  apply hb.trans
  calc
    _≤K*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f)*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F:=by
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hK.le
    _=_:=by
      have hpow:Z^(f+e)=Z^f*Z^e:=Real.rpow_add hz _ _
      change K*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f)*Z^e*
        ((C.absNorm:ℝ)*D.absNorm)^θ*F=K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^(f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*((C.absNorm:ℝ)*D.absNorm)^θ*F
      rw [show f+2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
          (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0)=f+e by dsimp [e];ring,hpow]
      ring

end SevenEighths.CenteredMomentCommonExceptionalCanonical

end

end OAI

end Source1962

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonExceptionalCanonicalWindow.lean; sha256: b251fef9bce9fd5c5836923c50efbd4909034bd8558d104488230993537a458d -/
section Source1963
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalSource CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentExceptionalHeight CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentCommonExceptionalCanonical CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤s.X₁ → Z^rLeft≤s.X₂ → Z^rLeft≤s.Y₁ → Z^rLeft≤s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 :=by
  obtain ⟨J,hJ⟩:=actual_common_canonical_bound lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s v p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂ C D hC hD R seed hR hsC hsD
    rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂ rows hn hsEx hvEx hsCond hvCond
    η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN θ₁ θ₂ X Y hX hY Ds hDs
  let F:=K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg v)) (by positivity))
  have hh:=whole_window_pair s v C D hC hD R seed Ds (fun L=>(moebius L:ℂ)) rows
    s.η v.η s.t v.t θ₁ θ₂ X Y hX hY logAnnulus logAnnulus
    logAnnulus_compact logAnnulus_compact logAnnulus_smooth logAnnulus_smooth
    J J (F*mass s v p q s.t v.t θ₁ θ₂ J)
    (mul_nonneg hF (mass_nonneg s v p q s.t v.t θ₁ θ₂ J)) ?_
  · simpa only [F,pow_two,mul_assoc] using hh
  intro u w
  have hb:=hZ.2 (withHeight s s.η (s.t+2*Real.pi*(u-θ₁)))
    (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))) p q hslo hshi hlo hhi hsP hvP hsW₁ hsW₂ hvW₁ hvW₂
    C D hC hD R seed hR hsC hsD rLeft rRight hsX₁ hsX₂ hsY₁ hsY₂ hvX₁ hvX₂ hvY₁ hvY₂
    rows hn hsEx hvEx hsCond hvCond η₀ χ U hcop hη m hm hml hm2 hex Cr M hCr hN Ds hDs
  have hm:=shifted_mass s v s.η v.η p q s.t v.t θ₁ θ₂ u w J
  apply hb.trans
  calc
    _=F*profileMass (withHeight s s.η (s.t+2*Real.pi*(u-θ₁))).toData
        (withHeight v v.η (v.t+2*Real.pi*(w-θ₂))).toData p q J:=by
      dsimp only [F,frozenProfile,withHeight]
      ring
    _≤F*(mass s v p q s.t v.t θ₁ θ₂ J*(1+‖u‖)^J*(1+‖w‖)^J):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by ring

end SevenEighths.CenteredMomentCommonExceptionalCanonicalWindow

end

end OAI

end Source1963

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalCanonicalPair.lean; sha256: 833182bdfc0e27e8f5ba3b30224d50ed1207f78544be9638387b7adcebe1a80b -/
section Source1964
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalCanonicalPair
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentCommonExceptionalCanonicalWindow CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_canonical_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalCanonicalPair

end

end OAI

end Source1964

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalOriginalBlock.lean; sha256: feb7715090bec07d46ec49fbb4fde19e5bb5d6809597090eefcf344f00540ee5 -/
section Source1965
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalOriginalBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound CenteredMomentSecondExceptionalCanonicalPair
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0<rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,hJ⟩:=actual_canonical_original_pair lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentSecondExceptionalOriginalBlock

end

end OAI

end Source1965

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalBudget.lean; sha256: b56ec74ec8b790d05474dc558404180677833a27a976641fa40eadf567929b2b -/
section Source1966
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalBudget
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondPhysicalLedger
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self (s:Input ι)(p:Tests)(J:ℕ):
    profileMass s.toData s.toData p p J=
      p.heightWeight s.t^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.heightWeight s.t^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor s p J Q K:=by
  unfold profileFactor
  have hp:0≤p.heightWeight s.t:=by unfold Tests.heightWeight; positivity
  positivity

lemma sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentSecondExceptionalBudget

end

end OAI

end Source1966

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalPhysicalSaving.lean; sha256: df2740b4da67cfb019ea97010711cdbc067b5706377637864d9ce22bf3ddc3a6 -/
section Source1967
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma column_power_saving (Z c d θ:ℝ) (hZ:1<Z) (hc:1≤c) (hd:1≤d) (hθ:θ≤1/3) :
    (c*d)^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3)≤1 := by
  have hc0:0<c:=zero_lt_one.trans_le hc
  have hd0:0<d:=zero_lt_one.trans_le hd
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:-(Real.logb Z c+Real.logb Z d)/3=Real.logb Z (c*d)*(-1/3):=by
    rw [Real.logb_mul hc0.ne' hd0.ne'];ring
  rw [he,Real.rpow_mul hz.le,Real.rpow_logb hz (ne_of_gt hZ) (mul_pos hc0 hd0),
    ←Real.rpow_add (mul_pos hc0 hd0)]
  have hcd:1≤c*d:=by nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hcd (by linarith : θ+ -1/3≤0)).trans_eq
    (Real.rpow_zero _)

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

theorem original_budget_physical_saving_full
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤min c d:=le_min hc hd
  have hc':min c d≤c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤r
  · rw [max_eq_left hr]
    by_cases hm:r≤min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤max (r-min c d) 0:=le_max_right _ _
    linarith

theorem original_budget_physical_saving
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)(hθ:θ≤1/3)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  have hcol:=column_power_saving Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ hZ hc hd hθ
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hA:0≤A:=mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _)
  have hv:=volume_pos s.toData
  have hE:0≤E:=by dsimp [E];positivity
  have hnum:A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n≤A*E:=by
    calc
      _≤A*((C.absNorm:ℝ)*D.absNorm)^θ*
          (E*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
        exact mul_le_mul_of_nonneg_left hcost (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      _=A*E*(((C.absNorm:ℝ)*D.absNorm)^θ*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by ring
      _≤A*E*1:=mul_le_mul_of_nonneg_left hcol (mul_nonneg hA hE)
      _=A*E:=mul_one _
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right hnum (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI

end Source1967

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalSaving.lean; sha256: 7fba2f930c8a8b840630371c399641be27bc8af6571a3604d7ea3a1dde995245 -/
section Source1968
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem original_budget_physical_saving_full
    {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg Sprofile s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact Sprofile s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1968

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalFixedQSaved.lean; sha256: e0d8fa66fe002cf53ecd8f2b3f6ebe22be70bf5598aff64d0ea72efc653c079d -/
section Source1969
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end Source1969

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalCommonSaving.lean; sha256: 676647a34089a39ddb4332099d710962599ca418bad84064fce840145c422f82 -/
section Source1970
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSecondExceptionalCommonSaving
open CenteredMomentSecondExceptionalPhysicalSaving
lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1<Z)(hc:1≤c)(hd:1≤d)
    (hθ:0≤θ)(hC:c≤Z^B)(hD:d≤Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hcd:0≤c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end SevenEighths.CenteredMomentSecondExceptionalCommonSaving

end

end OAI

end Source1970

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalFixedQUniform.lean; sha256: 36d035c95fc7e41540301f92f8a9a33e1b750d04cc5f5eaf198bf099a9d85d29 -/
section Source1971
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end Source1971

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalRows.lean; sha256: 43a8c87cf8276f01fa7a306679da08e09f22b6f23d39753bc824976ee9ea7971 -/
section Source1972
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0<rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1972

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalDyadic.lean; sha256: efa2da05f1888c5c59c398dd771fcea1711350db598638b870be23ac7999bd21 -/
section Source1973
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hcop hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1973

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalSaved.lean; sha256: a61a2e04672e9b6987940b144508eaf6edf5c6204efe77e033ee80fe7c1f0481 -/
section Source1974
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1974

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalFixedQChosenBlock.lean; sha256: e094038ea6cef135844eb84328fcea20f851b30d25ae2aedc29705a50b898c6c -/
section Source1975
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

theorem chosen_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),
      R0≠0 → seed∣C → seed∣D → (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      sourceRadius s≤Z^Lbound → ∀(R Kphys:ℝ),0<Kphys →
      (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(4*R)≤Z^B →
      ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R0 seed) C D hC hD U R
        (partRows true s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hbound⟩:=
    CenteredMomentFiniteProfileExceptionalFixedQ.actual_uniform_exceptional_block
      wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 χ₀ hη m hm hml hm2 hsource R Kphys hKphys hcond n
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R0 seed
  let rows:=partRows true s.η χ₀ Q m C D U R
  have hn:∀z∈rows,z≠0:=exceptional_part_nonzero s.η χ₀ Q m C D U R
  have hex:=exceptional_part_inducing s.η χ₀ Q m C D U R
  have hprofile0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hp:=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hprofile0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hprofile0 1
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2
  have hD1:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^Lbound:=by
    by_cases hh:0≤sourceRadius s
    · exact (div_le_self hh hD1).trans hsource
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hh) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have ha:0<(∏i,s.lo i)*wlo*wlo:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
  have hlower (I:Ideal O)(hI:β I≠0):
      ((∏i,s.lo i)*wlo*wlo)*volume s.toData≤(I.absNorm:ℝ):=by
    have hh:=profile_column_lower R0 s.ν s.W s.P s.lo s.W₁ s.W₂ wlo wlo
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos (fun i=>(s.lo_pos i).le)
      hwlo.le hwlo.le s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      (fun i x hx=>(s.support i hx).1)
      (fun x hx=>(p.support 0 (by rwa [hW1] at hx)).1)
      (fun x hx=>(p.support 1 (by rwa [hW2] at hx)).1)
      (Fintype.piFinset s.pools) I hI
    simpa only [CenteredMomentExceptionalAmplitudePair.volume,map_one,Nat.cast_one,mul_one,div_one,mul_assoc] using hh
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have hZpos:0<Z:=zero_lt_one.trans hZ.1
    exact mul_nonneg hCk (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hp (Real.rpow_nonneg hZpos.le _)) (Real.rpow_nonneg hv.le _))
      (Real.rpow_nonneg hKphys.le _)) (Real.rpow_nonneg ha.le _)) (Nat.cast_nonneg _))
  obtain ⟨τ,hτ⟩:=exists_exceptional_family s.η C D hC hD hCD U
  have he:=actual_family_both_rows s.η χ₀ Q hQ72 m hm hml hm2 C D hC hD U τ hτ R
  have hc (χ ξ:RayCharacter)(z:O)(hz:z∈rows):
      (expandedConductor (τ χ) R0 C z:ℝ)≤Z^B ∧
      (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤Z^B:=by
    have hg:=expanded_conductor_bounds hτ hCD s.t S β R rows W Kphys hKphys n hzero χ ξ R0 z
    have hzlive:z∈liveRows C D U R rows:=by
      rw [show liveRows C D U R rows=rows from exceptional_part_live s.η χ₀ Q m C D U R]
      exact hz
    have hzN:=live_norm_le_four_radius C D U R rows z hzlive
    have hb:(expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤Z^B:=by
      apply le_trans _ hcond
      exact mul_le_mul_of_nonneg_left hzN (by positivity)
    constructor
    · exact (show (expandedConductor (τ χ) R0 C z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.1).trans hb
    · exact (show (expandedConductor (reflected (τ ξ)) R0 D z:ℝ)≤
        (expandedFactor s.η:ℝ)*R0.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hg.2).trans hb
  exact hZ.2 s p hlo hhi hP hW1 hW2 C D hC hD R0 seed hR0 hsC hsD hNC hND hCD U
    r hX1 hX2 hY1 hY2 τ hτ.height_eq rows hn he.1 he.2
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).1)
    (fun χ z hz=>by simpa only [expandedConductor,Nat.cast_mul] using (hc χ χ z hz).2)
    χ₀ hη m hm hml hm2 hex (sourceRadius s) hβ hHD
    ((∏i,s.lo i)*wlo*wlo) ha hlower R Kphys hKphys n

end SevenEighths.CenteredMomentSecondExceptionalFixedQChosenBlock

end

end OAI

end Source1975

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalAggregate.lean; sha256: fb64ba47415fddfed73269beb1c039a688847fc4a2f29becdbf641f633044abc -/
section Source1976
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_radical_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,radicalWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockRadicalHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=>Finset.sum_nonneg (fun U _=>mul_nonneg (Nat.cast_nonneg _) (radicalWeight_nonneg _ _)))

theorem part_energy_radical_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        radicalWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          radicalWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left (live_radical_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_radical_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_radical_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end SevenEighths.CenteredMomentSecondExceptionalAggregate

end

end OAI

end Source1976

/- Original source: OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalPhysicalUniform.lean; sha256: 9190e8756e1cb6c236fac9b6cea135a956cbb0a2a2741ce9843c64a8bc6df438 -/
section Source1977
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end Source1977

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalFixedQSource.lean; sha256: 49d2a891448583561e4f607a615bd86524c3a7ddbece00a20dcdfb6103a7c62c -/
section Source1978
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalFixedQSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hblock⟩:=chosen_exceptional_block wlo whi hwlo hwhi lo hi W
    ε δ θ B B hε hδ hθ hB hB
  obtain ⟨Cm,hCm,hmass⟩:=source_part_radical_bound B L Cr δ hB hL hCr hδ
  refine ⟨J,Sprofile,hSp,Ck*Cm,mul_nonneg hCk hCm.le,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hblock⟩:=hblock Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRcap hcond r hX1 hX2 hY1 hY2
  have hp0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hh':=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hp0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hp0 1
  let V:=volume s.toData
  let a:ℝ:=(∏i,s.lo i)*wlo*wlo
  let F:=Ck*profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ+2*B*θ-2*max r 0/3)*V^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
    have hzp:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F,V]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hcap)
    true s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) V F
    hKphys hRcap hcap (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:CenteredMomentSecondBlockAggregate.SourceBlocks q.val.1 q.val.2 U Kphys R (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U R
        (partRows true s.η χ₀ Q m q.val.1 q.val.2 U R) W Kphys (fun i=>(n i:ℤ))‖/V≤
          F*radicalWeight q.val.1 q.val.2:=by
    intro q hq U n
    have hg:=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource S β) _ _ q.property
    have hcnd:(expandedFactor s.η:ℝ)*R0.absNorm*q.val.1.absNorm*q.val.2.absNorm*(4*R)≤Z^B:=by
      apply le_trans _ hcond
      have hH:0≤sourceRadius s:=(Nat.cast_nonneg q.val.1.absNorm).trans hg.2.2.2.2.2.1
      calc
        _=(expandedFactor s.η:ℝ)*R0.absNorm*((q.val.1.absNorm:ℝ)*q.val.2.absNorm)*(4*R):=by ring
        _≤(expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s*sourceRadius s)*(4*R):=by
          gcongr
          · exact hg.2.2.2.2.2.1
          · exact hg.2.2.2.2.2.2
        _=_:=by ring
    have hh:=hZ.2 s p hlo hhi hP hW1 hW2 q.val.1 q.val.2 hs.1 hs.2 R0 seed hR0
      hg.2.2.2.1 hg.2.2.2.2.1 (hg.2.2.2.2.2.1.trans hcap) (hg.2.2.2.2.2.2.trans hcap)
      hg.2.2.1 U r hX1 hX2 hY1 hY2 χ₀ ((mem_liveLabels _ _ _ q).mp hq).1
      m hm hml hm2 hcap R Kphys hKphys hcnd (fun i=>(n i:ℤ))
    rw [←physicalBlock_active]
    exact hh.trans_eq (by dsimp only [F,V,a,radicalWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ=
      Z^(2*ε+2*δ+2*B*θ-2*max r 0/3):=by
    rw [←Real.rpow_add (zero_lt_one.trans hZ.1)]
    congr 1
    ring
  dsimp only [F,V,a]
  calc
    _=(Ck*Cm)*profileFactor Sprofile s p J Q K*
      (Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]

end SevenEighths.CenteredMomentSecondExceptionalFixedQSource

end

end OAI

end Source1978

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalFamilyUniform.lean; sha256: 8855774942d25ba08214194d99cf55af40990fb128cda7085513529bd6f16699 -/
section Source1979
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

def fixedExpandedCost : ℝ :=
  1296*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedExpandedCost_pos : 0<fixedExpandedCost := by
  have hb : (0:ℝ)<(Ideal.span {fixedBadMask}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h72 : (0:ℝ)<(Ideal.span {(72:O)}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (show (72:O)≠0 by norm_num)))
  have hf : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  unfold fixedExpandedCost
  positivity

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

theorem expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    (expandedConductor (τ χ) R C z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z := by
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hl' : (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hl
  have hr' : (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hr
  rw [expandedFactor_real] at hl' hr'
  exact ⟨hl',hr'⟩

theorem live_expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O)(hz:z∈liveRows C D U radius rows) :
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
  obtain ⟨hR,hz0,hz1,_⟩ := liveRows_geometry C D U radius rows z hz
  obtain ⟨hl,hr⟩ := expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hf := fixedExpandedCost_pos
  have hbound : fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
    calc
      _≤fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*(4*radius) :=
        mul_le_mul_of_nonneg_left (live_norm_le_four_radius C D U radius rows z hz)
          (by positivity)
      _=_ := by ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem eventually_uniform_live_caps (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀η:Character,
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*fixedExpandedCost)
  obtain ⟨Z₁,hZ₁⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₁,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ η C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m q hη hCN hDN hRN hrad z hz
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₁ Z ((le_max_right _ _).trans hZ)
  obtain ⟨hR,hz0,hz1,hl,hr⟩ := live_expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z hz
  have hbound : (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius≤
      Z^(c+d+r+m+q+ε) := by
    calc
      _≤Z^ε*Z^q*Z^r*Z^c*Z^d*Z^m := by gcongr
      _=Z^(c+d+r+m+q+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,
          ←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem exists_uniform_exceptional_family (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D),
    primeSupport C=primeSupport D→∀U:Finset (CommonIndex C D),
    ∃τ:RayCharacter→Character,Family η C D hC hD U τ ∧
    ∀Z:ℝ,Z₀≤Z→∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  obtain ⟨Z₀,hZ₀,hcaps⟩ := eventually_uniform_live_caps ε hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro η C D hC hD hCD U
  obtain ⟨τ,hτ⟩ := exists_exceptional_family η C D hC hD hCD U
  refine ⟨τ,hτ,?_⟩
  intro Z hZ
  exact hcaps Z hZ η C D hC hD hCD U τ hτ

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI

end Source1979

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalSourceCaps.lean; sha256: 5249b188c9ee252ef66f5e3f4cbd7e48a51530c0ca86e3d4d4e7afaa677f5764 -/
section Source1980
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace SevenEighths.CenteredMomentSecondExceptionalSourceCaps
open HeckeFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalFamilyUniform
local notation "O" => HeckeFamily.O

theorem eventually_source_caps :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(η:Character)(R0:Ideal O)(H R B:ℝ),
      0≤B → 0≤H → 0≤R → (η.modulus.absNorm:ℝ)≤Z^B →
      (R0.absNorm:ℝ)≤Z^B → H≤Z^B → R≤Z^B →
      H≤Z^(5*B+1) ∧
      (expandedFactor η:ℝ)*R0.absNorm*H^2*(4*R)≤Z^(5*B+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*fixedExpandedCost)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro η R0 H R B hB hH hR hη hR0 hHN hRN
  have hz:0<Z:=zero_lt_one.trans hZ
  have hH2:H^2≤(Z^B)^2:=pow_le_pow_left₀ hH hHN 2
  have hbig:B≤5*B+1:=by linarith
  refine ⟨hHN.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hbig),?_⟩
  rw [expandedFactor_real]
  calc
    _=(4*fixedExpandedCost)*(η.modulus.absNorm:ℝ)*R0.absNorm*H^2*R:=by ring
    _≤Z*(Z^B)*(Z^B)*(Z^B)^2*(Z^B):=by gcongr
    _=Z^(5*B+1):=by
      rw [show (Z^B)^2=Z^B*Z^B by ring]
      calc
        _=Z^(1:ℝ)*Z^B*Z^B*(Z^B*Z^B)*Z^B:=by rw [Real.rpow_one]
        _=Z^(5*B+1):=by
          repeat rw [←Real.rpow_add hz]
          congr 1
          ring

end SevenEighths.CenteredMomentSecondExceptionalSourceCaps

end

end OAI

end Source1980

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondExceptionalUniformSource.lean; sha256: 5e184d97161c24ce02b4df931decccc96a759a1fb8f483db8e6272dff58b5ca4 -/
section Source1981
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalUniformSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

theorem original_exceptional_energy (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ) :=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hsource⟩:=
    CenteredMomentSecondExceptionalFixedQSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ (5*B+1) B 1 hε hδ hθ (by positivity) hB zero_lt_one
  refine ⟨J,Sprofile,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hsource⟩:=hsource Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hsource,CenteredMomentSecondExceptionalSourceCaps.eventually_source_caps] with Z hZ hcaps
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRN r hX1 hX2 hY1 hY2
  obtain ⟨hHlarge,hcond⟩:=hcaps.2 s.η R0 (sourceRadius s) R B hB hH0 hR.le hη hR0N hH hRN
  exact hZ.2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hHlarge χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys hR (by simpa using hRN) hcond r hX1 hX2 hY1 hY2

end SevenEighths.CenteredMomentSecondExceptionalUniformSource

end

end OAI

end Source1981

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceDiagonal.lean; sha256: f35d5c5f2d1755dd2f92ab3a1bfafbe294e8a87daed85c42f50591bbbd300c8a -/
section Source1982
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSourceDiagonal
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceSecondZeroEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem actual_second_zero (N:ℕ)(ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N →
      ∀(a b:ℝ),0<a → 0≤b → ∀(s:Input ι)(p:Profiles a b),
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → ∀(R seed:Ideal O),seed≠0 →
      ∀κ:ℂ,
      ‖κ*sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData≤
      C*‖κ‖*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*
        (∏i,s.M i))^2*(1+(∏i,max 0 (s.hi i))*b*b)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=profile_second_zero_energy N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p hw1 hw2 R seed hseed κ
  have hM (i:ι):0≤s.M i:=zero_le_one.trans (s.M_ge_one i)
  have hhi (i:ι):0≤max 0 (s.hi i):=le_max_left _ _
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt ha) (p.support i hn).1
  have hslotzero (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hW1:∀x,‖s.W₁ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 0):=by
    intro x;rw [hw1];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hW2:∀x,‖s.W₂ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 1):=by
    intro x;rw [hw2];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hh:=(hbound hcard s.η s.t R s.ν s.ν_bound s.W s.P s.M (fun i=>max 0 (s.hi i)) s.W₁ s.W₂
    (SchwartzMap.seminorm ℝ 0 0 (p.profile 0)) (SchwartzMap.seminorm ℝ 0 0 (p.profile 1)) b b
    hM (apply_nonneg _ _) (apply_nonneg _ _) hhi hb hb s.W_bound hW1 hW2
    hslotzero (by rw [hw1];exact hz 0) (by rw [hw2];exact hz 1)
    (fun i x hx=>((s.support i hx).2).trans (le_max_right _ _))
    (by intro x hx;rw [hw1] at hx;exact (p.support 0 hx).2)
    (by intro x hx;rw [hw2] at hx;exact (p.support 1 hx).2)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero hseed rfl s.same_product (Fintype.piFinset s.pools)).2 κ
  have hV:=volume_pos s.toData
  simpa only [map_one,Nat.cast_one,mul_one,div_one,coefficient,volume,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,abs_of_pos s.X₁_pos,abs_of_pos s.X₂_pos,
    abs_of_pos (Finset.prod_pos (fun i _=>s.P_pos i)),mul_div_assoc,div_mul_eq_mul_div] using hh

end SevenEighths.CenteredMomentSecondSourceDiagonal

end

end OAI

end Source1982

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceRemainder.lean; sha256: 510ef13ecdf973cde3ca6996e4bc23624a43ea238351fb730905e4744715884e -/
section Source1983
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondSourceRemainder
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

open CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson

theorem original_source_remainder (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cexc Cdiag Ctail:ℝ,0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec Kphys:ℝ),0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving):=by
  obtain ⟨J,Sprofile,hSp,Cexc,hCexc,hexc⟩:=
    CenteredMomentSecondExceptionalUniformSource.original_exceptional_energy
      wlo whi hwlo hwhi lo hi W ε δ θ B hε hδ hθ hB
  obtain ⟨Cdiag,hCdiag,hdiag⟩:=CenteredMomentSecondSourceDiagonal.actual_second_zero (Fintype.card ι) ε hε
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_input_tail_arbitrary_saving hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hexc⟩:=hexc Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hexc,htail] with Z hZ htZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β χ₀ m hm hml hm2
    Tsec Kphys hKphys hVcap hTcap hnom R hR hRcap r hX1 hX2 hY1 hY2
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  have hboundI:∀I∈S,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I _ hn=>(original_column_norm s R0 seed I hz1 hz2 hn).2
  have he:=sourceGaussEnergy_localized s.η s.t S β W Kphys Tsec Z ξ hKphys
  rw [original_energy_split s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s) hKphys hboundI] at he
  have hrem:sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
      partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)=
      ((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t+
      partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)+
      secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ:=by rw [he];ring
  have hd:=hdiag (ι:=ι) le_rfl wlo whi hwlo hwhi s p hw1 hw2 R0 seed hseed0
    ((Kphys:ℂ)*paperRadialFourier W 0)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys] at hd
  have hhiEq:(∏i,max 0 (s.hi i))=∏i,hi i:=by
    apply Finset.prod_congr rfl
    intro i _
    rw [hhis i,max_eq_right (hhi i)]
  rw [hhiEq] at hd
  have hex:=hZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap r hX1 hX2 hY1 hY2
  have ht:=htZ.2 s (p.profile 0) (p.profile 1) hw1 hw2 (p.support 0) (p.support 1)
    (fun i=>(hhis i).le) R0 seed W Kphys Tsec hKphys hVcap hTcap hnom
  rw [hrem]
  calc
    _≤(‖((Kphys:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t‖+
      ‖partEnergy true s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖+
      ‖secondDiscardedEnergy s.η s.t S β W Kphys Tsec Z ξ‖)/volume s.toData:=by
      exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le
    _=_:=by rw [add_div,add_div]
    _≤_:=by
      apply add_le_add (add_le_add _ hex) ht
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hKphys]
      convert hd using 1 ; ring

end SevenEighths.CenteredMomentSecondSourceRemainder

end

end OAI

end Source1983

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalCost.lean; sha256: 3d8c069f81501a2dec440a03b46e17d740748c623d71f51a691a53641e7aba59 -/
section Source1984
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondNonexceptionalCost
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

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondRadicalBudget

theorem actual_canonical_child_cost (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃Ck:ℝ,0<Ck ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let _r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → 0≤sourceRadius s → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂ :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=actual_canonical_children lo hi W 1 J₁ J₂ B δ hB hδ
  have hfixed:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  refine ⟨4*(fixedFactor:ℝ)*(C0*Ce),by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH0 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hp:=profileCost_nonneg s
  have hhgt:=heightEnvelope_pos s.t
  have hpm1:=profileMoment_nonneg J₁
  have hpm2:=profileMoment_nonneg J₂
  by_cases hzero:physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n=0
  · rw [hzero,norm_zero,zero_div]
    positivity
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=
    fun I hi=>(original_column_norm s R0 seed I hz1 hz2 hi).2
  let E:=childEnvelope s.η C D U n
  have hdyad:0<dyadicScale (n 1):=dyadicScale_pos _
  have hE:0≤E:=by unfold E childEnvelope;positivity
  have hτ:∀χ:RayCharacter,((τ χ).modulus.absNorm:ℝ)*dyadicScale (n 1)≤E:=
    family_child_envelope hf s.t S β R rows W Kphys hKphys n hzero
  have hl:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₁*E)*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b a ha
    apply (hleft L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₁)
      (show 0≤(1+‖v‖)^(2*J₁) by positivity)
    simpa only [mul_assoc] using hh
  have hr:∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b) (canonicalRadial (τ χ) Q n) L a≤
        (E₂*E)*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b a ha
    apply (hright L hL hLN hsf χ v b a ha).trans
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hτ χ) hE₂)
      (show 0≤(1+‖v‖)^(2*J₂) by positivity)
    simpa only [mul_assoc] using hh
  have hh:=hZ.2 Kphys hKphys n s τ hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 (E₁*E) (E₂*E) (mul_nonneg hE₁ hE) (mul_nonneg hE₂ hE) hl hr
  have hsqrt:Real.sqrt ((E₁*E)*(E₂*E))=E*Real.sqrt (E₁*E₂):=by
    rw [show (E₁*E)*(E₂*E)=E^2*(E₁*E₂) by ring,
      Real.sqrt_mul (sq_nonneg E),Real.sqrt_sq hE]
  simp only [pow_one,hsqrt] at hh
  have hscalar:=actual_source_envelope_scalar s.η s.t S β C D hC hD U R rows W Kphys hKphys n
    (sourceRadius s) hβ hzero
  let F:ℝ:=(C0*Ce)*Z^(2*δ)*profileCost s*Real.sqrt (E₁*E₂)*
    heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by dsimp only [F];positivity
  have hsc:=mul_le_mul_of_nonneg_left hscalar hF
  apply hh.trans
  convert hsc using 1 <;> dsimp only [F,E] <;> ring

end SevenEighths.CenteredMomentSecondNonexceptionalCost

end

end OAI

end Source1984

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalAggregate.lean; sha256: 46c96d7a7f74fff3e80da18e475766c365b74f3f340aae23315dc3cfc4f3926e -/
section Source1985
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_harmonic_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,pairWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=>Finset.sum_nonneg (fun U _=>mul_nonneg (Nat.cast_nonneg _) (pairWeight_nonneg _ _)))

theorem part_energy_harmonic_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        pairWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*pairWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          pairWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left (live_harmonic_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_harmonic_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_harmonic_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end SevenEighths.CenteredMomentSecondNonexceptionalAggregate

end

end OAI

end Source1985

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalLiveSource.lean; sha256: 432bdb36a78bc2030daa40fcb4d73f4fba8cc721c267b3192b564c10e231d805 -/
section Source1986
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondNonexceptionalLiveSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem original_nonexceptional_energy (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (B L Cr δ ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hδ:0<δ)(hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀s:Input ι,(∀i,s.lo i=lo i)→(∀i,s.hi i=hi i)→
      s.W₁ 0=0→s.W₂ 0=0→0≤sourceRadius s→sourceRadius s≤Z^B→
    ∀R0 seed:Ideal O,Squarefree seed→seed≠0→
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀(χ₀:RayCharacter)(Q:Ideal O)(m:O),Q≤Ideal.span {(72:O)}→
      m≠0→goodLambda∣m→(2:O)∣m→
    ∀Kphys Tsec ξ:ℝ,0<Kphys→frequencyRadius Tsec Z ξ≤Cr*Z^L→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData≤
      C*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ) := by
  obtain ⟨Ck,hCk,hblock⟩:=actual_canonical_child_cost lo hi W J₁ J₂ B δ hB hδ
  obtain ⟨Cm,hCm,hmass⟩:=source_part_harmonic_bound B L Cr ε hB hL hCr hε
  refine ⟨Ck*Cm,mul_pos hCk hCm,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s hlo hhi hz1 hz2 hH0 hH R0 seed hseed hseed0 S β
  have hg (q:ActiveLabel S β):=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
  have hs (q:ActiveLabel S β):=commonLabels_supported (activeSource S β) _ _ q.property
  choose τ hf using fun (q:ActiveLabel S β) (U:Finset (CommonIndex q.val.1 q.val.2))=>
    exists_exceptional_family s.η q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.1 U
  refine ⟨τ,hf,?_⟩
  intro χ₀ Q m hQ hm hml hm2 Kphys Tsec ξ hKphys hR E₁ E₂ hE₁ hE₂ hleft hright
  let F:=Ck*Z^(2*δ)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
    Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂
  have hF:0≤F:=by
    have hp:=profileCost_nonneg s
    have ht:=heightEnvelope_pos s.t
    have hm1:=profileMoment_nonneg J₁
    have hm2:=profileMoment_nonneg J₂
    have hz:0<Z:=zero_lt_one.trans hZ.1
    dsimp only [F]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hH)
    false s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) (volume s.toData) F
    hKphys hR hH (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))‖/volume s.toData≤F*pairWeight q.val.1 q.val.2:=by
    intro q hq U n
    by_cases hzero:physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))=0
    · rw [hzero,norm_zero,zero_div]
      exact mul_nonneg hF (pairWeight_nonneg _ _)
    · have hh:=hZ.2 Kphys hKphys (fun i=>(n i:ℤ)) s (τ q U) hlo hhi R0 seed
        q.val.1 q.val.2 (hs q).1 (hs q).2 (hg q).2.2.2.1 (hg q).2.2.2.2.1
        ((hg q).2.2.2.2.2.1.trans hH) ((hg q).2.2.2.2.2.2.trans hH) (hg q).2.2.1 U (hf q U)
        hz1 hz2 hH0 hH (frequencyRadius Tsec Z ξ) Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂
        (hleft q hq U n hzero) (hright q hq U n hzero)
      rw [←physicalBlock_active]
      exact hh.trans_eq (by dsimp only [F,pairWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*δ)*Z^ε=Z^(2*δ+ε):=by rw [Real.rpow_add (zero_lt_one.trans hZ.1)]
  dsimp only [F]
  calc
    _=(Ck*Cm)*(Z^(2*δ)*Z^ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]
end SevenEighths.CenteredMomentSecondNonexceptionalLiveSource

end

end OAI

end Source1986

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondLiveSourceDescent.lean; sha256: 802ed267728a6e19592b7095097b85e23ca87e68493d68988d29e19ce84d5d23 -/
section Source1987
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondLiveSourceDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

theorem original_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i,hi i)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving) :=by
  obtain ⟨Cmain,hCmain,hmain⟩:=
    CenteredMomentSecondNonexceptionalLiveSource.original_nonexceptional_energy lo hi W J₁ J₂
      B B 1 δ ε hB hB zero_lt_one hδ hε
  obtain ⟨J,Sprofile,SΦ,hSp,Cexc,Cdiag,Ctail,hCexc,hCdiag,hCtail,hrem⟩:=
    CenteredMomentSecondSourceRemainder.original_source_remainder wlo whi hwlo hwhi
      lo hi hhi W ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sprofile,SΦ,hSp,Cmain,Cexc,Cdiag,Ctail,hCmain,hCexc,hCdiag,hCtail,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hrem⟩:=hrem Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hmain,hrem] with Z hmZ hrZ
  refine ⟨hmZ.1,?_⟩
  intro s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (p.support i hn).1
  have hz1:s.W₁ 0=0:=by rw [hw1];exact hz 0
  have hz2:s.W₂ 0=0:=by rw [hw2];exact hz 1
  obtain ⟨τ,hfamily,hchild⟩:=hmZ.2 s hlo hhis hz1 hz2 hH0 hH R0 seed hseed hseed0
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂
    hleft hright r hX1 hX2 hY1 hY2
  have hn:=hchild χ₀ Q m hQ72 hm hml hm2 Kphys Tsec ξ hKphys
    (by simpa only [one_mul] using hRcap) E₁ E₂ hE₁ hE₂ hleft hright
  have he:=hrZ.2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
    χ₀ m hm hml hm2 Tsec Kphys hKphys hVcap hTcap hnom hR hRcap r hX1 hX2 hY1 hY2
  have ht:‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      ‖partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData+
      ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)‖/volume s.toData:=by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (volume_pos s.toData).le
    have h:=norm_add_le
      (partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
      (sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys-
        partEnergy false s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s))
    simpa only [←add_sub_assoc, add_sub_cancel_left] using h
  exact ht.trans ((add_le_add hn he).trans_eq (by ring))

end SevenEighths.CenteredMomentSecondLiveSourceDescent

end

end OAI

end Source1987

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputReindex.lean; sha256: aefabbfb58e7aa8c0d270fcd660efe611728f4248bb8a2aae9a36149c9b74f8c -/
section Source1988
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputReindex
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _
local instance : DecidableEq (β⊕Fin 2) := Classical.decEq _

def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=>s.slots (e.symm i)
  prime := fun i=>s.prime (e.symm i)
  ν := fun i=>s.ν (e.symm i)
  W := fun i=>s.W (e.symm i)
  lo := fun i=>s.lo (e.symm i)
  hi := fun i=>s.hi (e.symm i)
  P := fun i=>s.P (e.symm i)
  lo_pos := fun i=>s.lo_pos (e.symm i)
  P_pos := fun i=>s.P_pos (e.symm i)
  support := fun i=>s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=>s.M (e.symm i)
  M_ge_one := fun i=>s.M_ge_one (e.symm i)
  coefficient_bound := fun i=>s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=>s.ν_bound (e.symm i)
  W_bound := fun i=>s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le (e.symm i)
  upper_ge := fun i=>s.upper_ge (e.symm i)

def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))

omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl

lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v

lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)

lemma profile_map (e : α≃β) (s : Input α) (R seed : Ideal O) (v : Tuple α) :
    (original (reindex e s) R seed).profile (tupleMap e v) =
      (original s R seed).profile v := by
  simp only [OriginalData.profile,original,reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=>s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))

lemma columns_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).columns=(original s R seed).columns := by
  unfold OriginalData.columns
  change finiteColumns (Fintype.piFinset (reindex e s).pools)=finiteColumns (Fintype.piFinset s.pools)
  rw [←pools_map,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleMap_product e v

lemma coefficient_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).beta=(original s R seed).beta := by
  funext I
  unfold OriginalData.beta finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=>finiteTupleProduct v=I),
    (original (reindex e s) R seed).profile v)=_
  rw [←pools_map,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h => (tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]
  rfl

lemma volume_map (e : α≃β) (s : Input α) : volume (reindex e s)=volume s := by
  simp only [volume,reindex,e.symm.prod_comp]

lemma controls_map (e : α≃β) (s : Input α) :
    (∏i,(reindex e s).M i)=(∏i,s.M i) ∧
    (∏i,(reindex e s).lo i)=(∏i,s.lo i) ∧
    (∏i,(reindex e s).hi i)=(∏i,s.hi i) := by
  simp only [reindex,e.symm.prod_comp,and_self]

lemma sourceRadius_map (e : α≃β) (s : Input α) :
    CenteredMomentOriginalCommonHarmonic.sourceRadius (reindex e s)=
      CenteredMomentOriginalCommonHarmonic.sourceRadius s := by
  simp only [CenteredMomentOriginalCommonHarmonic.sourceRadius,reindex,e.symm.prod_comp]

theorem normalizedGaussSource_map (e : α≃β) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (reindex e s) R seed W K=normalizedGaussSource s R seed W K := by
  unfold normalizedGaussSource
  rw [columns_map,coefficient_map,volume_map]
  rfl

def imageInput (e : α↪β) (T : Finset α) (s : Input T) : Input (T.map e) :=
  reindex (Finset.equivMap e T) s

omit [Fintype α] [Fintype β] in
lemma imageInput_lo (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).lo ((Finset.equivMap e T) i)=s.lo i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_hi (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).hi ((Finset.equivMap e T) i)=s.hi i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_normalized (e : α↪β) (T : Finset α) (s : Input T)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (imageInput e T s) R seed W K=normalizedGaussSource s R seed W K :=
  normalizedGaussSource_map (Finset.equivMap e T) s R seed W K

def allocatedImage (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Input ((liveIndices B.val).map e) :=
  imageInput e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_ranges (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (lo hi : β→ℝ) (hlo : ∀i,s.lo i=lo (e i)) (hhi : ∀i,s.hi i=hi (e i)) :
    (∀j,(allocatedImage e s C R B τ t).lo j=lo j.val) ∧
    (∀j,(allocatedImage e s C R B τ t).hi j=hi j.val) := by
  constructor
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_lo]
    exact hlo i.val
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_hi]
    exact hhi i.val

omit [Fintype β] in
theorem allocatedImage_normalized (e : α↪β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (allocatedImage e s C R B τ t) (R*C) seed W K =
      childNormalizedGaussSource s C R seed B τ t W K :=
  imageInput_normalized e (liveIndices B.val) (child s C R B τ t) (R*C) seed W K

end SevenEighths.CenteredMomentSourceInputReindex

end

end OAI

end Source1988

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondUniformSubsetSource.lean; sha256: 62c37da4359314b756af35deca68c3a97bab5d7767b253de343d8ca07a843acc -/
section Source1989
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondUniformSubsetSource
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

lemma control_mono {wlo whi : ℝ} (p : Profiles wlo whi)
    {S T : Finset (ℕ×ℕ)} (h : S⊆T) : p.control S≤p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (Seminorm.le_def.mp (Finset.sup_mono h) _)
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma moment_mono {j k : ℕ} (h : j≤k) : profileMoment j≤profileMoment k := by
  apply integral_mono (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth j)
    (columnDensity_moments _ logAnnulus_compact logAnnulus_smooth k)
  intro x
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg x]) h) (norm_nonneg _)

omit [DecidableEq ι] in
lemma factor_mono {wlo whi : ℝ} {S T : Finset (ℕ×ℕ)} (hST : S⊆T)
    (s : Input ι) (p : Profiles wlo whi) {j k : ℕ} (hjk : j≤k)
    (Q : Ideal O) {A B : ℝ} (hA : 0≤A) (hAB : A≤B) :
    profileFactor S s p j Q A≤profileFactor T s p k Q B := by
  have hp:=control_mono p hST
  have hpn:=p.control_nonneg S
  have hpn':=p.control_nonneg T
  have hm:=moment_mono hjk
  have hmn:=profileMoment_nonneg j
  have hmn':=profileMoment_nonneg k
  have hπ : (1:ℝ)≤1+2*Real.pi := by linarith [Real.pi_pos]
  have ht : (1:ℝ)≤1+‖s.t‖ := by linarith [norm_nonneg s.t]
  have h4 : 4*j≤4*k := Nat.mul_le_mul_left _ hjk
  have h2 : 2*j≤2*k := Nat.mul_le_mul_left _ hjk
  have hπpow:=pow_le_pow_right₀ hπ h4
  have htpow:=pow_le_pow_right₀ ht h2
  have hB : 0≤B := hA.trans hAB
  unfold profileFactor
  change A*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*j)*
    p.control S^2*(1+‖s.t‖)^(2*j)*slotControl s.toData^2*frozenProfile s^2*profileMoment j^2 ≤ _
  change _ ≤ B*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*k)*
    p.control T^2*(1+‖s.t‖)^(2*k)*slotControl s.toData^2*frozenProfile s^2*profileMoment k^2
  gcongr

theorem original_subsets_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:T,hi i.val)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  have hall (T : Finset ι) := CenteredMomentSecondLiveSourceDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:T=>lo i.val) (fun i:T=>hi i.val) (fun i=>hhi i.val)
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:Finset ι,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:Finset ι,Cm T
  let Ce0 : ℝ := 1+∑T:Finset ι,Ce T
  let Cd0 : ℝ := 1+∑T:Finset ι,Cd T
  let Ct0 : ℝ := 1+∑T:Finset ι,Ct T
  have sum_pos (f : Finset ι→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:Finset ι,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset ι)))=>hf T)
    linarith
  have sum_le (f : Finset ι→ℝ) (hf : ∀T,0≤f T) (T : Finset ι) : f T≤1+∑U:Finset ι,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset (Finset ι)))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨∅,Finset.mem_univ _,hSp ∅⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:Finset ι,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:Finset ι,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=(hZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcm:=sum_le Cm (fun T=>(hCm T).le) T
  have hce:=sum_le Ce hCe T
  have hcd:=sum_le Cd (fun T=>(hCd T).le) T
  have hct:=sum_le Ct (fun T=>(hCt T).le) T
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (sum_le K (fun T=>(hK T).le) T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have he:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hCm0 : 0≤Cm0 := (sum_pos Cm (fun T=>(hCm T).le)).le
  have hCe0 : 0≤Ce0 := (sum_pos Ce hCe).le
  have hCd0 : 0≤Cd0 := (sum_pos Cd (fun T=>(hCd T).le)).le
  have hCt0 : 0≤Ct0 := (sum_pos Ct (fun T=>(hCt T).le)).le
  have hprodhi : 0≤∏i:T,hi i.val := Finset.prod_nonneg (fun i _=>hhi i.val)
  have hprodlo : 0≤∏i:T,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr

open CenteredMomentSourceInputReindex CenteredMomentAmplificationChildInput CenteredMomentCommonProfile

def nestedImage (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) :=
  allocatedImage (⟨Subtype.val,Subtype.val_injective⟩ : liveIndices B.val ↪ ι)
    (child s C R B τ t) (Q^k) (R*C) Bp υ v

omit [DecidableEq ι] in
lemma nestedImage_ranges (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) (lo hi : ι→ℝ)
    (hlo : ∀i,s.lo i=lo i) (hhi : ∀i,s.hi i=hi i) :
    (∀j,(nestedImage s C R B τ t Q k Bp υ v).lo j=lo j.val) ∧
    (∀j,(nestedImage s C R B τ t Q k Bp υ v).hi j=hi j.val) :=
  allocatedImage_ranges _ _ _ _ _ _ _ lo hi (fun i=>hlo i.val) (fun i=>hhi i.val)

omit [DecidableEq ι] in
lemma nestedImage_source (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (nestedImage s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed W K =
      childNormalizedGaussSource (child s C R B τ t) (Q^k) (R*C) seed Bp υ v W K :=
  allocatedImage_normalized _ _ _ _ _ _ _ _ _ _

omit [DecidableEq ι] in
lemma nestedImage_data (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) :
    (nestedImage s C R B τ t Q k Bp υ v).η=υ ∧
    (nestedImage s C R B τ t Q k Bp υ v).t=v ∧
    (nestedImage s C R B τ t Q k Bp υ v).m=
      fixedBadMask*idealGenerator ((R*C)*(Q^k)) := ⟨rfl,rfl,rfl⟩

end SevenEighths.CenteredMomentSecondUniformSubsetSource

end

end OAI

end Source1989

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstChildProfileControl.lean; sha256: e9043102cb911a11838130508bd82adaee2b4b0f852217aa7003854aa868bcba -/
section Source1990
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (s : Input ι) : ℝ := ∏ i,s.M i

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤mass s :=
  Finset.one_le_prod₀ (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : mass (child s C R B τ t)≤mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod₀ (fun i (_:i∈Finset.univ)=>by positivity)
    (fun i (_:i∈Finset.univ)=>hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert h' using 1 <;> simp only [profileCost,Data.profileFactor,mass]; ring

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
theorem twice_controls (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileCost d≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*mass s^2)*mass d^2 ∧
    slotControl d.toData^2*frozenProfile d^2≤
      ((128*b)^N)^2*(b^N)^2*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact ⟨profile_cost_bound d N b (mass s) hb hu hn hm,
    exceptional_slot_bound d N b (mass s) hb hu hn hm⟩

def exceptionalConstant (N : ℕ) (b : ℝ) (J : ℕ) (Q : Ideal O) (K : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2*
    ((128*b)^N)^2*(b^N)^2

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileFactor S s p J Q K≤exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert hh using 1 <;> simp only [profileFactor,exceptionalConstant,F] <;> ring

omit [DecidableEq ι] in
theorem twice_exceptional_factor {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Qfix : Ideal O) (K : ℝ)
    (hK : 0≤K) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileFactor S d p J Qfix K≤exceptionalConstant N b J Qfix K*
      p.control S^2*(1+‖v‖)^(2*J)*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact exceptional_factor_bound S p J Qfix K hK d N b (mass s) hb hu hn hm

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI

end Source1990

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondChildPowerBudget.lean; sha256: 163910f0e016b4ae4e15c18dd1247e398a35300d0d6cb1b6b3e9859f3b38720e -/
section Source1991
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondChildPowerBudget
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEligibleEnergy
open CenteredMomentFirstChildProfileControl CenteredMomentCommonRadialPointwise
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma endpoint_product (s : Input ι) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) :
    0≤∏i,s.hi i ∧ (∏i,s.hi i)≤b^N := by
  refine ⟨Finset.prod_nonneg (fun i _=>hhi i),?_⟩
  calc
    _≤∏i:ι,b:=Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>(s.upper_ge i).trans hu)
    _=b^Fintype.card ι:=by simp
    _≤b^N:=pow_le_pow_right₀ hb hc

omit [DecidableEq ι] in
lemma main_cost (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) :
    profileCost s*sourceRadius s≤
      (2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)*
        CenteredMomentAmplificationChildInput.volume s*mass s^2 := by
  have hg:=CenteredMomentAmplificationChildSourceCaps.radius_le N b b₁ b₂ hb
    (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc hhi
    (fun i=>(s.upper_ge i).trans hu) hs₁ hs₂ hb₁ hb₂
  have hp:=profile_cost_bound s N b A hb hu hc hm
  have he : max 1 s.b₁*max 1 s.b₂≤b₁*b₂ :=
    mul_le_mul (max_le h₁ hb₁) (max_le h₂ hb₂) (by positivity) (by linarith)
  have hp' : profileCost s≤(2*(b₁*b₂)*b^N*A^2)*mass s^2 := by
    apply hp.trans
    gcongr
  have hh:=mul_le_mul hp' hg.2 hg.1 (by positivity)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma diagonal_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) (N : ℕ) (b whi ε : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (hhi : ∀i,0≤s.hi i) (hε : 0≤ε) :
    (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)≤
    (4*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      (1+b^N*whi^2)^(1+ε))*mass s^2 := by
  have hp:=endpoint_product s N b hb hu hc hhi
  have hx : 1+(∏i,s.hi i)*whi*whi≤1+b^N*whi^2 := by nlinarith [mul_le_mul_of_nonneg_right hp.2 (sq_nonneg whi)]
  have hx0 : 0≤1+(∏i,s.hi i)*whi*whi := by nlinarith [mul_nonneg hp.1 (sq_nonneg whi)]
  have h:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx (by linarith : 0≤1+ε))
    (sq_nonneg (2*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*mass s))
  convert h using 1 ; ring

omit [DecidableEq ι] in
lemma tail_cost (s : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    plainControl s W₁ W₂^2=
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*mass s^2 := by
  unfold plainControl mass
  ring

def powers (ε : ℝ) : Fin 4→ℝ := ![1,1/3,ε,0]

lemma powers_nonneg (ε : ℝ) (hε : 0≤ε) : ∀j,0≤powers ε j := by
  intro j
  fin_cases j <;> simp [powers,hε]

def coefficients {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ) : Fin 4→ℝ :=
  ![a 0*(2*(b₁*b₂)*b^N*A^2)*(b^N*b₁*b₂)/seedNorm,
    a 1*exceptionalConstant N b J Q K*p.control S^2*(1+‖t‖)^(2*J)*A^4/seedNorm,
    a 2*4*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*(1+b^N*whi^2)^(1+ε)/seedNorm,
    a 3*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2]

lemma coefficients_nonneg {wlo whi : ℝ} (N : ℕ) (b b₁ b₂ A : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K t ε seedNorm : ℝ) (a : Fin 4→ℝ)
    (hb : 0≤b) (h₁ : 0≤b₁) (h₂ : 0≤b₂) (hK : 0≤K)
    (hs : 0≤seedNorm) (ha : ∀j,0≤a j) :
    ∀j,0≤coefficients N b b₁ b₂ A S p J Q K t ε seedNorm a j := by
  have h0:=ha 0
  have h1:=ha 1
  have h2:=ha 2
  have h3:=ha 3
  intro j
  fin_cases j <;> dsimp [coefficients,exceptionalConstant] <;> positivity

def sourceCost {wlo whi : ℝ} (s : Input ι) (S : Finset (ℕ×ℕ))
    (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ)
    (a : Fin 4→ℝ) : ℝ :=
    a 0*profileCost s*sourceRadius s/seedNorm+
    a 1*profileFactor S s p J Q K*(CenteredMomentAmplificationChildInput.volume s)^(1/3:ℝ)/seedNorm+
    a 2*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*mass s)^2*
      (1+(∏i,s.hi i)*whi*whi)^(1+ε)*(CenteredMomentAmplificationChildInput.volume s)^ε/seedNorm+
    a 3*plainControl s (p.profile 0) (p.profile 1)^2

omit [DecidableEq ι] in
theorem source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ A : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (hm : mass s≤A) (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε)
    (hs : 0≤seedNorm) (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    sourceCost s S p J Q K ε seedNorm a ≤
      (∑j,coefficients N b b₁ b₂ A S p J Q K s.t ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  unfold sourceCost
  have hv := (CenteredMomentAmplificationChildInput.volume_pos s).le
  have hmain:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (main_cost s N b b₁ b₂ A hb h₁ h₂ hu hc hhi hs₁ hs₂ hb₁ hb₂ hm) (ha 0)) hs
  have hexc:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exceptional_factor_bound S p J Q K hK s N b A hb hu hc hm) (ha 1))
      (Real.rpow_nonneg hv (1/3:ℝ))) hs
  have hdiag:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (diagonal_cost s (p.profile 0) (p.profile 1) N b whi ε hb hu hc hhi hε) (ha 2))
      (Real.rpow_nonneg hv ε)) hs
  have htail:=congrArg (fun x:ℝ=>a 3*x) (tail_cost s (p.profile 0) (p.profile 1))
  have hh:=add_le_add (add_le_add (add_le_add hmain hexc) hdiag) (le_of_eq htail)
  convert hh using 1 <;>
    (try simp only [coefficients,powers,Fin.sum_univ_succ,Fin.sum_univ_zero,
      Matrix.cons_val_zero,Matrix.cons_val_succ,
      Real.rpow_one,Real.rpow_zero]) <;> ring

omit [DecidableEq ι] in
theorem twice_source_rhs {wlo whi : ℝ} (s : Input ι) (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hu : s.upper≤b)
    (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂)
    (C R : Ideal O) (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (P : Ideal O) (k : ℕ)
    (Bp : CenteredMomentCommonAllocationSum.actualAllocations
      (CenteredMomentAmplificationChildInput.child s C R B τ t).pools (P^k))
    (υ : Character) (v : ℝ)
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O)
    (K ε seedNorm : ℝ) (hK : 0≤K) (hε : 0≤ε) (hs : 0≤seedNorm)
    (a : Fin 4→ℝ) (ha : ∀j,0≤a j) :
    let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v;
    sourceCost d S p J Q K ε seedNorm a≤
      (∑j,coefficients N b b₁ b₂ (mass s) S p J Q K v ε seedNorm a j*
        (CenteredMomentAmplificationChildInput.volume d)^(powers ε j))*mass d^2 := by
  let d:=CenteredMomentAmplificationChildSourceCaps.twiceChild s C R B τ t P k Bp υ v
  have hm : mass d≤mass s :=
    (child_mass (CenteredMomentAmplificationChildInput.child s C R B τ t) (P^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact source_rhs d N b b₁ b₂ (mass s) hb h₁ h₂ hu hn
    (fun i=>hhi i.val.val) hs₁ hs₂ hb₁ hb₂ hm S p J Q K ε seedNorm hK hε hs a ha

end SevenEighths.CenteredMomentSecondChildPowerBudget

end

end OAI

end Source1991

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourcePowerDescent.lean; sha256: 3d5fcb585cc58aae60a1305b94b07dd2f4a8510c5c16950284be6b81222523f6 -/
section Source1992
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

def physicalFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  ![Cmain*Z^(2*δ+ε)*ηNorm*Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*
      profileMoment J₁*profileMoment J₂,
    Cexc*Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*K^(5/6:ℝ)*
      (loProduct*wlo*wlo)^(-2/3:ℝ),
    Cdiag*K*‖paperRadialFourier W 0‖,
    Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*K*Z^(-saving)]

lemma physicalFactors_nonneg (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ))
    (hm : 0≤Cmain) (he : 0≤Cexc) (hd : 0≤Cdiag) (ht : 0≤Ctail)
    (hZ : 0≤Z) (hK : 0≤K) (hη : 0≤ηNorm) (hl : 0≤loProduct) :
    ∀j,0≤physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
      loProduct wlo J₁ J₂ SΦ W j := by
  have hp1:=profileMoment_nonneg J₁
  have hp2:=profileMoment_nonneg J₂
  have hheight:=(heightEnvelope_pos t).le
  have hlo : 0≤loProduct*wlo*wlo := by nlinarith [mul_nonneg hl (sq_nonneg wlo)]
  have hs : 0≤SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  intro j
  fin_cases j <;> dsimp [physicalFactors] <;> positivity

theorem original_subsets_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondUniformSubsetSource.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI

end Source1992

/- Original source: OAI/NumberTheory/DirichletL/Moments/SourceInputTailSeed.lean; sha256: 349b5bc5d72f2fb1e81c6a5f5717fdae8d9b83e46e2c9bb4959146f56b604d2b -/
section Source1993
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma paid_seed_power (Z Bseed saving seedNorm : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

lemma paid_seed_term (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

omit [DecidableEq ι] in
theorem second_input_tail_seed (hi : ι→ℝ) (wlo whi B Bseed ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B) (hξ : 0<ξ) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(W₁ W₂ : 𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),
      seed≠0→(seed.absNorm:ℝ)≤Z^Bseed→
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        Z^(-saving)/(seed.absNorm:ℝ) := by
  obtain ⟨SΦ,C,hC,hbound⟩ := second_input_tail_arbitrary_saving hi wlo whi B ξ
    (saving+Bseed) hhi hwlo hwhi hB hξ
  refine ⟨SΦ,C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hseed hseedcap hK hV hT hnom
  have hsn : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed)
  exact (hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hV hT hnom).trans
    (paid_seed_term Z Bseed saving (seed.absNorm:ℝ) _ (zero_lt_one.trans hz.1) hsn hseedcap
      (by positivity))

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI

end Source1993

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondSourceSeededPowerDescent.lean; sha256: d5eb398b9c52024f20efa103418c39595c70704819013ca2acbb2c2bb6211a24 -/
section Source1994
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed

def seededFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo seedNorm : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  let a:=physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W
  ![a 0,a 1,a 2,a 3/seedNorm]

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤s.b₁ → 0≤s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondUniformSubsetSource.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondSourceSeededPowerDescent

end

end OAI

end Source1994

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonLiveFrozen.lean; sha256: da5400d8d8f74e964bbdd532e08aac66bfaef4271a727848318afbae13bd4970 -/
section Source1995
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonLiveFrozen
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
open CenteredMomentCommonRadialPointwise CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSourceNormalization CenteredMomentSecondLiveEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma source_mask_energy (keep:O→Prop) (Q:Finset (Ideal O)) (C L:Ideal O)
    (c f:Ideal O→ℂ) (W:𝓢(ℝ,ℂ)) (K:ℝ):
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I ∧ L∣I then c I else 0) f W K =
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I then c I else 0)
      (fun I=>(if L∣I then 1 else 0)*f I) W K := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem original_source_weighted (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
          energy (commonData s C R B) r L := by
  have hh:=normalized_restricted_child_energy s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I)
    r.keep r.profile r.scale r.scale_pos r.nonneg
  simp_rw [live_divisor_energy] at hh
  dsimp only [sourceEnergy]
  rw [source_mask_energy]
  apply hh.trans_eq
  apply congrArg (fun x:ℝ=>((actualAllocations s.pools C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  exact congrArg (fun x:ℝ=>(‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*x)
    (live_source_eq s r C R L B)

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData s C R b).toSource.active L,
        childEnergy (commonData s C R b) r L a≤E) →
      sourceEnergy s r C hC R seed L≤C0*Z^δ*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L) := by
  obtain ⟨C₁,hC₁,hchild⟩:=CenteredMomentRadialPointwiseUniform.actual_uniform_divisor lo hi B (δ/2) hB (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩:=card_squared_subpower (ι:=ι) B (δ/2) hB (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC:0<(Ideal.absNorm C:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL:0<(Ideal.absNorm L:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hz:0<Z:=zero_lt_one.trans hZ
  have hprof:=s.toData.profile_nonneg
  have heach (b:actualAllocations s.pools C) (hlive:frozenCoefficient b.val C R s.ν s.W s.P≠0):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b hlive)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_weighted s r C hC R seed L hseed).trans
    unfold commonCost
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _≤∑b:actualAllocations s.pools C,
          (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(C.absNorm:ℝ))*
            (C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm:ℝ)):=by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hzero:frozenCoefficient b.val C R s.ν s.W s.P=0
        · simp only [hzero,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul]
          positivity
        · have hcost:=frozen_normalized_cost (ι:=ι) b.val (alloc_ne s C b) C R hC.1
            (Finset.mem_filter.mp b.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound
            s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
          exact mul_le_mul hcost (heach b hzero)
            (CenteredMomentRadialEligibleEnergy.energy_nonneg _ _ _) (by positivity)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
  apply hh.trans
  have hc2:=hcount s C hC.1 Z hZ hNC
  calc
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=by
      unfold commonCost profileCost
      ring
    _≤(C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=
      mul_le_mul_of_nonneg_right hc2 (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (profileCost_nonneg s) hE)) (mul_nonneg hnC.le hnL.le))
    _=_:=by
      have hp:Z^(δ/2)*Z^(δ/2)=Z^δ:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=(C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm L):=by ring
        _=_:=by rw [hp]

end SevenEighths.CenteredMomentCommonLiveFrozen

end

end OAI

end Source1995

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonLiveHeight.lean; sha256: 4db7620beba8f719cd190a1e5450f59ed65a998adc4bec7a818bed6d0122078d -/
section Source1996
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLiveHeight
open HeckeFamily CenteredMomentCommonRadialSource CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceLiveColumn
 theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  obtain ⟨C0,hC0,hbound⟩:=CenteredMomentCommonLiveFrozen.actual_common_source_pointwise lo hi B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s hlo hhi r C hC R seed L hs hL E Z hE hZ hNC hNL J τ v hc
  have hh:=hbound (withHeight s τ v) hlo hhi r C hC R seed L hs hL
    (E*(1+‖v‖)^(2*J)) Z (mul_nonneg hE (by positivity)) hZ hNC hNL hc
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  unfold sourceEnergy at hh
  have hmul:=(div_le_iff₀ hraw).mp hh
  apply hmul.trans_eq
  change (C0*Z^δ*(profileCost s*(E*(1+‖v‖)^(2*J)))/
      ((Ideal.absNorm C:ℝ)*Ideal.absNorm L))*(s.X₁*s.X₂*∏i,s.P i)=_
  unfold envelope
  ring

end SevenEighths.CenteredMomentCommonLiveHeight

end

end OAI

end Source1996

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenSupported.lean; sha256: 18b65a009ff1f86477af4a1f26bfe2e64345ac798a6cb09470a58a6ab082d5a0 -/
section Source1997
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenSupported
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound CenteredMomentSecondDivisorSupport CenteredMomentSourceRow
open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSecondOriginalChildren
open CenteredMomentSecondSupportedChildren CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _
theorem actual_block_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
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
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O) (ρ x:O→ℝ) (X Y:ℝ),0<X → 0<Y →
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
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
  obtain ⟨Ce,hCe,hsource⟩:=CenteredMomentCommonLiveHeight.actual_height_envelope lo hi B δ hB hδ
  obtain ⟨C0,hC0,hkernel⟩:=actual_block_from_supported_envelopes W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro r hr η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcore (G:Ideal O) (E:ℝ) (hE:0≤E):0≤core s G Ce Z δ E:=by
    unfold core
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
      (mul_nonneg (profileCost_nonneg s) hE))
      (mul_nonneg (mul_nonneg s.X₁_pos.le s.X₂_pos.le) (Finset.prod_nonneg (fun i _=>(s.P_pos i).le)))) (Nat.cast_nonneg _)
  apply hZ.2 r hr η τ t S β C D hC hD hCD U hτ Hsource hβ hn R rows ρ x X Y hX hY Q m χ₀ hQ hmLam hm2
    hrows Φ H hH hΦ hmajor (core s C Ce Z δ E₁) (core s D Ce Z δ E₂)
    (hcore C E₁ hE₁) (hcore D E₂ hE₂)
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) C hC R0 seed L hsC hsf
      E₁ Z hE₁ hZ.1 hnC hNL J₁ (τ χ) v (hleft L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh
  · intro L hL hcap hsf χ v
    have hNL: (Ideal.absNorm L:ℝ)≤Z^B:=hcap.trans hn
    have hh:=hsource s hlo hhi (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) D hD R0 seed L hsD hsf
      E₂ Z hE₂ hZ.1 hnD hNL J₂ (τ χ) v (hright L hL hcap hsf χ v)
    simpa only [envelope_eq_core,sourceRadial,S,β,A] using hh

end SevenEighths.CenteredMomentSecondFrozenSupported

end

end OAI

end Source1997

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenPhysical.lean; sha256: 278af42d592331bb3da3640c652d1349c98ed07523f4d8103d58a988daf8343e -/
section Source1998
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenPhysical
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
open CenteredMomentSecondNonexceptionalPhysical CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
theorem actual_physical_from_supported_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
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
      ∀Hsource:ℝ,(∀I,β I≠0→(I.absNorm:ℝ)≤Hsource) →
      Hsource/(D.absNorm:ℝ)≤Z^B →
      ∀(R:ℝ) (rows:Finset O),
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀(Φ:𝓢(ℝ,ℂ)) (H:ℝ),∀hH:0<H,
      ∀hΦ:(∀z:O,0≤(Φ (normValue z/H)).re), (∀z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (sourceRadial (nonexceptional η χ Q m A) Φ H hH hΦ) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay := by
  obtain ⟨C0,Ce,hC0,hCe,hkernel⟩:=CenteredMomentSecondFrozenSupported.actual_block_from_supported_children lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hkernel] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r η τ t s hlo hhi R0 seed S β C D hC hD hsC hsD hnC hnD hCD U A hτ Hsource hβ hn
    R rows Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hr:0<r:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hpow:0<(1+r)^decay:=pow_pos (by linarith) _
  have hh:=hZ.2 r hr η τ t s hlo hhi R0 seed C D hC hD hsC hsD hnC hnD hCD U hτ Hsource hβ hn
    R rows (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
    Q m χ₀ hQ hmLam hm2 hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  change (1+r)^decay*‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  rw [paired_core_budget s C D hC hD Ce Z δ E₁ E₂ t hCe.le
    (zero_lt_one.trans hZ.1).le hE₁ hE₂ J₁ J₂] at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar;positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  have hnrows:∀z∈rows,z≠0:=fun z hz=>(hrows z hz).1
  have hp:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)
  have hphys:‖physicalBlock η t S β C D hC hD U R rows W Kphys n‖=
      outerScalar C D Kphys n*normalizer C D U*
        ‖normalizedBlock η t S β C D hC hD U R rows W Kphys n‖:=by
    rw [physicalBlock_eq η t S β C D hC hD U R rows hnrows W Kphys hKphys n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  rw [hphys]
  apply (div_le_iff₀ (volume_pos s.toData)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpow).mpr
  have hzz:Z^(2*δ)=Z^δ*Z^δ:=by
    rw [show 2*δ=δ+δ by ring,Real.rpow_add (zero_lt_one.trans hZ.1)]
  rw [hzz]
  convert hp using 1 <;> ring

end SevenEighths.CenteredMomentSecondFrozenPhysical

end

end OAI

end Source1998

/- Original source: OAI/NumberTheory/DirichletL/Moments/SecondFrozenChosen.lean; sha256: a08c79c63143cd230929518686a386c5e376d20e8ec89fb516d1ad078330f845 -/
section Source1999
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenChosen
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
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentSecondOriginalChildren CenteredMomentSecondSupportedChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondPhysicalCost CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

def canonicalRadial (τ:Character)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)
theorem actual_canonical_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay :=by
  obtain ⟨C0,Ce,hC0,hCe,hbound⟩:=
    CenteredMomentSecondFrozenPhysical.actual_physical_from_supported_children
      lo hi W decay J₁ J₂ B δ hB hδ
  refine ⟨C0,Ce,hC0,hCe,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Kphys hKphys n r s τ hlo hhi R0 seed S β C D hC hD hsC hsD hNC hND hCD U hf
    hz1 hz2 hH R Q m χ₀ hQ hm hml hm2 E₁ E₂ hE₁ hE₂ hleft hright
  let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
  let rows:=partRows false s.η χ₀ Q m C D U R
  have hβ:∀I:Ideal O,β I≠0→(I.absNorm:ℝ)≤sourceRadius s:=by
    intro I hi
    exact (original_column_norm s R0 seed I hz1 hz2 hi).2
  have hHD:sourceRadius s/(D.absNorm:ℝ)≤Z^B:=by
    have hDN:1≤(D.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
    by_cases hp:0≤sourceRadius s
    · exact (div_le_self hp hDN).trans hH
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (Nat.cast_nonneg _)).trans
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hrows:∀z∈dyadicRows rows n,nonexceptional s.η χ₀ Q m A z:=by
    intro z hz
    have hh:=Finset.mem_filter.mp ((dyadicRows_subset rows n) hz)
    simpa only [rows,partRows,Bool.false_eq_true,ite_false] using hh.2
  have hmajor:∀z∈dyadicRows rows n,1≤(ballProfile (normValue z/dyadicScale (n 1))).re:=by
    intro z hz
    have hb:=ballProfile_majorizes (dyadicScale (n 1)) (dyadicScale_pos _) z
      (dyadicRows_norm rows n z hz).2.le
    simpa only [normValue_eq_embedding] using hb
  have hleft':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=>ballProfile_nonneg _)) L a≤E₁*(1+‖v‖)^(2*J₁):=by
    intro L hL hLN hsf χ v b hlive a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hleft L hL hLN hsf χ v b hlive a ha
  have hright':∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),
      (L.absNorm:ℝ)≤sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
      childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
        (sourceRadial (nonexceptional s.η χ Q m A) ballProfile (dyadicScale (n 1))
          (dyadicScale_pos _) (fun z=>ballProfile_nonneg _)) L a≤E₂*(1+‖v‖)^(2*J₂):=by
    intro L hL hLN hsf χ v b hlive a ha
    rw [sourceRadial_eq_canonical hf χ Q m hm hml hm2 n]
    exact hright L hL hLN hsf χ v b hlive a ha
  have hh:=hZ.2 Kphys hKphys n s.η τ s.t s hlo hhi R0 seed C D hC hD hsC hsD hNC hND hCD U
    hf.height_eq (sourceRadius s) hβ hHD R (dyadicRows rows n) Q m χ₀ hQ hml hm2 hrows
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun z=>ballProfile_nonneg _) hmajor
    E₁ E₂ hE₁ hE₂ hleft' hright'
  rwa [←physicalBlock_dyadic_rows] at hh

end SevenEighths.CenteredMomentSecondFrozenChosen

end

end OAI

end Source1999
