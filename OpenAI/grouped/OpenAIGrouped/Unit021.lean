import OpenAIGrouped.Unit014
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit020
import OpenAIGrouped.Unit007
import Mathlib.Analysis.MellinInversion
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit018
import OpenAIGrouped.Unit016
import Mathlib.RingTheory.Radical.Basic
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit009
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OpenAIGrouped.Unit010

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonRadiusSaving.lean; sha256: ee625794b23b08fd5094d628d59c167d10cea9a00f2651db76a513d957e6e239 -/
section Source840
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

def errorLoss (sigma : ℝ) (k : ℕ) : ℝ :=
  if k=1 then 5*sigma/6 else if k=6 then 3*sigma/2 else 23*sigma/18

theorem error_penalty_refined (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0+5*sigma/6≤errorLoss sigma k := by
  have hs : 0≤sigma := by linarith
  rcases hk with rfl|rfl|rfl
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_one,one_mul]
    have hm : max (l/3-l) 0=0 := max_eq_right (by linarith)
    rw [hm,zero_add]
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat,sub_zero]
    have hm : max (6*l/3) 0≤2*sigma/3 := max_le (by linarith) (by linarith)
    linarith
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat]
    have hm : max (7*l/3-l) 0≤4*sigma/9 := max_le (by linarith) (by linarith)
    linarith

theorem errorLoss_le (sigma : ℝ) (hs : 0≤sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7) : errorLoss sigma k≤3*sigma/2 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [errorLoss,ite_true,ite_false] <;> linarith

theorem error_saving_refined (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_refined l sigma hl hu k hk]

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem common_gain_width (d x c w wo sigma delta reserve branch : ℝ)
    (hs : 0≤sigma) (hd : 0≤delta) (hr : 0≤reserve) (hb : 1≤branch)
    (hx : -delta≤x) :
    0≤x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve ∧
    (d+x)-c-2*w+wo+sigma≤
      x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve := by
  have h0 := le_max_right (d-c-2*w+wo) (0:ℝ)
  have h1 := le_max_left (d-c-2*w+wo) (0:ℝ)
  constructor <;> nlinarith

theorem saving_power_factor (Z F c w sigma delta reserve : ℝ) (hZ : 1≤Z)
    (hF : 2*(c+w)/3-3*sigma/2-5*(delta+reserve)/6≤F) :
    Z^(-F)≤Z^(-2*(c+w)/3+3*sigma/2+5*(delta+reserve)/6) := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem canonical_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    let B := c+d-2*p-R
    0≤c ∧ 0≤q ∧ 0≤B ∧ 3*c-5*d≤6*B+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hh := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hh
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have h0 := le_max_right (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h1 := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h2 := le_max_right (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  exact ⟨hc,hq.1,by linarith,by linarith [hq.2]⟩

theorem actual_main_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_common_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_main_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) (hs : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))≤
      Z^(-2*c/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_main_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)≤
      Z^(-2*(c+errorRemoval p0 Z k)/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_error_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve
    hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

open CenteredMomentFirstScale

theorem actual_common_radius_widths (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec)
    (hxi : 0≤xi) (hs : 0≤sigma) (hr : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let delta := frequencyLoss Z Csec xi
    let gm := Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j
    (0≤gm ∧ d+K0-j-c+sigma≤gm) ∧
    ∀p : O,∀k : ℕ,
      let ge := Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j
      0≤ge ∧ d+K0-j-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ge := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hd := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have hx : -frequencyLoss Z Csec xi≤nominalLog I J E K X Z-Real.logb Z (dyadicScale n) := by
    linarith
  constructor
  · rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) 0 0 sigma
      (frequencyLoss Z Csec xi) reserve 2 hs hd hr (by norm_num) hx
    simp only [mul_zero,sub_zero,add_zero] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩
  · intro p k
    rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
      sigma (frequencyLoss Z Csec xi) reserve 1 hs hd hr (by norm_num) hx
    simp only [one_mul] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI

end Source840

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalLedger.lean; sha256: 2981fd0f3d52384bca643de0408059fbb662a4c36e3d134bbfe03bad08fecd35 -/
section Source841
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstPhysicalLedger
open CenteredMomentFirstScale CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstExtractedLedger CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

theorem nominal_log (I J E : Ideal O) (hE : E≠0)
    (Z H X : ℝ) (hH : 0<H) (hX : 0<X) :
    Real.logb Z (firstNominalScale I J E H X)=
      2*Real.logb Z X-Real.logb Z ((commonPart I J).absNorm:ℝ)-
        Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)+
        Real.logb Z (E.absNorm:ℝ)-Real.logb Z H := by
  have hc:=norm_pos _ (commonPart_ne_zero I J)
  have hd:=norm_pos _ (commonPart_ne_zero J I)
  have he:=norm_pos E hE
  have hr:=active_norm_pos I J
  unfold firstNominalScale
  rw [Real.logb_div (mul_pos (mul_pos he hr) (sq_pos_of_pos hX)).ne'
      (mul_pos (mul_pos hH hc) hd).ne',
    Real.logb_mul (mul_pos he hr).ne' (sq_pos_of_pos hX).ne',
    Real.logb_mul he.ne' hr.ne',Real.logb_pow,
    Real.logb_mul (mul_pos hH hc).ne' hd.ne',Real.logb_mul hH.ne' hc.ne']
  push_cast
  ring

theorem retained_nominal_frequency (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n)≤
      Real.logb Z (firstNominalScale I J E H X)+frequencyLoss Z Csec ξ := by
  apply retained_first_dyad_enclosure Tsec Z Csec _ ξ hZ hC _ n hn
  simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (firstNominalScale_pos I J E hE H X hH hX)] using hsec

theorem retained_deficit (I J E : Ideal O) (hE : E≠0)
    (Z H X Tsec Csec ξ : ℝ) (hZ : 1<Z) (hH : 0<H) (hX : 0<X)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec ξ≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+
        Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n) := by
  linarith [retained_nominal_frequency I J E hE Z H X Tsec Csec ξ hZ hH hX hC hsec n hn]

theorem frequency_loss_eventually (Csec ξ : ℝ) (hC : 0<Csec) (hξ : 0<ξ) :
    ∃Z₀ : ℝ,1<Z₀ ∧ ∀Z : ℝ,Z₀≤Z → 1<Z ∧ frequencyLoss Z Csec ξ<ξ := by
  have hg := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ξ/4 by linarith))) (4*Csec)
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (hg.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max Z₀ 2,by linarith [le_max_right Z₀ (2:ℝ)],?_⟩
  intro Z hZ
  obtain ⟨hb,hZ1⟩:=hZ₀ Z ((le_max_left Z₀ 2).trans hZ)
  have hl:=Real.logb_le_logb_of_le hZ1 (show 0<4*Csec by positivity) hb
  rw [Real.logb_rpow (zero_lt_one.trans hZ1) hZ1.ne'] at hl
  exact ⟨hZ1,by unfold frequencyLoss;linarith⟩

theorem actual_first_saving (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (hE : E≠0) (Z H X Tsec Csec ξ q w wo ell σ branch : ℝ)
    (hZ : 1<Z) (hH : 0<H) (hX : 0<X) (hC : 1≤Csec)
    (hξ : 0≤ξ) (hsec : Tsec≤Csec*firstNominalScale I J E H X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n)
    (hq : 0≤q) (hw : 0≤w) (hwo : 0≤wo) (hell : 0≤ell) (hσ : 0≤σ)
    (hbranch : branch≤2) (hwσ : w≤7*σ/3) :
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let e:=Real.logb Z (E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n)
    2*(c+w)/3-3*σ-5*(frequencyLoss Z Csec ξ)/6≤
      firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
        (max (D₀-c-2*w+wo) 0+branch*σ) ell := by
  dsimp only
  have hRn : (1:ℝ)≤((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hEn : (1:ℝ)≤(E.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hR:=Real.logb_nonneg hZ hRn
  have he:=Real.logb_nonneg hZ hEn
  apply actual_extracted_first_saving I J hI hJ Z hZ _ _ _ _ _ _ _ _ hw
    (by linarith) hwo hσ (frequencyLoss_nonneg Z Csec ξ hZ hC hξ)
    (by linarith) (retained_deficit I J E hE Z H X Tsec Csec ξ hZ hH hX
      (by linarith) hsec n hn) _ hell hwσ
  nlinarith

end SevenEighths.CenteredMomentFirstPhysicalLedger

end

end OAI

end Source841

/- Original source: OAI/NumberTheory/DirichletL/Moments/AmplifiedChildWidth.lean; sha256: 1d9abea4ca98c7266e72b50c7e3ec32b98d2a70ad21e36af6a66763457749581 -/
section Source842
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem modulus_pos (η:Character) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot
theorem span_pos (m:O)(hm:m≠0) : 0<((Ideal.span {m}).absNorm:ℝ) :=
  norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hm)

theorem canonical_modulus_log (η ρ:Character)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem radical_error_log_bound (ρ η:Character)(χ:RayCharacter)(m p:O)
    (hm:m≠0)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:η.modulus.absNorm≤radicalBound (childCharacter ρ χ) m p (errorMovingExponent n)) :
    Real.logb Z (η.modulus.absNorm:ℝ)≤
      Real.logb Z (ρ.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+errorMoving p Z (n+1) := by
  have hmpos:=span_pos m hm
  have h12:=span_pos 12 (by norm_num)
  have h72:=span_pos 72 (by norm_num)
  have hρ:=modulus_pos ρ
  have hray:( (childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound ρ χ
  have hb:(η.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)) := by
    have hh:(η.modulus.absNorm:ℝ)≤(radicalBound (childCharacter ρ χ) m p (errorMovingExponent n):ℝ):=by exact_mod_cast hN
    rw [radicalBound_error_power _ m p hp Z hZ n hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hray (by positivity))
        (by positivity)) (by positivity))
  have hh:=Real.logb_le_logb_of_le hZ (modulus_pos η) hb
  rw [Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm).ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {m}).absNorm).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (mul_pos (modulus_pos ρ) (span_pos 12 (by norm_num))).ne' (span_pos m hm).ne',
    Real.logb_mul (modulus_pos ρ).ne' (span_pos 12 (by norm_num)).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  linarith

theorem common_nominal_identity (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)=
    m+q+(d-c-2*w+wo-max (d-c-2*w+wo) 0)-branch*σ-δ-reserve := by ring

theorem common_nominal_le (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)≤
    m+q-branch*σ-δ-reserve := by
  rw [common_nominal_identity]
  linarith [le_max_left (d-c-2*w+wo) (0:ℝ)]

theorem shortened_log (I J:Ideal O)(X Z:ℝ)(hX:0<X)(p:O)(hp:p≠0)(k:ℕ) :
    Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^k))=
      Real.logb Z X-Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-errorRemoval p Z k := by
  rw [Real.logb_div hX.ne' (mul_pos (norm_pos _ (commonPart_ne_zero I J))
    (pow_pos (normValue_pos p hp) k)).ne',
    Real.logb_mul (norm_pos _ (commonPart_ne_zero I J)).ne' (pow_pos (normValue_pos p hp) k).ne',
    Real.logb_pow]
  unfold errorRemoval
  ring

theorem main_nominal_bound (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem error_nominal_bound (η ρ θ:Character)(χ:RayCharacter)(m₀ m₁ p:O)
    (hm₀:m₀≠0)(hm₁:m₁≠0)(hp:p≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
    (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m₀}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) m₁ p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m₀}).absNorm:ℝ)+Real.logb Z ((Ideal.span {m₁}).absNorm:ℝ)+
      2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)-σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  have hq:=radical_error_log_bound ρ θ χ m₁ p hm₁ hp Z hZ n hn hN
  rw [canonical_modulus_log η ρ m₀ hm₀ I J A Z hmod] at hq
  rw [shortened_log I J X Z hX p hp (n+1),errorCommonRadius,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',nominalLog,
    CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-2*errorRemoval p Z (n+1)+errorMoving p Z (n+1)) (0:ℝ)]

theorem physical_radial_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

theorem physical_whole_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ))) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hb':Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by linarith
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' (modulus_pos (τ χ)).ne'] at hb'
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy)
    (modulus_pos (τ χ)).le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1)))
      (modulus_pos (τ χ)))).mp hb')

theorem original_coefficient_fixed_mask {ι:Type*}[Fintype ι]
    (D:OriginalData ι)(ρ:Character)(t T:ℝ) :
    D.coefficient ρ fixedBadMask t T=
      fun I:supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*heightCoeff ρ t I) := by
  funext I
  rw [OriginalData.coefficient,←heightCoeff_eq_fixed_rowWeight ρ t I
    (Finset.mem_filter.mp I.property).2]

def presentationFactor : ℝ :=
  ((Ideal.span {(72:O)}).absNorm:ℝ)*(fixedFactor:ℝ)

theorem presentationFactor_pos : 0<presentationFactor :=
  mul_pos (span_pos 72 (by norm_num)) (by exact_mod_cast fixedFactor_pos)

theorem presentationFactor_log (Z:ℝ) : Real.logb Z presentationFactor=
    2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
  unfold presentationFactor fixedFactor
  push_cast
  rw [Real.logb_mul (span_pos 72 (by norm_num)).ne'
      (mul_pos (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero))
        (span_pos 72 (by norm_num))).ne',
    Real.logb_mul (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (span_pos 12 (by norm_num)).ne' (span_pos fixedBadMask fixedBadMask_ne_zero).ne']
  ring

theorem first_fixed_log_le (Z:ℝ)(hZ:1<Z) :
    Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)≤Real.logb Z presentationFactor := by
  apply Real.logb_le_logb_of_le hZ (span_pos 72 (by norm_num))
  have hf:(1:ℝ)≤fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact le_mul_of_one_le_right (span_pos 72 (by norm_num)).le hf

theorem exists_fixed_width_threshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 := by
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  let C:ℝ:=((Ideal.span {fixedBadMask}).absNorm:ℝ)*(16*b*Csec*(fixedFactor:ℝ)*presentationFactor)
  have hCp:0<C:=mul_pos (span_pos fixedBadMask fixedBadMask_ne_zero)
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos)
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<σ/4 by linarith))) C
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ ξ hξ
  obtain ⟨hCZ,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hh:Real.logb Z C≤σ/4:=(Real.logb_le_iff_le_rpow hZ1 hCp).mpr hCZ
  dsimp [C] at hh
  rw [Real.logb_mul (span_pos fixedBadMask fixedBadMask_ne_zero).ne'
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos).ne'] at hh
  linarith

def fixedWidthThreshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) : ℝ :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose

theorem fixedWidthThreshold_spec (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    1<fixedWidthThreshold b Csec σ hb hCs hσ ∧
    ∀Z:ℝ,fixedWidthThreshold b Csec σ hb hCs hσ≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose_spec

section ActualSource
variable (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (Character.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem error_nominal_fixed (θ:Character)(χ:RayCharacter)(p:O)(hp:p≠0)
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z dd kk cc σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-σ-δ-reserve := by
  have hh:=error_nominal_bound η ρ θ χ m fixedBadMask p hm fixedBadMask_ne_zero hp
    I J A K X Z σ δ reserve hK hX hZ hmod n hn hN
  rw [presentationFactor_log]
  linarith

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_declared_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_whole_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_whole_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

theorem error_declared_width_drop (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=error_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

end ActualSource
end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI

end Source842

/- Original source: OAI/NumberTheory/DirichletL/Detector/RadialMellin.lean; sha256: fafd663de5bd857c564980129c02711e08e934740930b38c941d0458c4056f5c -/
section Source843
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace SevenEighths.ProbeRadialMellin

def laplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t*r : ℝ))

lemma mellin_real (f : ℝ → ℂ) (s : ℝ) :
    mellin f (s : ℂ) = ∫ r : ℝ in Ioi 0, (r^(s-1) : ℝ) • f r := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open EisensteinSchwartzPoisson

def paperConstant : ℝ := 2*Real.pi/Real.sqrt 3

lemma paperConstant_pos : 0<paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0<t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0<t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

lemma positive_source_mellin (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) : 0<(mellin W (s:ℂ)).re ∧ (mellin W (s:ℂ)).im=0 := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (s:ℂ)
  have hr : ∀r, W r = ((W r).re:ℂ) := by
    intro r
    apply Complex.ext <;> simp [hreal]
  have he : mellin W (s:ℂ) =
      (((∫ r : ℝ in Ioi 0, r^(s-1)*(W r).re):ℝ):ℂ) := by
    rw [mellin_real, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [hr r, Complex.real_smul, Complex.ofReal_mul]
    simp
  rw [he]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  have hi : IntegrableOn (fun r : ℝ => r^(s-1)*(W r).re) (Ioi 0) := by
    have hh := ((mellinConvergent_real W s).mp hc).re
    simpa only [RCLike.smul_re] using! hh
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
  · have hset : Function.support (fun r : ℝ => r^(s-1)*(W r).re) ∩ Ioi 0 =
        Function.support (fun r : ℝ => (W r).re) := by
      ext r
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · intro hh
        exact fun h => hh.1 (by rw [h, mul_zero])
      · intro hh
        have hw : W r≠0 := fun h => hh (by rw [h]; rfl)
        have hp := ha.trans_le (hW hw).1
        exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hp _).ne' hh, hp⟩
    rw [hset]
    apply ((Complex.continuous_re.comp W.continuous).isOpen_support).measure_pos volume
    by_contra h
    apply hne
    ext r
    have hh : (W r).re=0 := by
      by_contra hn
      exact h ⟨r,hn⟩
    change W r = 0
    rw [hr r, hh, Complex.ofReal_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (hnonneg r)

theorem radial_mellin_positive (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    0<(mellin (paperRadialFourier W) (s:ℂ)).re ∧
      (mellin (paperRadialFourier W) (s:ℂ)).im=0 := by
  obtain ⟨hp, hz⟩ := positive_source_mellin W a b ha hW hreal hnonneg hne (1-s)
  have hh : mellin W (1-(s:ℂ)) = ((mellin W ((1-s:ℝ):ℂ)).re:ℂ) := by
    rw [show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ext (by simp) (by simpa using hz)
  rw [radial_mellin_identity W a b ha hW (s:ℂ) hs hs1, hh]
  have hpow : (paperConstant:ℂ)^(1-2*(s:ℂ)) = ((paperConstant^(1-2*s):ℝ):ℂ) := by
    rw [show 1-2*(s:ℂ)=((1-2*s:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow paperConstant_pos.le]
  rw [hpow, show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_im, and_true]
  exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos paperConstant_pos _)
    (Real.Gamma_pos_of_pos hs)) (Real.Gamma_pos_of_pos (by linarith))) hp

theorem radial_mellin_one_sixth_pos (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    0<(mellin (paperRadialFourier W) (1/6)).re ∧
      (mellin (paperRadialFourier W) (1/6)).im=0 := by
  simpa using radial_mellin_positive W a b ha hW hreal hnonneg hne (1/6)
    (by norm_num) (by norm_num)

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0<z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicReflectionKernel.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0<w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0<lo) :
    ∃ (n : ℕ) (C : ℝ), 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

theorem radial_mellin_analytic (W : SchwartzMap ℝ ℂ) :
    AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} :=
  (radial_mellin_differentiable W).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem radial_mellin_strip_rapid (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C/(1+|t|)^N := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW lo hi hlo N
  refine ⟨C,hC,fun σ hσ t => (le_div_iff₀ (by positivity)).mpr ?_⟩
  simpa only [mul_comm] using hb σ hσ t

theorem radial_mellin_vertical_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0<σ) :
    Complex.VerticalIntegrable (mellin (paperRadialFourier W)) σ := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ => mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (radial_mellin_analytic W _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using CubicReflectionKernel.weighted_two_to_cauchy
      (norm_nonneg _) t (hb σ ⟨le_rfl,le_rfl⟩ t)

theorem radial_mellin_inverse_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*
      mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
  have hi := radial_mellin_vertical_integrable W a b ha hW σ hσ
  apply (hi.norm.const_mul (x^(-σ))).mono'
  · have hm := hi.aestronglyMeasurable
    have hc : Continuous (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((σ:ℂ)+t*Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable.mul hm
  · exact Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem radial_mellin_inversion (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    mellinInv σ (mellin (paperRadialFourier W)) x = paperRadialFourier W x :=
  mellinInv_mellin_eq σ (paperRadialFourier W) hx
    (radial_mellin_convergent W σ hσ)
    (radial_mellin_vertical_integrable W a b ha hW σ hσ)
    (radial_continuous W).continuousAt

theorem radial_mellin_one_sixth_ne_zero (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    mellin (paperRadialFourier W) (1/6) ≠ 0 := by
  intro h
  have hp := (radial_mellin_one_sixth_pos W a b ha hW hreal hnonneg hne).1
  rw [h] at hp
  exact (lt_irrefl 0) hp

end SevenEighths.ProbeRadialMellin

end

end OAI

end Source843

/- Original source: OAI/NumberTheory/DirichletL/Moments/ComparisonReflection.lean; sha256: 54b1c132fdfedee64fd85e504d70199abd664d82bc7b93eb1197a56475c96357 -/
section Source844
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma residue_nontrivial (c : O) (χ : MulChar (O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (O⧸Ideal.span {c}) := by
  by_contra h
  have : Subsingleton (O⧸Ideal.span {c}) := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp [hx]

lemma residue_zero (c : O) [NeZero c] (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X))) :
    (∑' z : O,elementCoeff η z*W (‖eisEmbedding z‖^2/X))=
      6*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) hs
    (by rw [hzero,zero_mul])
    (fun u z => by rw [elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_idealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    (∑' I : NI,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' I : NI,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hQ : 0<‖eisEmbedding c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : O => ‖paperRadialFourier W
      (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X))‖) := by
    convert paperRadialFourier_lattice_summable_norm W (X/‖eisEmbedding c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : O,elementCoeff (character c χ hu) z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' z : O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
    change (∑' z : O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  linear_combination he'/6

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY : 0<‖eisEmbedding c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖eisEmbedding c‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [←mul_assoc,hfac,mul_assoc]

theorem reflected_profile_height_control (a b : ℝ) (ha : 0<a) (A K : ℕ) :
    ∃ n : ℕ,∀ (W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t : ℝ,∀j : ℕ,j≤K → ∀x : ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) j x‖≤C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  obtain ⟨n,hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDbd⟩ := hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t j hj x hx
  have hsame : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext y
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t y
  have hb := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) j hj x hx
  rw [hsame] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hDbd t) hC.le).trans_eq (by ring))
end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end Source844

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionDeletion.lean; sha256: 1a84677ea26cd8c5d0656488bb08e6972f8204b1078f2e5707c652db06a8936a -/
section Source845
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def norm (I : NI) : ℝ := I.val.absNorm
lemma norm_pos (I : NI) : 0 < norm I := CompletedGauss.nonzeroIdeal_norm_pos I

def outside (S : Finset (Ideal O)) (I : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal O)) := {I : NI // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal O)) := {I : NI // outside S I.val}

def extract (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∉ S)).prod
lemma extract_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : extract S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : residual S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal O)) (I : NI) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal O)) (I : Ideal O) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    NI ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

lemma outside_iff_coprime (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal O) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

lemma deleted_coefficient (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    idealCoeff (η.excludePrimes S hS) I.val =
      if outside S I.val then idealCoeff η I.val else 0 := by
  rw [idealCoeff_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x^2 * ‖F x‖ ≤ C

lemma schwartz_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo W := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 W, apply_nonneg _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hx] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 x

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := CompletedGauss.nonzeroIdeal_norm_rpow_summable 2 (by norm_num)
  convert h using 1
  funext I
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable (η : Character) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => idealCoeff η I.val * F (norm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI × NI => ‖F (norm p.1 * norm p.2 / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  have hs := inverse_norm_sq_summable.mul_of_nonneg inverse_norm_sq_summable
    (fun I => by positivity) (fun I => by positivity)
  apply (hs.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (norm_pos p.1) (norm_pos p.2)) hX
  have h : ‖F (norm p.1 * norm p.2 / X)‖ ≤ C / (norm p.1 * norm p.2 / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)

lemma outside_plain_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) =
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, idealCoeff η (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, idealCoeff η I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val *
        ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)

lemma normalization_factor (X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X/N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0<X) (D : SmoothIdeal S) :
    idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val.val *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, idealCoeff η I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm

theorem reflected_normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0 :=
  normalized_restoration η S hS _ (reflected_decayTwo W) X hX

def outsideSum (η : Character) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)

lemma outsideSum_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPS : P ∉ S) (I : Ideal O) :
    outside S (P*I) ↔ outside S I := by
  have hn (Q : Ideal O) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) =
    idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => idealCoeff η P *
    ((if outside S I.val then idealCoeff η I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then idealCoeff η P * idealCoeff η I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * idealCoeff η (∏ P ∈ D, P) *
      (∑' I : NI, idealCoeff η I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : Character) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (D : NI) :
    idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
      HeckeDyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val *
    ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [norm] at ht
  dsimp only [norm]
  linear_combination -(-1 : ℂ)^D.card * ht

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

def reflectedTerm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

lemma reflectedTerm_eq (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (idealCoeff ηi H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hreflect : ∀ Y : ℝ, 0<Y → HeckeDyadic.polynomial η false W Y 0 0 =
      G * HeckeDyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0<X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

theorem primitive_deleted_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS (paperRadialFourier W) X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      TraceCharacter.normalizedGauss c χ *
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H := by
  dsimp only
  apply deletion_reflection _ _ S hS W (paperRadialFourier W)
    (schwartz_decayTwo W) (reflected_decayTwo W) _ _ _
    (fun Y hY => primitive_normalized_reflection c χ hu hp hχ W Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))

theorem primitive_deleted_reflection_absolute (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,
      ‖reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H‖) := by
  dsimp only
  exact summable_sum (fun D hD =>
    ((primitive_deleted_reflection c χ hu hp hχ S hS W X hX).1 D hD).norm)

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI

end Source845

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionMass.lean; sha256: 552ba9aa43b0765a049cdb1003396d63341bd445d3112ca625cdbf388261510c -/
section Source846
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

def weight (I : Ideal O) : ℝ := (Real.sqrt (I.absNorm : ℝ))⁻¹
lemma weight_nonneg (I : Ideal O) : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul (I J : Ideal O) : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal O) = 1 := by simp [weight]
lemma weight_pow (I : Ideal O) (n : ℕ) : weight (I^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal O)) (f : Ideal O → Ideal O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one (P : Ideal O) (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

def exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) (P : S) : ℕ :=
  (normalizedFactors I.val.val).count P.val
lemma reconstruct_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective (S : Finset (Ideal O)) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal O)) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

def localMass (P : Ideal O) : ℝ := (1+weight P)/(1-weight P)
lemma localMass_nonneg (P : Ideal O) (hP : Prime P) : 0 ≤ localMass P := by
  exact div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le (P : Ideal O) (hP : Prime P) : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven (P : Ideal O) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three (P : Ideal O) (hP : Prime P) (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [ite_eq_left hp]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [ite_eq_right hp,one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod₀ (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (Real.rpow_nonneg (by positivity) _)

def coefficient (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

lemma coefficient_norm_le (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (coefficient η ηi S D) := (coefficient_summable_norm η ηi S hS D hD).of_norm

lemma coefficient_mass_le_euler (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

def unitSmooth (S : Finset (Ideal O)) : SmoothIdeal S :=
  ⟨⟨1,one_ne_zero⟩,by
    change (normalizedFactors (1 : Ideal O)).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩
lemma coefficient_empty_unit (η ηi : Character) (S : Finset (Ideal O)) :
    coefficient η ηi S ∅ (unitSmooth S) = 1 := by
  have hm : (moebius (1 : Ideal O) : ℂ) = 1 := by
    simpa only [Finset.prod_empty,Finset.card_empty,pow_zero] using
      subset_product_moebius ∅ (by simp)
  change (moebius (1 : Ideal O) : ℂ) * idealCoeff η 1 * idealCoeff ηi 1 /
    (Real.sqrt ((Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm (1 : Ideal O) : ℝ)) : ℂ) = 1
  rw [hm,map_one,map_one,map_one]
  norm_num

lemma reflectedTerm_eq_coefficient (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H = coefficient η ηi S D H *
      HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
        (Q * (Ideal.absNorm (∏ P ∈ D,P):ℝ)/(X*norm H.val)) 0 0 := rfl

end SevenEighths.CenteredMomentReflectionMass
end

end OAI

end Source846

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonMaskExpansion.lean; sha256: 7a7905cbf1da98804584b9a6d53749e29138c32d8384c3ad370c7ad5c38379f5 -/
section Source847
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def profileSlot (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P : ℝ) : ℂ :=
  naturalSlot χ pool (fun I=>ν I*W ((I.absNorm:ℝ)/P)) P

lemma outside_prime (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) : outside R I ↔ I∉R := by
  constructor
  · intro h hi
    exact h I hi dvd_rfl
  · intro h J hj hd
    have he : J=I := (prime_dvd_prime_iff_eq (hR J hj) hI).mp hd
    exact h (he ▸ hj)

lemma deleted_prime (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) :
    idealCoeff (χ.excludePrimes R hR) I = if I∈R then 0 else idealCoeff χ I := by
  have h:=deleted_coefficient χ R hR ⟨I,hI.ne_zero⟩
  simpa only [outside_prime R hR I hI,ite_not] using h

theorem naturalSlot_delete (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (pool : Finset (Ideal O)) (hp : ∀ I∈pool,Prime I) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (χ.excludePrimes R hR) pool β P =
      naturalSlot χ pool β P - naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hinter : pool∩R=pool.filter (fun I=>I∈R) := by ext I;simp
  rw [←mul_sub,hinter,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [deleted_prime χ R hR I (hp I hi)]
  by_cases h:I∈R <;> simp [h]

lemma prod_sub_expansion {α : Type*} [DecidableEq α] (F : Finset α) (a b : α→ℂ) :
    (∏i∈F,(a i-b i))=∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,b i)*(∏i∈F\J,a i) := by
  have he : (∏i∈F,(a i-b i))=∏i∈F,((-b i)+a i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [he,Finset.prod_add]
  simp only [Finset.prod_neg]

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

theorem simultaneous_deletion (χ : Character) (R : Finset (Ideal O))
    (hR : ∀ I∈R,Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (F : Finset α)
    (pool : α→Finset (Ideal O)) (hp : ∀i∈F,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      signedCoefficient χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ false W₁ (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial χ false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i))=
      ∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i))*
        (∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
    have hh:=prod_sub_expansion F (fun i=>naturalSlot χ (pool i) (β i) (P i))
      (fun i=>naturalSlot χ (pool i∩R) (β i) (P i))
    exact (Finset.prod_congr rfl (fun i hi=>naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans hh
  rw [normalized_finite_deletion_moebius χ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [signedCoefficient,plainCoefficient]
  ring

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

lemma slotMass_nonneg (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    0≤slotMass R pool β P := by unfold slotMass;positivity

lemma naturalSlot_norm (χ : Character) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma plainCoefficient_norm (χ : Character) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (idealCoeff_norm_le_one χ _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma slot_point_mass (I : Ideal O) (hI : Prime I) (β : Ideal O→ℂ)
    (P b M : ℝ) (hP : 0<P) (hM : 0≤M) (hβ : ‖β I‖≤M)
    (hs : β I≠0 → (I.absNorm:ℝ)≤b*P) :
    (Real.sqrt P)⁻¹*‖β I‖≤(Real.sqrt (max 1 b)*M)*weight I := by
  by_cases hz : β I=0
  · simp only [hz,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (weight_nonneg _)
  have hN : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  have hB : 0≤max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hsqrt : Real.sqrt (I.absNorm:ℝ)≤Real.sqrt (max 1 b)*Real.sqrt P := by
    rw [←Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt ((hs hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.le))
  have hi : (Real.sqrt P)⁻¹≤Real.sqrt (max 1 b)*weight I := by
    rw [weight,←div_eq_mul_inv,inv_eq_one_div,
      div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)]
    simpa using hsqrt
  calc
    _≤(Real.sqrt (max 1 b)*weight I)*M :=
      mul_le_mul hi hβ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weight_nonneg _))
    _=_ := by ring

lemma slotMass_bound (R pool : Finset (Ideal O)) (hp : ∀I∈pool,Prime I)
    (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    slotMass R pool β P≤(Real.sqrt (max 1 b)*M)*∑I∈R,weight I := by
  unfold slotMass
  rw [Finset.mul_sum]
  calc
    _≤∑I∈pool∩R,(Real.sqrt (max 1 b)*M)*weight I :=
      Finset.sum_le_sum (fun I hi=>slot_point_mass I (hp I (Finset.mem_inter.mp hi).1)
        β P b M hP hM (hβ I (Finset.mem_inter.mp hi).1) (hs I (Finset.mem_inter.mp hi).1))
    _=(Real.sqrt (max 1 b)*M)*∑I∈pool∩R,weight I := (Finset.mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun I hi hn=>weight_nonneg I))
      (mul_nonneg (Real.sqrt_nonneg _) hM)

lemma one_add_sum_weight (R : Finset (Ideal O)) :
    1+∑I∈R,weight I≤∏I∈R,(1+weight I) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert I R hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hw:=weight_nonneg I
    have hs:0≤∑J∈R,weight J:=Finset.sum_nonneg (fun J _=>weight_nonneg J)
    nlinarith

lemma deletion_le_euler (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    (∏I∈R,(1+weight I))≤∏I∈R,localMass I := by
  apply Finset.prod_le_prod₀ (fun I hi=>by linarith [weight_nonneg I])
  intro I hi
  apply (le_div_iff₀ (sub_pos.mpr (prime_weight_lt_one I (hR I hi)))).mpr
  have h:=weight_nonneg I
  nlinarith

lemma euler_ge_one (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    1≤∏I∈R,localMass I :=
  (show 1≤∏I∈R,(1+weight I) by
    linarith [Finset.sum_nonneg (s:=R) (fun I _=>weight_nonneg I),one_add_sum_weight R]).trans
    (deletion_le_euler R hR)

lemma one_add_slotMass (R pool : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (hp : ∀I∈pool,Prime I) (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    1+slotMass R pool β P≤max 1 (Real.sqrt (max 1 b)*M)*(∏I∈R,localMass I) := by
  have ha:=slotMass_bound R pool hp β P b M hP hM hβ hs
  have hb:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hc:=le_max_left 1 (Real.sqrt (max 1 b)*M)
  have hd:=le_max_right 1 (Real.sqrt (max 1 b)*M)
  have he:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
  nlinarith

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

omit [DecidableEq α] in
lemma signedCoefficient_norm (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=>hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=>hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

omit [DecidableEq α] in
lemma majorant_mass (R : Finset (Ideal O)) (F : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      coefficientMajorant R D₁ D₂ J pool β P)=
      (∏I∈R,(1+weight I))^2*(∏i∈F,(1+slotMass R (pool i) (β i) (P i))) := by
  simp only [coefficientMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

omit [DecidableEq α] in
lemma uniformMajorant_nonneg (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (b M : α→ℝ) (hM : ∀i∈J,0≤M i) :
    0≤uniformMajorant R D₁ D₂ J b M := by
  apply mul_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_nonneg (fun i hi=>mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
    (Finset.sum_nonneg (fun I _=>weight_nonneg I)))

omit [DecidableEq α] in
lemma signedCoefficient_uniform (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0<P i) (hM : ∀i∈J,0≤M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _=>slotMass_nonneg _ _ _ _)
    (fun i hi=>slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

omit [DecidableEq α] in
lemma uniformMajorant_mass (R : Finset (Ideal O)) (F : Finset α) (b M : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)=
      (∏I∈R,(1+weight I))^2*
        ∏i∈F,(1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)) := by
  simp only [uniformMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

omit [DecidableEq α] in
lemma uniformMajorant_mass_le (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)) * (∏I∈R,localMass I)^(2+F.card) := by
  rw [uniformMajorant_mass]
  have hE:=euler_ge_one R hR
  have hp (i : α) (hi : i∈F) :
      1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
        max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
    have ha:1+∑I∈R,weight I≤∏I∈R,localMass I:=(one_add_sum_weight R).trans (deletion_le_euler R hR)
    have hb:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have hc:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤(∏I∈R,localMass I)^2*
        ∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun I _=>by linarith [weight_nonneg I]))
          (deletion_le_euler R hR) 2
      · exact Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
      · exact Finset.prod_nonneg (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
      · exact sq_nonneg _
    _=_ := by rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add];ring

omit [DecidableEq α] in

theorem uniform_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I),
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  let n:ℕ:=2+F.card
  have hn:(0:ℝ)<n:=by dsimp [n];positivity
  let δ:ℝ:=ε/n
  have hδ:0<δ:=div_pos hε hn
  obtain ⟨C₀,hC₀,hbound⟩:=euler_mass_subpower δ hδ
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨A*C₀^n,mul_pos hA (pow_pos hC₀ n),?_⟩
  intro R hR
  have he:0≤∏I∈R,localMass I:=(euler_ge_one R hR).trans' zero_le_one
  have hr:0≤(Ideal.absNorm (∏I∈R,I):ℝ):=Nat.cast_nonneg _
  have hpow:((Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ _ hn.ne'
  calc
    _≤A*(∏I∈R,localMass I)^n:=uniformMajorant_mass_le R hR F b M hM
    _≤A*(C₀*(Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he (hbound R hR) n) hA.le
    _=_:=by rw [mul_pow,hpow];ring

omit [DecidableEq α] in

theorem signed_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs
  apply le_trans _ (hbound R hR)
  apply Finset.sum_le_sum
  intro D₁ hD₁
  apply Finset.sum_le_sum
  intro D₂ hD₂
  apply Finset.sum_le_sum
  intro J hJ
  have hj:=Finset.mem_powerset.mp hJ
  exact signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
    (Finset.mem_powerset.mp hD₂) J pool β P b M
    (fun i hi=>hp i (hj hi)) (fun i hi=>hP i (hj hi)) (fun i hi=>hM i (hj hi))
    (fun i hi=>hβ i (hj hi)) (fun i hi=>hs i (hj hi))

lemma profile_bounds (pool : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ)
    (P b M : ℝ) (hP : 0<P) (hν : ∀I∈pool,‖ν I‖≤1)
    (hW : ∀x,‖W x‖≤M) (hs : Function.support W⊆Set.Iic b) :
    (∀I∈pool,‖ν I*W ((I.absNorm:ℝ)/P)‖≤M) ∧
      (∀I∈pool,ν I*W ((I.absNorm:ℝ)/P)≠0 → (I.absNorm:ℝ)≤b*P) := by
  constructor
  · intro I hi
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν I hi)).trans (hW _)
  · intro I hi hn
    exact (div_le_iff₀ hP).mp (hs (right_ne_zero_of_mul hn))

omit [DecidableEq α] in

theorem profile_signed_mass_subpower (F : Finset α) (b M : α→ℝ)
    (hM : ∀i∈F,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (ν : α→Ideal O→ℂ)
      (W : α→ℝ→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖ν i I‖≤1) → (∀i∈F,∀x,‖W i x‖≤M i) →
      (∀i∈F,Function.support (W i)⊆Set.Iic (b i)) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool
          (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P‖)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=signed_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool ν W P hp hP hν hW hs
  exact hbound R hR χ pool (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P hp hP
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).1)
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).2)

end SevenEighths.CenteredMomentCommonMaskExpansion

end

end OAI

end Source847

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalRowSourceMask.lean; sha256: 157f212ba5bab6088dc2c676c5a87e36b632b6768c32f8f5f37d74a8252af177 -/
section Source848
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma support_prime (R P : Ideal O) (hP : P∈primeSupport R) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma coprime_support_iff (I R : Ideal O) (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := by
  constructor
  · intro h
    have aux : ∀s : Multiset (Ideal O),(∀P∈s,IsCoprime I P)→IsCoprime I s.prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simpa using (isCoprime_one_right : IsCoprime I 1)
      | @cons a s ih =>
        intro hs
        rw [Multiset.prod_cons]
        exact (hs a (Multiset.mem_cons_self _ _)).mul_right
          (ih (fun P hP=>hs P (Multiset.mem_cons_of_mem hP)))
    rw [←Ideal.prod_normalizedFactors_eq_self hR]
    exact aux _ (fun P hP=>h P (Multiset.mem_toFinset.mpr hP))
  · intro h P hP
    exact h.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP))

def excluded (χ : Character) (R : Ideal O) : Character :=
  χ.excludePrimes (primeSupport R) (support_prime R)

lemma excluded_ideal (χ : Character) (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator (χ : Character) (hχ0 : elementCoeff χ 0=0)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (idealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI

end Source848

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalRowSourceFamily.lean; sha256: 2820c4ff2b35a7765ed9797a582217401a71bb7e800443e6978b31f955cb58c0 -/
section Source849
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

structure NaturalRow (η : Character) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm≤rowConductorBound η fixedBadMask 1 z
  element : ∀n,elementCoeff character n=rowTwist (elementHom η) fixedBadMask 1 z n

def naturalRow (η : Character) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e:=exists_row_character_with_conductor η fixedBadMask 1 z
    fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,(Classical.choose_spec e).2⟩

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

lemma NaturalRow.masked_element_span {η : Character} {z : O} (F : NaturalRow η z)
    (r : O) (hr : r≠0) (n : O) :
    elementCoeff (excluded F.character (Ideal.span {r})) n=
      rowTwist (elementHom η) (fixedBadMask*r) 1 z n := by
  rw [excluded_element F.character F.element_zero (Ideal.span {r})
    (Ideal.span_singleton_eq_bot.not.mpr hr),Ideal.isCoprime_span_singleton_iff,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask r 1 z n (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

theorem NaturalRow.nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (hz : z≠0) (Q R : Ideal O) (hR : R≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    F.character.residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η F.character Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hbase

def fixedConductorFactor : ℕ := (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

lemma NaturalRow.natural_modulus_bound {η : Character} {z : O} (F : NaturalRow η z) :
    F.character.modulus.absNorm≤η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm := by
  have hh:=F.modulus_bound
  simpa [rowConductorBound,fixedConductorFactor,Ideal.span_singleton_one,mul_assoc] using hh

theorem NaturalRow.modulus_power_bound {η : Character} {z : O} (F : NaturalRow η z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (_hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m)
    (hz : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (F.character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by
  have hb : (F.character.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)*((Ideal.span {z}).absNorm:ℝ) :=
    by exact_mod_cast F.natural_modulus_bound
  apply hb.trans
  calc
    _≤(Z^m*(fixedConductorFactor:ℝ))*(Cz*Z^q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) hz
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _))
    _=(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by rw [Real.rpow_add hZ]; ring

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI

end Source849

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalRowSourceDictionary.lean; sha256: fb915e959dd7d2659b800fa5ad8688015dd73a15aab105b0d9c7fcda28be5251 -/
section Source850
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.masked_plain {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI

end Source850

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonMaskEnergy.lean; sha256: 4cac2632a3141729667a2b4b43bbdddf5719f80516525ad74d5028da4dbe0e53 -/
section Source851
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

theorem finite_shared_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι→κ→ℂ) (ρ : κ→ℝ) (hρ : ∀j,0≤ρ j)
    (ha : ∀i j,‖a i j‖≤ρ j) (E : ℝ) (hE : 0≤E)
    (hf : ∀j,(∑i,‖f i j‖^2)≤E) :
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j)^2*E := by
  have hb (j : κ) : (∑i,‖a i j*f i j‖^2)≤(ρ j*Real.sqrt E)^2 := by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2 := Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2) := (Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*E := mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_ := by rw [mul_pow,Real.sq_sqrt hE]
  have hh := CompletedGauss.finite_tsum_energy_bound
    (fun j i=>a i j*f i j) (fun j=>ρ j*Real.sqrt E)
    (fun j=>mul_nonneg (hρ j) (Real.sqrt_nonneg _)) (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

lemma triple_sum {τ : Type*} {υ : Type*} {ξ : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset τ) (T : Finset υ) (U : Finset ξ)
    [Fintype ({x // x∈S}×{x // x∈T}×{x // x∈U})]
    (g : τ→υ→ξ→A) :
    (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑x∈S,∑y∈T,∑z∈U,g x y z := by
  have hh : (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑j∈S×ˢ(T×ˢU),g j.1 j.2.1 j.2.2 := by
    apply Finset.sum_bij (fun j _=>(j.1.val,j.2.1.val,j.2.2.val))
    · intro j _
      exact Finset.mem_product.mpr ⟨j.1.property,Finset.mem_product.mpr ⟨j.2.1.property,j.2.2.property⟩⟩
    · intro i _ j _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun x=>x.2.1) h)
        · exact Subtype.ext (congrArg (fun x=>x.2.2) h)
    · intro j hj
      obtain ⟨h1,h23⟩:=Finset.mem_product.mp hj
      obtain ⟨h2,h3⟩:=Finset.mem_product.mp h23
      exact ⟨(⟨j.1,h1⟩,⟨j.2.1,h2⟩,⟨j.2.2,h3⟩),Finset.mem_univ _,rfl⟩
    · intro j _
      rfl
  simpa only [Finset.sum_product] using hh

theorem actual_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩:=uniform_mass_subpower F b M hM (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset (Ideal O) // D∈R.powerset} ×
    {D : Finset (Ideal O) // D∈R.powerset} × {J : Finset α // J∈F.powerset}
  let a (i : ι) (j : κ) := signedCoefficient (χ i) R j.1.val j.2.1.val j.2.2.val (pool i) (β i) (P i)
  let f (i : ι) (j : κ) := HeckeDyadic.polynomial (χ i) false (W₁ i)
    (X₁ i/(Ideal.absNorm (∏I∈j.1.val,I):ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ i) false (W₂ i)
    (X₂ i/(Ideal.absNorm (∏I∈j.2.1.val,I):ℝ)) 0 0 *
    ∏k∈F\j.2.2.val,naturalSlot (χ i) (pool i k) (β i k) (P i k)
  let ρ (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hρ (j : κ) : 0≤ρ j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (i : ι) (j : κ) : ‖a i j‖≤ρ j := by
    exact signedCoefficient_uniform (χ i) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool i) (β i) (P i) b M
      (fun k hk=>hp i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hP i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hβ i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hs i k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh:=finite_shared_energy a f ρ hρ ha E hE
    (fun j=>he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (i : ι) : (∑j,a i j*f i j)=
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
      ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>signedCoefficient (χ i) R D₁ D₂ J (pool i) (β i) (P i)*
        (HeckeDyadic.polynomial (χ i) false (W₁ i) (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial (χ i) false (W₂ i) (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏k∈F\J,naturalSlot (χ i) (pool i k) (β i k) (P i k)))).trans
      (simultaneous_deletion (χ i) R hR (W₁ i) (W₂ i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
        F (pool i) (hp i) (β i) (P i)).symm
  have hm : (∑j,ρ j)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2))^2=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>hρ j)) hm 2) hE).trans_eq
      (by rw [mul_pow,hr]))

lemma sqrt_inverse_cpow (X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2:ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  rw [sqrt_inverse_cpow X hX]
  unfold HeckeDyadic.polynomial idealSum
  congr 1
  have he:=tsum_subtype_eq_of_support_subset
    (s:={I : Ideal O | I≠0}) (f:=fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi;subst I;exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=_ at he
  simpa only [HeckeDyadic.summand,HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,
    HeckeDyadic.norm,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

lemma normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X=
      (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,plain_zero_height _ _ X hX]
  ring

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height _ _ X₁ hX₁,plain_zero_height _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,idealCoeff (excluded F.character R) I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

lemma deleted_height_phase (X N t : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)=(N:ℂ)^(Complex.I*t)*((X/N:ℝ):ℂ)^(Complex.I*t) := by
  have hh:=Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg hX.le hN.le) (Complex.I*t)
  rw [←Complex.ofReal_mul,show N*(X/N)=X by field_simp] at hh
  exact hh

lemma positive_height_phase_norm (X t : ℝ) (hX : 0<X) : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)

lemma deleted_normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
      (normPowerProfile W a b ha hs hW t) (X/N) 0 0=
      (N:ℂ)^(Complex.I*t)*((Real.sqrt (X/N):ℂ)⁻¹*twistedIdealSum χ W t (X/N)) := by
  rw [normalized_twisted_plain χ W a b ha hs hW t (X/N) (div_pos hX hN),
    deleted_height_phase X N t hX hN]
  ring

theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          (HeckeDyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           HeckeDyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (CompletedGauss.primeSupport R)
    (support_prime R) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=>hp i) (fun i=>heightCoefficient (β i) t) P

theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr₁ : 1≤X₁*b₁) (hr₂ : 1≤X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

theorem original_positive_energy {α : Type*} [Fintype α] [DecidableEq α]
    (b M : α→ℝ) (hM : ∀j,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)(R : Ideal O),R≠0 →
      ∀(W₁ W₂ : ι→ℝ→ℂ)(a₁ b₁ a₂ b₂ : ι→ℝ)
        (ha₁ : ∀i,0<a₁ i)(ha₂ : ∀i,0<a₂ i)
        (hs₁ : ∀i,Function.support (W₁ i)⊆Set.Icc (a₁ i) (b₁ i))
        (hs₂ : ∀i,Function.support (W₂ i)⊆Set.Icc (a₂ i) (b₂ i))
        (hW₁ : ∀i,ContDiff ℝ ∞ (W₁ i))(hW₂ : ∀i,ContDiff ℝ ∞ (W₂ i))
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)
        (t X₁ X₂ : ι→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
      (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      let χ:=fun i=>(naturalRow (η i) (z i) (hz i)).character
      let S:=CompletedGauss.primeSupport R
      (∀D₁∈S.powerset,∀D₂∈S.powerset,∀J∈(Finset.univ : Finset α).powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈Finset.univ\J,naturalSlot (χ i) (pool i j) (heightCoefficient (β i j) (t i)) (P i j)‖^2)≤E) →
      (∑i,‖positiveSlotRow (η i)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
        1 (z i) (W₁ i) (W₂ i) (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i)‖^2)≤
        C*(Ideal.absNorm (∏I∈S,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hbound⟩:=actual_shared_energy (Finset.univ : Finset α) b M (fun j _=>hM j) ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P t X₁ X₂
    hX₁ hX₂ hp hP hβ hs E hE
  dsimp only
  intro hchild
  have hh:=hbound (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
    (fun i=>normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
    X₁ X₂ pool (fun i j=>heightCoefficient (β i j) (t i)) P hX₁ hX₂
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι) := original_positive_normalized (naturalRow (η i) (z i) (hz i)) R hR
    (W₁ i) (W₂ i) (a₁ i) (b₁ i) (a₂ i) (b₂ i) (ha₁ i) (ha₂ i) (hs₁ i) (hs₂ i)
    (hW₁ i) (hW₂ i) (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  simp_rw [he,norm_mul,positive_height_phase_norm _ _ (hX₁ _),
    positive_height_phase_norm _ _ (hX₂ _),one_mul]
  simpa only [excluded,norm_mul] using hh

theorem original_positive_deletion_height {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
        (signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          ((Ideal.absNorm (∏I∈D₁,I):ℂ)^(Complex.I*t)*
           (Ideal.absNorm (∏I∈D₂,I):ℂ)^(Complex.I*t))) *
        (((Real.sqrt (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₁ t (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ))) *
         ((Real.sqrt (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₂ t (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ))) *
         ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_deletion η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂
    pool hp β P hP t X₁ X₂ hX₁ hX₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  apply Finset.sum_congr rfl
  intro J hJ
  have hN₁:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₁
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₁ hi))
  have hN₂:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₂
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₂ hi))
  have h1:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₁ a₁ b₁ ha₁ hs₁ hW₁
    t X₁ (Ideal.absNorm (∏I∈D₁,I):ℝ) hX₁ hN₁
  have h2:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₂ a₂ b₂ ha₂ hs₂ hW₂
    t X₂ (Ideal.absNorm (∏I∈D₂,I):ℝ) hX₂ hN₂
  convert congrArg (fun q : ℂ=>
    signedCoefficient (naturalRow η z hz).character (CompletedGauss.primeSupport R) D₁ D₂ J pool
      (fun i=>heightCoefficient (β i) t) P * q *
      ∏i∈Finset.univ\J,naturalSlot (naturalRow η z hz).character (pool i) (heightCoefficient (β i) t) (P i))
    (congrArg₂ (fun x y : ℂ=>x*y) h1 h2) using 1 <;> push_cast <;> ring

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI

end Source851

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedNaturalSource.lean; sha256: b2dcf790d4b8c2d013c039119eca3c064d33afca72214a3a5585995ee0a436f3 -/
section Source852
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : 1≤U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero (χ : Character) (X : ℝ) :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0<X) (j : Fin 2) : 0<rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

lemma raw_same_product (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X₁ X₂ Y₁ Y₂ : ℝ) (h : X₁*X₂=Y₁*Y₂) :
    rawScale D a X₁ 0*rawScale D a X₂ 1=rawScale D a Y₁ 0*rawScale D a Y₂ 1 := by
  simp only [rawScale,div_mul_div_comm,h]

theorem allocated_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀F : Finset α,SharedBound F b M C ε := by
  have he (F : Finset α) : ∃C : ℝ,0<C ∧ SharedBound F b M C ε :=
    actual_shared_energy F b M (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑F : Finset α,C F
  have hsum : 0≤∑F : Finset α,C F:=Finset.sum_nonneg (fun F _=>(hC F).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro F ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C F≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ F)
    dsimp [B]
    linarith
  exact (hb F R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

lemma primeSupport_product_radical (R : Ideal O) (hR : R≠0) :
    (∏I∈CompletedGauss.primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈CompletedGauss.primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

def AllocatedBound (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (α⊕Fin 2))),
  ∀{ι : Type*} [Fintype ι],∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)
    (R : Ideal O),R≠0 → ∀(V₁ V₂ : ι→Plain)
    (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)(t X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i)(hX₂ : ∀i,0<X₂ i),
    (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
    (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
    (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
    ∀E : ℝ,0≤E →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (η i) (z i) (hz i)).character D a (V₁ i) (V₂ i)
         (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i) D₁ D₂ J‖^2)≤E) →
    (∑i,‖allocatedPositiveRow (η i)
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (z i) (t i) (pool i) (β i) (P i) D a (V₁ i).W (V₂ i).W (X₁ i) (X₂ i)‖^2)≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*E

theorem allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ AllocatedBound b M C ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hh:=hbound (liveIndices D a) (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>(V₁ i).profile _ (rawScale_pos D a (X₁ i) (hX₁ i) 0) (t i))
    (fun i=>(V₂ i).profile _ (rawScale_pos D a (X₂ i) (hX₂ i) 1) (t i))
    (fun i=>clippedScale (rawScale D a (X₁ i) 0)) (fun i=>clippedScale (rawScale D a (X₂ i) 1))
    pool (fun i j=>heightCoefficient (β i j) (t i)) P
    (fun _=>by unfold clippedScale;positivity) (fun _=>by unfold clippedScale;positivity)
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι):=allocated_normalized (η i) (z i) (hz i) R hR D a (V₁ i) (V₂ i)
    (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  have hphase (U t : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
    positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
  simp_rw [he,norm_mul,hphase,one_mul]
  rw [←primeSupport_product_radical R hR]
  simpa only [SharedBound,excluded,norm_mul] using hh

theorem uniform_allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
      AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε := by
  have he (T : Finset α) : ∃C : ℝ,0<C ∧ AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε :=
    allocated_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro T D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C T≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ T)
    dsimp [B]
    linarith
  exact (hb T D a η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

theorem natural_nonprincipal_width (η : Character) (z : O) (hz : z≠0)
    (Q R : Ideal O) (hR : R≠0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m) (hrow : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (naturalRow η z hz).character.residue≠1 ∧
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) :=
  ⟨(naturalRow η z hz).nonprincipal hz Q R hR hex,
    (naturalRow η z hz).modulus_power_bound Z m q Cz hZ hCz hη hrow⟩

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : X₁*X₂=Y₁*Y₂

lemma Row.extracted_same_product {b M : α→ℝ} (s : Row α b M)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    rawScale D a s.X₁ 0*rawScale D a s.X₂ 1=rawScale D a s.Y₁ 0*rawScale D a s.Y₂ 1 :=
  raw_same_product D a _ _ _ _ s.same_product

theorem uniform_paired_nuW_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
    ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (T⊕Fin 2))),
    ∀{ι : Type*} [Fintype ι],∀s : ι→Row T (fun i=>b i) (fun i=>M i),
    ∀(R : Ideal O),R≠0 → ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).X₁ (s i).X₂ (s i).X₁_pos (s i).X₂_pos D₁ D₂ J‖^2)≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).Y₁ (s i).Y₂ (s i).Y₁_pos (s i).Y₂_pos D₁ D₂ J‖^2)≤E₂) →
    (∑i,(‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).X₁ (s i).X₂‖^2+
      ‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).Y₁ (s i).Y₂‖^2))≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C,hC,hbound⟩:=uniform_allocated_energy b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro T D a ι _ s R hR E₁ E₂ hE₁ hE₂ hleft hright
  have hl:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).X₁) (fun i=>(s i).X₂) (fun i=>(s i).X₁_pos) (fun i=>(s i).X₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₁ hE₁ hleft
  have hr:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).Y₁) (fun i=>(s i).Y₂) (fun i=>(s i).Y₁_pos) (fun i=>(s i).Y₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₂ hE₂ hright
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hl hr

def inputSlots (s : CenteredMomentCommonRadialData.Input α) : Slots α s.hi s.M where
  pool:=s.slots
  ν:=s.ν
  W:=s.W
  P:=s.P
  prime:=s.prime
  P_pos:=s.P_pos
  ν_bound:=s.ν_bound
  W_bound:=s.W_bound
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma inputSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) :
    (inputSlots s).coefficient=s.toData.coefficient := rfl

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma commonSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    (commonSlots s C B).coefficient=(CenteredMomentCommonRadialData.commonData s C R B).coefficient := rfl

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI

end Source852

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionTails.lean; sha256: d643a6ee4d63f28899efd4a43922b4d81b65f4b92daa5df79b69ea83f11b527a -/
section Source853
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma ideal_norm_rpow_summable (B : ℕ) (hB : 2≤B) :
    Summable (fun I : NI=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)<B := by exact_mod_cast (by omega : 1<B)
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NI=>I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

lemma plain_term_rapid_bound (η : Character) (F : ℝ→ℂ) (B : ℕ) (D Y : ℝ)
    (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) (I : NI) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

theorem plain_rapid_summable (η : Character) (F : ℝ→ℂ) (B : ℕ) (hB : 2≤B)
    (D Y : ℝ) (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) :
    Summable (fun I : NI=>idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

theorem plain_rapid_bound (B : ℕ) (hB : 2≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤D → 0<Y →
      (∀x : ℝ,0<x → x^B*‖F x‖≤D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=>Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : NI,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤D*Y^B*C := by
    exact (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

theorem actual_reflected_absolute_bound (a b : ℝ) (ha : 0<a) (B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y : ℝ),0<Y →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y) := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha B 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y hY
  have hf : ∀x : ℝ,0<x → x^B*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) B)
      (norm_nonneg _)).trans hh
  exact (hKb η _ (D*(1+‖t‖)^n) Y (by positivity) hY hf).trans_eq (by ring)

lemma discarded_rapid_control (F : ℝ→ℂ) (A B : ℕ) (D R : ℝ)
    (hD : 0≤D) (hR : 0<R) (hF : ∀x : ℝ,0<x → x^(B+A)*‖F x‖≤D) :
    ∀x : ℝ,0<x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤D :=hF x hx

theorem actual_reflected_discarded_bound (a b : ℝ) (ha : 0<a) (A B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y R : ℝ),0<Y → 0<R →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y R hY hR
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*(1+‖t‖)^n) R (by positivity) hR hf
  exact (hKb η _ ((D*(1+‖t‖)^n)/R^A) Y (by positivity) hY hm).trans_eq (by ring)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end Source853

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionLength.lean; sha256: 311471b5418905c3d829edf91e10f51625399590244843e216d95d3f2b3855ca -/
section Source854
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma nonempty_clipped_scale (S B q : ℝ) (hS : 0<S) (hq : 1≤q)
    (hsupport : q/S≤B) : max 1 S≤max 1 B*S := by
  have hh : 1≤B*S := hq.trans ((div_le_iff₀ hS).mp hsupport)
  apply max_le
  · exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS.le)
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 B) hS.le

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

theorem eventually_reflected_length (C B box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M n Q R d h s q : ℝ),
      0<Q → 0<d → 0<s → Q*R≤C*Z^M → d≤R → 1≤h →
      s≤Z^(xi/2) → 1≤q → q/(s*(Q*d/(Z^n*h)))≤B →
      let declared := Real.logb Z (box*max 1 (s*(Q*d/(Z^n*h))))
      0≤declared ∧ declared≤M-n+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (C*max 1 B*box))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro M n Q R d h s q hQ hd hs hcap hdR hh hsm hq hsupport
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : 0<s*(Q*d/(Z^n*h)) := by positivity
  have hraw := reflected_scale_bound Z M n xi C Q R d h s hZ hC.le hQ.le hd.le hs.le hcap hdR hh hsm
  have hclip := nonempty_clipped_scale _ B q hp hq hsupport
  have hT : 1≤box*max 1 (s*(Q*d/(Z^n*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤box*max 1 (s*(Q*d/(Z^n*h))) :=
        mul_le_mul hbox (le_max_left _ _) (by norm_num) (by linarith)
  constructor
  · exact Real.logb_nonneg hZ hT
  · apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hT)).mpr
    calc
      _≤box*(max 1 B*(C*Z^(M-n+xi/2))) :=
        mul_le_mul_of_nonneg_left (hclip.trans
          (mul_le_mul_of_nonneg_left hraw (le_max_of_le_left (by norm_num)))) (by linarith)
      _=(C*max 1 B*box)*Z^(M-n+xi/2) :=by ring
      _≤Z^(xi/2)*Z^(M-n+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
      _=Z^(M-n+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end Source854

/- Original source: OAI/NumberTheory/DirichletL/Moments/CommonMaskChildCapacity.lean; sha256: e773d97165326c8236860ba4c893c39c316e6e5415c794c70218f71603437689 -/
section Source855
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.CenteredMomentCommonMaskChildCapacity
open HeckeFamily HeckeDyadic CenteredMomentComparisonReflection
local notation "O" => HeckeFamily.O

lemma polynomial_nonzero_support (χ : Character) (W : ℝ→ℂ) (X sigma t b : ℝ)
    (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) : 1≤b*X := by
  by_contra hh
  have hb : b*X<1:=lt_of_not_ge hh
  apply hn
  unfold polynomial
  have hzero : ∀I : NonzeroIdeal,summand χ false W X sigma t I=0 := by
    intro I
    have hW : W (norm I/X)=0 := by
      by_contra hW
      have hu:=hs hW
      have hle : norm I≤b*X:=(div_le_iff₀ hX).mp hu
      have hi : 1≤norm I := by
        change 1≤(I.val.absNorm:ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      linarith
    simp only [summand,hW,mul_zero,zero_mul]
  simp only [hzero,tsum_zero,mul_zero]

lemma actual_clipped_log (χ : Character) (W : ℝ→ℂ) (Z X sigma t b : ℝ)
    (hZ : 1<Z) (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) :
    0≤Real.logb Z (max 1 X) ∧
      Real.logb Z (max 1 X)≤Real.logb Z X+Real.logb Z (max 1 b) := by
  have hB : 0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X≤max 1 b*X := by
    apply max_le
    · exact (polynomial_nonzero_support χ W X sigma t b hX hs hn).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  linarith

lemma deleted_same_product (X₁ X₂ Y₁ Y₂ T d₁ d₂ : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) ∧
      (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by
  constructor <;> rw [div_mul_div_comm]
  · rw [hX]
  · rw [hY]

theorem actual_deleted_capacity {α : Type*} [DecidableEq α]
    (F J : Finset α) (hJ : J⊆F) (P : α→ℝ) (hP : ∀i∈F,1≤P i)
    (χ : Character) (W₁ W₂ : ℝ→ℂ) (Z X₁ X₂ t₁ t₂ b₁ b₂ kappa M : ℝ)
    (D₁ D₂ : Ideal O) (hD₁ : D₁≠0) (hD₂ : D₂≠0)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hk : 0≤kappa)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hn : polynomial χ false W₁ (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
      polynomial χ false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂≠0)
    (hcap : Real.logb Z (X₁*X₂)+6*kappa*(∑i∈F,Real.logb Z (P i))≤M) :
    let n₁:=Real.logb Z (max 1 (X₁/(D₁.absNorm:ℝ)))
    let n₂:=Real.logb Z (max 1 (X₂/(D₂.absNorm:ℝ)))
    0≤n₁ ∧ 0≤n₂ ∧ n₁+n₂+6*kappa*(∑i∈J,Real.logb Z (P i))≤
      M+Real.logb Z (max 1 b₁*max 1 b₂) := by
  have hd₁ : 1≤(D₁.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₁)
  have hd₂ : 1≤(D₂.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₂)
  have hd₁p : 0<(D₁.absNorm:ℝ):=zero_lt_one.trans_le hd₁
  have hd₂p : 0<(D₂.absNorm:ℝ):=zero_lt_one.trans_le hd₂
  have hc₁:=actual_clipped_log χ W₁ Z _ 0 t₁ b₁ hZ (div_pos hX₁ hd₁p) hs₁ (mul_ne_zero_iff.mp hn).1
  have hc₂:=actual_clipped_log χ W₂ Z _ 0 t₂ b₂ hZ (div_pos hX₂ hd₂p) hs₂ (mul_ne_zero_iff.mp hn).2
  have hslots : (∑i∈J,Real.logb Z (P i))≤∑i∈F,Real.logb Z (P i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hJ (fun i hi _=>Real.logb_nonneg hZ (hP i hi))
  have hslots' := mul_le_mul_of_nonneg_left hslots (by positivity : 0≤6*kappa)
  have hlog₁:=Real.logb_nonneg hZ hd₁
  have hlog₂:=Real.logb_nonneg hZ hd₂
  rw [Real.logb_div hX₁.ne' hd₁p.ne'] at hc₁
  rw [Real.logb_div hX₂.ne' hd₂p.ne'] at hc₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne'] at hcap
  have hb₁ : 0<max 1 b₁:=zero_lt_one.trans_le (le_max_left _ _)
  have hb₂ : 0<max 1 b₂:=zero_lt_one.trans_le (le_max_left _ _)
  dsimp only
  refine ⟨hc₁.1,hc₂.1,?_⟩
  rw [Real.logb_mul hb₁.ne' hb₂.ne']
  linarith [hc₁.2,hc₂.2]

lemma eventually_fixed_clipping_cost (b₁ b₂ delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤delta := by
  have hc:=(tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop (max 1 b₁*max 1 b₂))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hC
  refine ⟨hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hC
end SevenEighths.CenteredMomentCommonMaskChildCapacity

end

end OAI

end Source855

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeGlobal.lean; sha256: 0a68a36818ffd0823cee6c3e48c322c6e652a3fa4e386a4c9300dfb467ae02e3 -/
section Source856
namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeGlobal
open HeckeFamily HeckePrimeRay HeckeZeroSupremum

lemma zeroMaximum_le_beta {ι : Type*} [Fintype ι]
    (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ)
    (hbeta : (51/100:ℝ)≤beta) :
    HeckeDetectorZeros.zeroMaximum χ hχ T≤beta := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hbeta
  · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
    have hz := (HeckeDetectorZeros.mem_familyZeros χ hχ T i s).mp hs
    exact zero_re_le_beta (χ i) (by linarith [hz.1]) (Or.inr (hχ i)) hz.2.2.2

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_prime_global_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e slack η σmin σmax κ : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hslack : 0<slack) (hη : 0≤η)
    (hbudget : 8*e*R+slack≤ε) (hbeta : (51/100:ℝ)≤beta)
    (hκ : 2*beta-1≤κ) :
    ∃ C : ℝ,0<C ∧ ∀ Z d : ℝ,1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (_hn : ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (i : ℕ),
    ∀ r σ freq : ℝ,0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq‖^2≤
        C*(Z^d)^(κ*r+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e slack η σmin σmax hR hdmax hτ hε he he' hslack hη hbudget
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z d hZ hd hdmax hU hT χ hn i r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hmax := zeroMaximum_le_beta (twistedFamily M H hH χ) hn
    (3*(i+1:ℕ)*Z^τ) hbeta
  have hb := hbound Z d hZ hd hdmax hU hT χ hn beta i hbeta beta_le_one
    (by linarith) r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hUp : 0<Z^d := by linarith
  have hp : ((Z^d)^((beta-1/2)*r+ε))^2 = (Z^d)^(2*((beta-1/2)*r+ε)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  calc
    _≤(C*(Z^d)^((beta-1/2)*r+ε))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _=C^2*(Z^d)^(2*((beta-1/2)*r+ε)) := by rw [mul_pow,hp]
    _≤C^2*(Z^d)^(κ*r+2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z^d)
        (by nlinarith [mul_le_mul_of_nonneg_right hκ hr])) (sq_nonneg _)

end SevenEighths.CenteredMomentPrimeGlobal

end

end OAI

end Source856

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeHeight.lean; sha256: f3a8dc33493a7b9950a2de66835cf13b57de0e86f7e893487c1c0a9c941fb0cc -/
section Source857
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem ray_prime_bounded_scale (W : ℝ→ℂ) (A B lo hi D : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : Continuous W) (_hD : 1≤D) :
    ∃C : ℝ,0<C ∧ ∀(χ : Character)(P σ freq : ℝ),1≤P → P≤D → lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖≤C := by
  obtain ⟨Cw,hCw,hprofile⟩ := fixed_profile_norm_bound W hW A B lo hi hA
  let S := annulusSet B D
  refine ⟨((S.card:ℝ)+1)*Cw,by positivity,?_⟩
  intro χ P σ freq hP hPD hσ hσhi
  have hp : 0<P := zero_lt_one.trans_le hP
  have hsub : (annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)⊆S := by
    intro I hI
    have hi := ConcretePrimeRowBridge.mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    exact ⟨hi.1,hi.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hPD (le_trans zero_le_one (le_max_left _ _))))⟩
  have hn (I : Ideal O) : ‖idealCoeff χ I*annularWeight W P σ freq I‖≤Cw := by
    have hc := idealCoeff_norm_le_one χ I
    apply (show ‖idealCoeff χ I*annularWeight W P σ freq I‖≤‖annularWeight W P σ freq I‖ by
      rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hc).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hCw.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hA.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hpow : ‖(P:ℂ)^(-(1/2:ℂ))‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    norm_num only [Complex.neg_re,show ((1/2:ℂ).re)=1/2 by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP (by norm_num)
  unfold rayPrimePolynomial
  rw [norm_mul]
  calc
    _ ≤ ‖∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),
        idealCoeff χ I*annularWeight W P σ freq I‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
    _ ≤ ∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),Cw :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun I _=>hn I))
    _ ≤ ∑ _I∈S,Cw := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>hCw.le)
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];nlinarith

lemma lifted_scale_power (Z T D P κ loss : ℝ) (hZ : 0<Z) (hT : 0<T) (hD : D≠0)
    (hU : 1<(Z*T)^D) (hP : 0<P) :
    ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P+2*(loss/(2*D)))=
      P^κ*Z^loss*T^loss := by
  have hu : 0<(Z*T)^D := zero_lt_one.trans hU
  rw [Real.rpow_add hu]
  have hs : ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P)=P^κ := by
    rw [mul_comm κ,Real.rpow_mul hu.le,Real.rpow_logb hu (ne_of_gt hU) hP]
  rw [hs,←Real.rpow_mul (mul_pos hZ hT).le]
  have he : D*(2*(loss/(2*D)))=loss := by field_simp
  rw [he,Real.mul_rpow hZ.le hT.le]
  ring

theorem ray_prime_all_height_large (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (_hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log P →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*P^κ*Z^loss*(3+|freq|)^loss := by
  let d := max Lmod Lslot+2
  have hd : 0<d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hd1 : 1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hmd : Lmod+1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hsd : Lslot≤d := by dsimp [d];have := le_max_right Lmod Lslot;linarith
  let eps := loss/(2*d)
  have heps : 0<eps := by dsimp [eps];positivity
  let e := min (eps/32) (1/2000)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have he' : e<1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hbudget : 8*e*1+eps/2≤eps := by have := min_le_left (eps/32) (1/2000);dsimp [e];linarith
  obtain ⟨C,hC,hbound⟩ := CenteredMomentPrimeGlobal.ray_prime_global_squared M H hH W A B hA hWs hW
    1 d 1 eps e (eps/2) (4/d) lo hi κ (by norm_num) hd.le (by norm_num) heps he he'
    (by positivity) (by positivity) hbudget hbeta hκ
  let Z₀ := max 2 (M.absNorm:ℝ)
  refine ⟨C,Z₀,hC,lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _),?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge
  have hz2 : 2≤Z := (le_max_left _ _).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hMZ : (M.absNorm:ℝ)≤Z := (le_max_right _ _).trans hZ
  let T := 3+|freq|
  let Zt := Z*T
  let U := Zt^d
  have hT3 : 3≤T := by dsimp [T];linarith [abs_nonneg freq]
  have hT : 0<T := by linarith
  have hzt6 : 6≤Zt := by dsimp [Zt];nlinarith
  have hzt : 0<Zt := by linarith
  have hzt1 : 1≤Zt := by linarith
  have hZzt : Z≤Zt := by dsimp [Zt];nlinarith
  have hTzt : T≤Zt := by dsimp [Zt];nlinarith
  have hztU : Zt≤U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hzt1 hd1
  have hU : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hPU : P≤U := hPcap.trans ((Real.rpow_le_rpow_of_exponent_le hz1 hsd).trans
    (Real.rpow_le_rpow hz.le hZzt hd.le))
  let r := Real.logb U P
  have hr : 0≤r := Real.logb_nonneg hU hP
  have hr1 : r≤1 := (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le hP)).mpr
    (by simpa only [Real.rpow_one] using hPU)
  have hPr : U^r=P := Real.rpow_logb hUp (ne_of_gt hU) (zero_lt_one.trans_le hP)
  have hQ (θ : RayQuotient.Characters M H) : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤U := by
    have ht : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤(χ.modulus.absNorm:ℝ)*M.absNorm := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH χ θ
    apply ht.trans
    calc
      _ ≤ Z^Lmod*Z := mul_le_mul hχ hMZ (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = Z^(Lmod+1) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hz1 hmd
      _ ≤ U := Real.rpow_le_rpow hz.le hZzt hd.le
  have hheight : (3+2*Zt)^2≤U^(4/d) := by
    have heq : U^(4/d)=Zt^(4:ℝ) := by
      dsimp [U]
      rw [←Real.rpow_mul hzt.le]
      congr 1
      field_simp
    rw [heq,Real.rpow_ofNat]
    have hb : 3+2*Zt≤Zt^2 := by nlinarith
    calc
      _ ≤ (Zt^2)^2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = _ := by ring
  have hb := hbound Zt d hzt1 hd.le le_rfl (by linarith : 2≤Zt^d)
    (by simpa only [Real.rpow_one] using (show (2:ℝ)<Zt by linarith)) χ hn 0 r σ freq hr hr1 hσ hσhi
    (by change _≤Real.log (U^r);rw [hPr];exact hlarge) hQ
    (by norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one];dsimp [T] at hTzt;linarith)
    (by simpa only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one] using hheight)
  change ‖rayPrimePolynomial M H χ W B (U^r) σ freq‖^2≤C*U^(κ*r+2*eps) at hb
  rw [hPr] at hb
  apply hb.trans_eq
  dsimp only [U,Zt,r,eps,T]
  rw [lifted_scale_power Z (3+|freq|) d P κ loss hz hT hd.ne' hU (zero_lt_one.trans_le hP)]
  ring

theorem ray_prime_all_height_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*(1+|freq|)^degree*Z^loss*P^κ := by
  obtain ⟨Cbig,Z₀,hCbig,hZ₀,hbig⟩ := ray_prime_all_height_large M H hH W A B hA hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let K := 2*(|Real.log A|+|Real.log B|)+1
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨Csmall,hCs,hsmall⟩ := ray_prime_bounded_scale M H W A B lo hi (Real.exp K) hA hWs hW.continuous
    (Real.one_le_exp hK)
  let degree := ⌈loss⌉₊
  let C0 := Cbig+Csmall^2
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0*(3:ℝ)^degree,Z₀,by positivity,hZ₀,?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi
  have hz1 : 1≤Z := hZ₀.le.trans hZ
  have hκ0 : 0≤κ := by linarith
  have hpκ : 1≤P^κ := Real.one_le_rpow hP hκ0
  have hzloss : 1≤Z^loss := Real.one_le_rpow hz1 hloss.le
  have htbase : 1≤3+|freq| := by linarith [abs_nonneg freq]
  have htloss : 1≤(3+|freq|)^loss := Real.one_le_rpow htbase hloss.le
  have hbase : ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C0*P^κ*Z^loss*(3+|freq|)^loss := by
    by_cases hlarge : K≤Real.log P
    · exact (hbig Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge).trans
        (by dsimp [C0];gcongr; nlinarith [sq_nonneg Csmall])
    · have hPD : P≤Real.exp K := by
        have he := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        simpa only [Real.exp_log (zero_lt_one.trans_le hP)] using he
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hsmall χ P σ freq hP hPD hσ hσhi) 2
      apply hb.trans
      calc
        Csmall^2 ≤ C0 := by dsimp [C0];linarith
        _ ≤ C0*P^κ := le_mul_of_one_le_right hC0.le hpκ
        _ ≤ C0*P^κ*Z^loss := le_mul_of_one_le_right (by positivity) hzloss
        _ ≤ _ := le_mul_of_one_le_right (by positivity) htloss
  have hheight : (3+|freq|)^loss≤(3:ℝ)^degree*(1+|freq|)^degree := by
    calc
      _ ≤ (3+|freq|)^(degree:ℝ) := Real.rpow_le_rpow_of_exponent_le htbase (Nat.le_ceil loss)
      _ = (3+|freq|)^degree := Real.rpow_natCast _ _
      _ ≤ (3*(1+|freq|))^degree := pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg freq]) _
      _ = _ := mul_pow _ _ _
  apply hbase.trans
  calc
    _ ≤ C0*P^κ*Z^loss*((3:ℝ)^degree*(1+|freq|)^degree) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI

end Source857

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeSlotBound.lean; sha256: 482a51e166c39caeb3b22c1e1b3004220b73f1a5a85ea4c52d2322b26c94817b -/
section Source858
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentPrimeSlotBound
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentRayNonprincipal
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

include hH
theorem actual_slot_all_height_squared (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hWs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧ ∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H b P) (slotProfile W P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  have hχreal:(χ.modulus.absNorm:ℝ)≤Z^Lmod:=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  rw [normalizedSlot_norm_sq M H η χ m A z hrow W b P σ t (zero_lt_one.trans_le hP)]
  exact hbound Z P hZ hP hPcap χ hχreal
    (all_ray_twists_nonprincipal M H hH η χ Q m A z hrow hQ hex) σ t hσ hσhi

end SevenEighths.CenteredMomentPrimeSlotBound

end

end OAI

end Source858

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeSlotUniform.lean; sha256: 1d6a687d39cddcbbdb726b5f6f783c1cec8174f724fd44b7a6359f7455a4cf2e -/
section Source859
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotUniform
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotBound CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (slotProfile (W i) P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  have hall:=fun i=>actual_slot_all_height_squared M H hH (W i) (a i) (b i) (ha i)
    (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  choose degree C Z₀ hC hZ₀ hbound using hall
  let D:ℕ:=∑i,degree i
  let Csum:ℝ:=1+∑i,C i
  let Zsum:ℝ:=2+∑i,Z₀ i
  have hCs:1≤Csum:=by dsimp [Csum]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>(hC i).le))
  have hZs:1<Zsum:=by
    have hh:0≤∑i,Z₀ i:=Finset.sum_nonneg (fun i _=>le_trans zero_le_one (hZ₀ i).le)
    dsimp [Zsum]; linarith
  refine ⟨D,Csum,Zsum,hCs,hZs,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  have hz0:Z₀ i≤Zsum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>le_trans zero_le_one (hZ₀ j).le) (Finset.mem_univ i)
    dsimp [Zsum]; linarith
  have hci:C i≤Csum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Csum]; linarith
  have hdi:degree i≤D:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ i)
  have hh:=hbound i Z P (hz0.trans hZ) hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) κ)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hZs.le.trans hZ |>.trans' zero_le_one) loss)
  exact mul_le_mul hci (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hdi)
    (by positivity) (zero_le_one.trans hCs)

end SevenEighths.CenteredMomentPrimeSlotUniform

end

end OAI

end Source859

/- Original source: OAI/NumberTheory/DirichletL/Moments/PrimeSlotExternal.lean; sha256: d5979313fd96270483a856e896e4b9489be7ff3d2deff985bce13137d9d89513 -/
section Source860
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotExternal
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile HeckePrimeAnnular
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotUniform CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_external_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t v V:ℝ,lo≤σ → σ≤hi → |v|≤V →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (annularWeight (W i) P σ v) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t v V hσ hσhi hv
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  rw [CenteredMomentPrimeSlotShift.normalizedSlot_norm_sq M H η χ m A z hrow (W i) (b i) P σ t v
    (zero_lt_one.trans_le hP),←CenteredMomentPrimeSlot.normalizedSlot_norm_sq M H η χ m A z hrow
      (W i) (b i) P σ (t+v) (zero_lt_one.trans_le hP)]
  apply (hbound i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ (t+v) hσ hσhi).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans (hZ₀.le.trans hZ)) _)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) _

end SevenEighths.CenteredMomentPrimeSlotExternal

end

end OAI

end Source860

/- Original source: OAI/NumberTheory/DirichletL/Moments/ActualLiveSlotRemoval.lean; sha256: b98857d480a582688353517a3cdcc106289a2f40867591de19f15dcbcfacf02e -/
section Source861
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentActualLiveSlotRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotExternal CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_live_slot_removal {ι:Type*} [Fintype ι] [DecidableEq ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀(J:Finset ι) (w:ι→ℝ) (F mesh:ℝ),0≤F → 0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
      ∃R:Finset ι,R⊆J ∧ (R=J ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh ∧
      ∀Z:ℝ,Z₀≤Z → ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M →
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod → ¬FixedInducingRow η Q m A z →
      ∀(σ ν:ι→ℝ) (t V:ℝ), (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|ν i|≤V) →
      ∀(W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i=>annularWeight (W i) (P i) (σ i) (ν i)
      ‖selectedProduct J η m A z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+F/6+κ*mesh)*
          ‖selectedProduct (J\R) η m A z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_external_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,Z₀,pow_pos (zero_lt_one.trans_le hC) _,hZ₀,?_⟩
  intro J w F mesh hF hmesh hw hwm hwcap
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w F κ mesh hF hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,hpay,hcost,?_⟩
  intro Z hZ η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ ν t V hσ hσhi hV hν W₁ W₂ X₁ X₂
  dsimp only
  have hz1:1≤Z:=hZ₀.le.trans hZ
  have hz0:0<Z:=zero_lt_one.trans_le hz1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hz1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η m A z (primePool M H (b i) (Z^(w i)))
      (annularWeight (W i) (Z^(w i)) (σ i) (ν i)) t (Z^(w i))‖^2≤B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hz1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hz1 (hwcap i)) η Q m A z hQ hm hA hz hmLam hm2 hcond hex
      (σ i) t (ν i) V (hσ i) (hσhi i) (hν i)
    rw [←Real.rpow_mul hz0.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η m A z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i))) (fun i=>annularWeight (W i) (Z^(w i)) (σ i) (ν i))
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hz0 w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(F/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hz1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hz0.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(F/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hz0.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(F/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hz0]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)

  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI

end Source861

/- Original source: OAI/NumberTheory/DirichletL/Moments/LiveCapacity.lean; sha256: 830fc6fa183f7da62fbd40121fdca927bca137599475729ce61e8cab38d4fa76 -/
section Source862
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

 theorem remaining_capacity {ι:Type*} [DecidableEq ι]
    (J R:Finset ι) (hR:R⊆J) (w:ι→ℝ) (n₁ n₂ M κ:ℝ)
    (hpay:R=J ∨ excess J w n₁ n₂ M κ≤6*κ*(∑i∈R,w i)) :
    R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M := by
  rcases hpay with h|h
  · exact Or.inl h
  · right
    have hs:=Finset.sum_sdiff hR (f:=w)
    have hm:=le_max_left (n₁+n₂+6*κ*(∑i∈J,w i)-M) (0:ℝ)
    change max _ _≤_ at h
    have hh:=hm.trans h
    rw [←hs] at hh
    nlinarith

 theorem removal_excess_cost {ι:Type*} [DecidableEq ι]
    (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ mesh:ℝ)
    (hκ:0<κ) (hm:0≤mesh) (hw:∀i∈J,0≤w i) (hwm:∀i∈J,w i≤mesh) :
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M) ∧
      κ*(∑i∈R,w i)≤excess J w n₁ n₂ M κ/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay,hcost⟩:=CenteredMomentWholeSlotDeletion.whole_removal
    J w (excess J w n₁ n₂ M κ) κ mesh (le_max_right _ _) hκ hm hw hwm
  exact ⟨R,hR,remaining_capacity J R hR w n₁ n₂ M κ hpay,hcost⟩

end SevenEighths.CenteredMomentLiveCapacity

end

end OAI

end Source862

/- Original source: OAI/NumberTheory/DirichletL/Moments/AllocatedChildCapacity.lean; sha256: 87899d96509e0e41058b12d1210a1817f95bfa6dc33ec9b6b843e512935dc24b -/
section Source863
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

lemma clipped_log (Z U : ℝ) (hZ : 1<Z) (hU : 0<U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1<Z) (h₁ : 0<U₁) (h₂ : 0<U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1<Z)
    (h₁ : 0<U₁) (h₂ : 0<U₂) (hs₁ : 1≤U₁*b₁) (hs₂ : 1≤U₂*b₂) :
    0≤clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0<U) (hs : 1≤U*b) :
      max (-Real.logb Z U) 0≤Real.logb Z (max 1 b) := by
    have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0<U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

omit [DecidableEq ι] in
lemma preVolume_pos (s : Data ι) : 0<preVolume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma formalReduction_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (P : ι→ℝ) (hP : ∀i,1≤P i) : 1≤formalReductionFactor D a P :=
  one_le_mul_of_one_le_of_one_le (selectedNorm_ge_one D a)
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1<Z) (P : ι→ℝ) (hP : ∀i,1≤P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (P : ι→ℝ) (hP : ∀i,0<P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=>hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=>hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

theorem excess_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,1≤P i) (hκ : (1/6:ℝ)≤κ)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*(∑i,Real.logb Z (P i))+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P (fun i=>zero_lt_one.trans_le (hP i))]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  have hp := mul_le_mul_of_nonneg_left (remainingLogs_le D a Z hZ P hP)
    (by linarith : 0≤6*κ-1)
  exact max_le_max (by linarith) le_rfl

theorem allocated_survives (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    1≤rawScale D a X₁ 0*s.b₁ ∧ 1≤rawScale D a X₂ 1*s.b₂ := by
  have hz (hs : rawScale D a X₁ 0*s.b₁<1 ∨ rawScale D a X₂ 1*s.b₂<1) : False := by
    apply hne
    exact CenteredMomentCommonMaskEnergy.original_retained_zero s.η s.m s.A z _ _ _ _
      s.support₁ s.support₂ (fun i : liveIndices D a=>s.slots i)
      (fun i : liveIndices D a=>s.coefficient i) (fun i : liveIndices D a=>s.P i)
      s.t _ _ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs
  constructor
  · exact le_of_not_gt (fun hh=>hz (Or.inl hh))
  · exact le_of_not_gt (fun hh=>hz (Or.inr hh))

theorem paired_capacity (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let bound := max (Real.logb Z (preVolume s)-Real.logb Z (formalReductionFactor D a s.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂≠0 →
      max (plainLogs D a Z s.X₁ s.X₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.Y₁ s.Y₂≠0 →
      max (plainLogs D a Z s.Y₁ s.Y₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) := by
  constructor
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.X₁ s.X₂ s.X₁_pos s.X₂_pos hn
    exact excess_le D a Z _ _ _ _ κ M hZ s.X₁_pos s.X₂_pos s.P hP hκ h₁ h₂
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hn
    have hb := excess_le D a Z _ _ _ _ κ M hZ s.Y₁_pos s.Y₂_pos s.P hP hκ h₁ h₂
    simpa only [s.same_product,preVolume] using hb

omit [DecidableEq ι] in
theorem common_preVolume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    preVolume (commonData s C R B)=preVolume s.toData/
      CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hr := CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  simpa only [preVolume,commonData,div_mul_div_comm,
    CenteredMomentCommonRawScale.remainingRaw,CenteredMomentCommonRawScale.plainNorm] using
      CenteredMomentCommonRawScale.raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

omit [DecidableEq ι] in
lemma common_reduction_ge_one (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) (hP : ∀i,1≤s.P i) :
    1≤CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hn (j : ι⊕Fin 2) : (1:ℝ)≤Ideal.absNorm (B.val j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  apply one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hn (Sum.inr 0)) (hn (Sum.inr 1)))
  apply Finset.one_le_prod₀
  intro i _
  unfold CenteredMomentCommonRawScale.frozenScale
  split_ifs
  · exact le_rfl
  · exact hP i

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

theorem common_allocated_raw_volume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2))) :
    let v := commonData s C R B
    let result := preVolume s.toData/(CenteredMomentCommonRawScale.rawReduction B.val s.P*
      formalReductionFactor D a v.P)
    rawScale D a v.X₁ 0*rawScale D a v.X₂ 1*(∏i∈liveIndices D a,v.P i)=result ∧
      rawScale D a v.Y₁ 0*rawScale D a v.Y₂ 1*(∏i∈liveIndices D a,v.P i)=result := by
  dsimp only
  have hx := raw_volume D a (commonData s C R B).X₁ (commonData s C R B).X₂
    (commonData s C R B).P (commonData s C R B).P_pos
  have hy := raw_volume D a (commonData s C R B).Y₁ (commonData s C R B).Y₂
    (commonData s C R B).P (commonData s C R B).P_pos
  change _=preVolume (commonData s C R B)/_ at hx
  rw [common_preVolume s C R B,div_div] at hx
  rw [(commonData s C R B).same_product] at hy
  change _=preVolume (commonData s C R B)/_ at hy
  rw [common_preVolume s C R B,div_div] at hy
  exact ⟨hx,hy⟩

theorem common_paired_capacity (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let v := commonData s C R B
    let bound := max (Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a v.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.X₁ v.X₂≠0 →
      max (plainLogs D a Z v.X₁ v.X₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.Y₁ v.Y₂≠0 →
      max (plainLogs D a Z v.Y₁ v.Y₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) := by
  dsimp only
  obtain ⟨hx,hy⟩ := paired_capacity (commonData s C R B) D a Z κ M hZ hκ (fun i=>hP i)
  have hv : Real.logb Z (preVolume (commonData s C R B))=
      Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P) := by
    rw [common_preVolume s C R B,Real.logb_div (preVolume_pos s.toData).ne'
      (CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos).ne']
  have hl := mul_le_mul_of_nonneg_left (common_slot_logs_le s C B Z hZ hP)
    (by linarith : 0≤6*κ-1)
  have hb : max (Real.logb Z (preVolume (commonData s C R B))-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z ((commonData s C R B).P i))+
      Real.logb Z (max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂)) 0≤
      max (Real.logb Z (preVolume s.toData)-
        Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
        Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
        (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0 := by
    rw [hv]
    apply max_le_max _ le_rfl
    change _≤Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    dsimp only [commonData]
    linarith
  exact ⟨fun z hz=>(hx z hz).trans hb,fun z hz=>(hy z hz).trans hb⟩

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

theorem allocated_clipping (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (Z X₁ X₂ : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    plainLogs D a Z X₁ X₂=Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+
      clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    0≤clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1)≤Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact ⟨clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1),
    clipping_loss_bound Z _ _ _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂⟩

lemma native_excess (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) :
    CenteredMomentLiveCapacity.excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) M κ=
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := rfl

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI

end Source863

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondCapacityLedger.lean; sha256: e20373738876fd5c8deb8055779d53ad895ef93a8d59d87c674821934dfad807 -/
section Source864
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1<Z)(P:ι→ℝ)(hP:∀i,1≤P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0<P i:=fun i=>zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=>hp i)).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1<Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith

theorem allocated_excess_from_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)
    (P:ι→ℝ)(hP:∀i,1≤P i)
    (hs₁:1≤rawScale D a X₁ 0*b₁)(hs₂:1≤rawScale D a X₂ 1*b₂)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ b₁ b₂ κ Mact hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le
  · have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
    linarith
  · positivity

theorem live_allocated_excess (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact allocated_excess_from_parent D a Z X₁ X₂ s.b₁ s.b₂ κ A M Mnom Mact
    w ell δ θ hZ h₁ h₂ hκ s.P hP hs₁ hs₂ hparent hshift hactual hw hell hδ hθ hclip

theorem live_whole_removal (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      κ*(∑i∈removed,Real.logb Z (s.P i))≤w+ell+δ/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hactual hw hell hδ hθ hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  linarith

theorem paired_edge_cost (shell width₁ width₂ cost₁ cost₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)(hwidth₁:width₁≤δ₂)(hwidth₂:width₂≤δ₂)
    (hc₁:cost₁≤w+ell+δ₁/6+θ/3+κ*mesh)
    (hc₂:cost₂≤w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(width₁+width₂)/2+(cost₁+cost₂)/2-(w+ell)≤
      δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

theorem edge_loss_budget (δ₁ δ₂ θ κ mesh ξ η:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤η):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤7*ξ/2+η := by
  nlinarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI

end Source864

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondCapacityShift.lean; sha256: 968b826c1385f5ca9b465c993ff79052d326fa48f981818c7bafc6759cf1b07d -/
section Source865
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm CenteredMomentSectorLocalization
local notation "O"=>ActualEisensteinCubic.O

lemma nominal_capacity_shift_identity (A m q c d R E j g w wo g₂ t₂ c₂ V:ℝ):
    let K₀:=2*A-c-d+R+E-m;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')-(A-(m+q))=
      g+w-(d+K₀-j)-wo+g₂-t₂-c₂ := by dsimp;ring

lemma main_capacity_gain (D₀ c σ δ:ℝ)(hc:0≤c)(hδ:0≤δ)(hD: -δ≤D₀):
    mainGain D₀ c σ-D₀≤6*(σ/3)+δ := by
  have hh:max (D₀-c) 0≤D₀+δ:=max_le (by linarith) (by linarith)
  unfold mainGain
  linarith

lemma error_capacity_gain (D₀ c σ δ Z:ℝ)(p:O)(k:ℕ)
    (hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)(hD: -δ≤D₀)
    (hk:k=1 ∨ k=6 ∨ k=7)
    (hl:σ/6≤Real.logb Z (normValue p)):
    errorGain D₀ c σ Z p k+errorRemoval p Z k-D₀-errorMoving p Z k≤
      6*errorRemoval p Z k+δ := by
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hm:0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl
    all_goals norm_num [errorMoving,errorRemoval]
    all_goals first | exact hp | constructor <;> linarith
  have hw:0≤errorRemoval p Z k:=hm.1.trans hm.2
  have he:σ+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:max (D₀-c-2*errorRemoval p Z k+errorMoving p Z k) 0≤D₀+δ:=
    max_le (by linarith) (by linarith)
  unfold errorGain
  linarith

theorem main_nominal_capacity_shift (A m q c d R E j σ δ g₂ t₂ c₂ V:ℝ)
    (hc:0≤c)(hδ:0≤δ)(hD: -δ≤d+(2*A-c-d+R+E-m)-j)
    (hcommon:g₂-t₂≤c₂):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let g:=mainGain D₀ c σ;
    let m':=2*(A-c)-j-g-g₂-V;
    let q':=q+R+E+t₂+V;
    (A-c-c₂)-(m'+q')≤A-(m+q)+6*(σ/3)+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (mainGain (d+(2*A-c-d+R+E-m)-j) c σ) 0 0 g₂ t₂ c₂ V
  have hg:=main_capacity_gain _ c σ δ hc hδ hD
  dsimp only at hi ⊢
  simp only [sub_zero,add_zero] at hi
  linarith

theorem error_nominal_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+2*wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hwo:0≤errorMoving p Z k:=by
    unfold errorMoving
    split_ifs <;> linarith
  dsimp only at hi ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI

end Source865

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondCapacityDefect.lean; sha256: 1e6a0cebdc553a98c82616b3564b4ef54e9d6a102c531f3f50c3807b1a9942e6 -/
section Source866
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  by_cases h:0≤B-x
  · rw [max_eq_left h];linarith
  · rw [max_eq_right (le_of_not_ge h)];linarith

theorem live_allocated_excess_defect (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mact) 0 := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ s.b₁ s.b₂ κ Mact hZ h₁ h₂ s.P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ s.P hP
  linarith

theorem live_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
        δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem source_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      ((∃z:O,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
          s.W₁ s.W₂ X₁ X₂≠0) →
        Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh) := by
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  rintro ⟨z,hne⟩
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem paired_width_defect_cost (shell edge₁ edge₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)
    (h₁:edge₁≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh)
    (h₂:edge₂≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(edge₁+edge₂)/2-(w+ell)≤δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI

end Source866

/- Original source: OAI/NumberTheory/DirichletL/Moments/FinalStageLedger.lean; sha256: 408e0b5d9d808728cc40f886121e1da71119a2bf4aab0100c4a4d1312fc3983a -/
section Source867
namespace OAI

noncomputable section
namespace SevenEighths.CenteredMomentFinalStageLedger

theorem capped_loss (M v : ℝ) : M/6≤2*v/3+max (M/4-v) 0 := by
  by_cases h : 0≤M/4-v
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem final_exponent (A M v loss₁ loss₂ : ℝ) :
    A-5*M/6-2*v/3-max (M/4-v) 0+loss₁+loss₂≤
      max (A-M) 0+loss₁+loss₂ := by
  have h:=capped_loss M v
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

theorem saving_exponent (A M v F₁ F₂ loss₁ loss₂ : ℝ)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    A-5*M/6-F₁-F₂≤max (A-M) 0+loss₁+loss₂ := by
  linarith [final_exponent A M v loss₁ loss₂]

theorem saving_power (Z A M v F₁ F₂ loss₁ loss₂ : ℝ) (hZ:1≤Z)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    Z^(A-5*M/6-F₁-F₂)≤Z^(max (A-M) 0+loss₁+loss₂) :=
  Real.rpow_le_rpow_of_exponent_le hZ (saving_exponent A M v F₁ F₂ loss₁ loss₂ h₁ h₂)

end SevenEighths.CenteredMomentFinalStageLedger

end

end OAI

end Source867

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondPaidLedger.lean; sha256: 3d6fddab64ad4ac4feddc9b85a2a4d56961695408f4d5614760b48517431df11 -/
section Source868
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondPaidLedger
open CenteredMomentFirstSecondCapacityLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentDescentLedger
open CenteredMomentSecondCanonical CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentRankinRadical
open CenteredMomentFinalStageLedger CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O

theorem repaired_error_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (CenteredMomentSectorLocalization.normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  dsimp only at hi ⊢
  linarith

lemma paired_first_saving (c D₀ q B wL wR woL woR gL gR ellL ellR:ℝ):
    (firstSaving c D₀ wL q woL B gL ellL+
      firstSaving c D₀ wR q woR B gR ellR)/2=
      firstSaving c D₀ ((wL+wR)/2) q ((woL+woR)/2) B
        ((gL+gR)/2) ((ellL+ellR)/2) := by
  unfold firstSaving
  ring

theorem actual_stage_saving
    (I J E:Ideal O)(hI:Supported I)(hJ:Supported J)(hE:E≠0)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (u:O)(hne:idealCorrelation C D hC hD (commonFrequencyGenerator C D*u)≠0)
    (A M Z H X Tsec Csec ξ q w wo ell σ branch:ℝ)
    (hZ:1<Z)(hH:0<H)(hX:0<X)(hCsec:1≤Csec)(hξ:0≤ξ)
    (hsec:Tsec≤Csec*firstNominalScale I J E H X)
    (n:ℤ)(hn:Retained (frequencyRadius Tsec Z ξ) n)
    (hq:0≤q)(hw:0≤w)(hwo:0≤wo)(hell:0≤ell)(hσ:0≤σ)
    (hbranch:branch≤2)(hwσ:w≤7*σ/3):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ);
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ);
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ);
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ);
    let e:=Real.logb Z (E.absNorm:ℝ);
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n);
    let F₁:=firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
      (max (D₀-c-2*w+wo) 0+branch*σ) ell;
    let F₂:=secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) u Z;
    let v:=c+w+min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ));
    A-5*M/6-F₁-F₂-max (M/4-v) 0≤
      max (A-M) 0+3*σ+5*frequencyLoss Z Csec ξ/6 := by
  have hfirst:=actual_first_saving I J E hI hJ hE Z H X Tsec Csec ξ q w wo ell σ branch
    hZ hH hX hCsec hξ hsec n hn hq hw hwo hell hσ hbranch hwσ
  have hsecond:=actual_ideal_secondSaving_lower C D hC hD hCD u Z hZ hne
  have hm₁:=min_le_left (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hm₂:=min_le_right (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hf:=final_exponent A M
    (Real.logb Z ((commonPart I J).absNorm:ℝ)+w+
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)))
    (3*σ+5*frequencyLoss Z Csec ξ/6) 0
  dsimp only at hfirst ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondPaidLedger

end

end OAI

end Source868

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstSecondLossParameters.lean; sha256: 71eba77cf26e7ac024e7a64469434ab3f41de88b0af647afbbcd17026e605c14 -/
section Source869
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters
open CenteredMomentFirstSecondCapacityLedger

def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

theorem numerical_choices (Mcap ε:ℝ)(hε:0<ε):
    ∃σ ξ mesh:ℝ,0<σ ∧ σ≤1 ∧ σ≤ε/100 ∧ 0<ξ ∧ 0<mesh ∧ mesh≤ξ ∧
      5*ξ≤σ/2 ∧ Mcap<(depth Mcap σ:ℝ)*σ/2 ∧
      (depth Mcap σ:ℝ)*(7*ξ/2+mesh)≤ε/32 ∧
      3*σ+5*ξ/6+7*ξ/2+mesh≤ε/16 := by
  let σ:ℝ:=min 1 (ε/100)
  have hσ:0<σ:=lt_min (by norm_num) (by positivity)
  have hσ₁:σ≤1:=min_le_left _ _
  have hσε:σ≤ε/100:=min_le_right _ _
  let n:=depth Mcap σ
  let ξ:ℝ:=min (σ/100) (ε/(200*((n:ℝ)+1)))
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have hξ:0<ξ:=lt_min (by positivity) (by positivity)
  have hξσ:ξ≤σ/100:=min_le_left _ _
  have hξε:ξ≤ε/(200*((n:ℝ)+1)):=min_le_right _ _
  have he:ξ*(200*((n:ℝ)+1))≤ε:=(le_div_iff₀ (by positivity)).mp hξε
  have hne:(n:ℝ)*ξ≤ε/200:=by nlinarith
  refine ⟨σ,ξ,ξ,hσ,hσ₁,hσε,hξ,hξ,le_rfl,?_,depth_covers Mcap σ hσ,?_,?_⟩
  · linarith
  · change (n:ℝ)*(7*ξ/2+ξ)≤ε/32
    nlinarith
  · linarith

theorem edge_with_choices (δ₁ δ₂ θ κ mesh ξ:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤ξ):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤9*ξ/2 := by
  have hh:=edge_loss_budget δ₁ δ₂ θ κ mesh ξ ξ hδ₁ hδ₂ hθ hκ hm hmesh
  linarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI

end Source869

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstExceptionalPaidScales.lean; sha256: 519f416c9c5fc2fd1f19c106ff9b50102a7f2164d6eb3fb0158fda5abdcfb1a6 -/
section Source870
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstPhysicalLedger
local notation "O"=>ActualEisensteinCubic.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0<H
  hX:0<X
  hCsec:1≤Csec
  hξ:0≤ξ
  hsec:Tsec≤Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤q
  hw:0≤w
  hwo:0≤wo
  hell:0≤ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

def removedWidth {Z:ℝ}(s:Branch Z):ℝ:=
  Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+s.w

def saving {Z:ℝ}(s:Branch Z):ℝ:=
  let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
  let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
  let p:=Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)
  let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
  let e:=Real.logb Z (s.E.absNorm:ℝ)
  let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
    Real.logb Z (dyadicScale s.n)
  firstSaving c D₀ s.w (s.q+R+e) s.wo (c+d-2*p-R)
    (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell

def loss {Z:ℝ}(s:Branch Z):ℝ:=3*s.σ+5*frequencyLoss Z s.Csec s.ξ/6

def rawCap (Z:ℝ)(X red:Fin 2→ℝ):ℝ:=
  min (Real.logb Z (X 0/red 0)) (Real.logb Z (X 1/red 1))

lemma actual_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤saving s:=by
  have hh:=actual_first_saving s.I s.J s.E s.hI s.hJ s.hE Z s.H s.X s.Tsec s.Csec
    s.ξ s.q s.w s.wo s.ell s.σ s.kind hZ s.hH s.hX s.hCsec s.hξ s.hsec
    s.n s.hn s.hq s.hw s.hwo s.hell s.hσ s.hkind s.hwσ
  simpa only [removedWidth,loss,saving,sub_add_eq_sub_sub] using hh

lemma raw_cap_lower (Z L d:ℝ)(hZ:1<Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^L≤X i)(hred:∀i,0<red i)(hupper:∀i,red i≤Z^d):
    L-d≤rawCap Z X red:=by
  have h (i:Fin 2):L-d≤Real.logb Z (X i/red i):=by
    have hz:0<Z:=zero_lt_one.trans hZ
    have hx:0<X i:=(Real.rpow_pos_of_pos hz L).trans_le (hX i)
    have hl:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz L) (hX i)
    have hr:=Real.logb_le_logb_of_le hZ (hred i) (hupper i)
    rw [Real.logb_rpow hz hZ.ne'] at hl hr
    rw [Real.logb_div hx.ne' (hred i).ne']
    linarith
  exact le_min (h 0) (h 1)

theorem actual_branch_stage (Z A M:ℝ)(hZ:1<Z)(s:Branch Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^(M/4)≤X i)(hred:∀i,0<red i)
    (hupper:∀i,red i≤Z^(removedWidth s)):
    A-5*M/6-saving s-2*max (rawCap Z X red) 0/3≤A-M+loss s:=by
  have hs:=actual_saving hZ s
  have hr:=raw_cap_lower Z (M/4) (removedWidth s) hZ X red hX hred hupper
  have hm:=le_max_left (rawCap Z X red) (0:ℝ)
  linarith

theorem actual_paired_stage (Z A M:ℝ)(hZ:1<Z)(s:Fin 2→Branch Z)
    (X red:Fin 2→Fin 2→ℝ)
    (hX:∀j i,Z^(M/4)≤X j i)(hred:∀j i,0<red j i)
    (hupper:∀j i,red j i≤Z^(removedWidth (s j))):
    A-5*M/6-(saving (s 0)+saving (s 1))/2-
      (max (rawCap Z (X 0) (red 0)) 0+max (rawCap Z (X 1) (red 1)) 0)/3≤
      max (A-M) 0+(loss (s 0)+loss (s 1))/2:=by
  have h₀:=actual_branch_stage Z A M hZ (s 0) (X 0) (red 0) (hX 0) (hred 0) (hupper 0)
  have h₁:=actual_branch_stage Z A M hZ (s 1) (X 1) (red 1) (hX 1) (hred 1) (hupper 1)
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

end SevenEighths.CenteredMomentFirstExceptionalPaidScales

end

end OAI

end Source870

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedAllowance.lean; sha256: d70f3f72b6f06f5ff014a37fe5a9ed7ae0376d6ff826c5493336d949334dd448 -/
section Source871
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6

def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6

lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤allowance C D Z:=by
  unfold allowance;positivity

lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ

theorem first_saving_with_allowance {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
    let e:=Real.logb Z (s.E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
      Real.logb Z (dyadicScale s.n)
    2*(c+s.w)/3-loss s≤
      firstSaving c D₀ s.w (s.q+R+e) s.wo (extractedAllowance s.I s.J Z)
        (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell:=by
  have hC:(1:ℝ)≤((commonPart s.I s.J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero s.I s.J))
  have hR:(1:ℝ)≤((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hE:(1:ℝ)≤(s.E.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr s.hE)
  have hc:=Real.logb_nonneg hZ hC
  have hr:=Real.logb_nonneg hZ hR
  have he:=Real.logb_nonneg hZ hE
  have hd:=retained_deficit s.I s.J s.E s.hE Z s.H s.X s.Tsec s.Csec s.ξ
    hZ s.hH s.hX (zero_lt_one.trans_le s.hCsec) s.hsec s.n s.hn
  have hh:=firstSaving_lower _ _ _ s.w
    (s.q+Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)+Real.logb Z (s.E.absNorm:ℝ))
    _ s.wo (extractedAllowance s.I s.J Z)
    (max (Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)+
      Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-Real.logb Z (dyadicScale s.n)-
      Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)-2*s.w+s.wo) 0+s.kind*s.σ)
    s.ell s.σ (frequencyLoss Z s.Csec s.ξ)
    hc s.hw (by linarith [s.hq]) s.hwo (by unfold extractedAllowance;positivity)
    s.hσ (frequencyLoss_nonneg Z s.Csec s.ξ hZ s.hCsec s.hξ)
    (by linarith [s.hq]) (le_refl _) hd (by nlinarith [s.hkind,s.hσ]) s.hell s.hwσ
  dsimp only at hh ⊢
  simpa only [loss,sub_add_eq_sub_sub] using hh

def columnSaving {Z:ℝ}(s:Branch Z):ℝ:=
  saving s-(Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+
    Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)-
    2*Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ))+
    extractedAllowance s.I s.J Z

lemma column_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤columnSaving s:=by
  have hh:=first_saving_with_allowance hZ s
  dsimp only [columnSaving,saving,removedWidth] at hh ⊢
  unfold firstSaving at hh ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI

end Source871

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedCommonRadius.lean; sha256: d60f10c75b6dfe71f43a3ea9335bbb507b677ff080d51122a76cfcff97759ae9 -/
section Source872
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedCommonRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstMixedAllowance CenteredMomentCommonRadiusSaving
local notation "O" => ActualEisensteinCubic.O

theorem column_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    0≤c ∧ 0≤q ∧ 0≤extractedAllowance I J Z ∧
      3*c-5*d≤6*extractedAllowance I J Z+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  refine ⟨hc,hq.1,?_,?_⟩
  · unfold extractedAllowance; positivity
  · unfold extractedAllowance; linarith [hq.2]

theorem actual_main_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_column_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

end SevenEighths.CenteredMomentFirstMixedCommonRadius

end

end OAI

end Source872

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstMixedNormalization.lean; sha256: 31e84cd4fd1bf6fcf5e1a3acf9dc9fd1038d4a291fef72f1662d53a3675d22cb -/
section Source873
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalization
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => ActualEisensteinCubic.O

theorem exceptional_reference_identity (Z V C D NE NR K Q w wo B j g ell:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hD:0<D)(hE:0<NE)(hR:0<NR)(hK:0<K)(hQ:0<Q):
    let c:=Real.logb Z C;
    let d:=Real.logb Z D;
    let q:=Real.logb Z Q;
    let K0:=Real.logb Z (NE*NR*V^2/(K*C*D));
    let M:=Real.logb Z K+q-Real.logb Z NE-Real.logb Z NR;
    (V/C)*Z^(-wo)*(V/C/Z^w)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      (Q*(V/C)^2*Z^B)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo B g ell):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hzlog:Real.log Z≠0:=ne_of_gt (Real.log_pos hZ)
  dsimp only
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_div,Real.log_mul,Real.log_rpow,Real.log_pow]
    unfold firstSaving Real.logb
    rw [Real.log_div,Real.log_mul,Real.log_mul,Real.log_pow,
      Real.log_mul,Real.log_mul] <;> try positivity
    field_simp
    ; ring

theorem actual_error_weight (p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(k:ℕ)
    (hk:k=1 ∨ k=6 ∨ k=7):
    localErrorCost p (k-1)≤Z^(-errorMoving p Z k):=by
  have hn:1≤normValue p:=normValue_ge_one p hp
  have hnpos:0<normValue p:=normValue_pos p hp
  have he:Z^(-(Real.logb Z (normValue p)))=(normValue p)⁻¹:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hnpos]
  rcases hk with rfl|rfl|rfl
  · simpa [localErrorCost,errorMoving,normValue] using he.ge
  · norm_num only [Nat.reduceSub,localErrorCost,errorMoving,ite_true,neg_zero,Real.rpow_zero]
    change (1-(normValue p)⁻¹)^2≤1
    have hi:0≤(normValue p)⁻¹:=inv_nonneg.mpr hnpos.le
    have hu:(normValue p)⁻¹≤1:=inv_le_one_of_one_le₀ hn
    nlinarith
  · simpa [localErrorCost,errorMoving,normValue] using he.ge

end SevenEighths.CenteredMomentFirstMixedNormalization

end

end OAI

end Source873

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstExceptionalPrefactor.lean; sha256: b5e775ec8dd733a0528443488c6f64c11e9f406108ce72978586fce52d27addb -/
section Source874
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon

lemma exceptional_core_nominal (K V E R C D A : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hA:0<A):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*A^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      (A/(E*R*V^2/(K*C*D)))^((5:ℝ)/6) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,
      Real.log_sqrt,Real.log_pow]
    ring

lemma amplified_nominal_ratio (Z T j g : ℝ)(hZ:1<Z)(hT:0<T):
    (Z^(j+g)/T)^((5:ℝ)/6)=Z^(5*(j-Real.logb Z T+g)/6) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show j-Real.logb Z T+g=j+g-Real.logb Z T by ring]
  rw [show 5*(j+g-Real.logb Z T)/6=(j+g-Real.logb Z T)*((5:ℝ)/6) by ring,
    Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_logb hz (ne_of_gt hZ) hT]

theorem exceptional_core_log (K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6) := by
  rw [exceptional_core_nominal K V E R C D (Z^(j+g)) hK hV hE hR hC hD
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)]
  rw [amplified_nominal_ratio Z _ j g hZ (by positivity)]

theorem scalar_exceptional_bound (s μ H K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z)
    (hs:s*V≤μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)):
    s/V*(V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) ≤
    μ*H*(V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6)) := by
  have hdiv:=div_le_div_of_nonneg_right hs (sq_nonneg V)
  have he:s*V/V^2=s/V:=by field_simp
  rw [he] at hdiv
  calc
    _≤(μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)/V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6):=by
      gcongr
    _=μ*H*(K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)):=by ring
    _=_:=by rw [exceptional_core_log K V E R C D Z j g hK hV hE hR hC hD hZ]

theorem actual_nominal_cancellation
    (I J E : Ideal ActualEisensteinCubic.O) (hE:E≠0)
    (K V Z j g : ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z):
    let C : ℝ := (commonPart I J).absNorm;
    let D : ℝ := (commonPart J I).absNorm;
    let N : ℝ := E.absNorm;
    let R : ℝ := (Ideal.span {activeConductor I J}).absNorm;
    K*Real.sqrt (C*D)/(N*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(N^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (firstNominalScale I J E K V)+g)/6) := by
  exact exceptional_core_log K V _ _ _ _ Z j g hK hV (norm_pos E hE)
    (active_norm_pos I J) (norm_pos _ (commonPart_ne_zero I J))
    (norm_pos _ (commonPart_ne_zero J I)) hZ

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI

end Source874

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstWholeAssembly.lean; sha256: 95c1de55452cd88256c2f105b94767fe7a57bce40341c2322f6c4a50393f1342 -/
section Source875
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeAssembly
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy
open CenteredMomentFirstAssembly CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstWholeKernel
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

 theorem finite_whole_children {ι α β : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ l,Supported (Ideal.span {b l}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ l,ConcretePrimeRowBridge.goodLambda^2∣b l-1)
    (har : ∀ i,IsCoprime (a i) (finitePrimeModulus P))
    (hbr : ∀ l,IsCoprime (b l) (finitePrimeModulus P))
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => d l*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*
                wholeKernel W V (K₀*H₀/(A₀*B₀))
                  (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
                  (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀)) := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let kr := k/‖eisEmbedding r‖^2
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
    ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)
  let KK := fun i l => wholeKernel W V (K₀*H₀/(A₀*B₀))
    (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
    (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀))
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2) =
      F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      have hh' := dilated_frequency_whole_kernel P hcop hg hchar j hj0 hj6 e
        (a i) (b l) (ha i) (hb l) (hab.mul_right (har i)) (hbr l) k hk h hh
        W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
      dsimp only at hh'
      calc
        _ = (c i*star (d l))*(dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h*
          windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) := by ring
        _ = _ := by rw [hh'];dsimp only [F,KK,kr,r,ρ];ring
    · simp [hab]
  calc
    _ = F*(∑ i∈S,∑ l∈T,
      ((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      simpa only [mul_assoc] using ht i l
    _ = _ := congrArg (fun z => F*z)
      (finite_first_children S T a b ha hb hpa hpb c d e r ρ (finiteSexticRow_mul P hg j) h KK)

end SevenEighths.CenteredMomentFirstWholeAssembly

end

end OAI

end Source875

/- Original source: OAI/NumberTheory/DirichletL/Moments/ChildEnergy.lean; sha256: 4a3d78b6f6b0a86792fb8d95cf27541bb59e795553ee6783c56d62ef2dd63071 -/
section Source876
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) z)) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) z) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) z‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentChildEnergy

end

end OAI

end Source876

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedChild.lean; sha256: 773dc16de3bf361d1d51593843a3843128433ef0fa14690e1b5f3659c29e9df1 -/
section Source877
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentReflectedChild
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth CenteredMomentChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem finite_reflected_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c (-z)‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hh := finite_energy_le_gaussEnergy S a ha c W K hK (rows.image Neg.neg) hW
    (by intro z hz;obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy hxy
    exact neg_injective hxy

theorem whole_kernel_reflected_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) (-z))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) (-z)) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_reflected_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentReflectedChild

end

end OAI

end Source877

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstChildBound.lean; sha256: 9380d9bde59006a69ba38ccfb8fcde63e8950df89c1cc2f34c687cf44f6dab9a -/
section Source878
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildBound
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_first_ray_divisor_bound (L : Finset (Ideal O))
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (firstPhaseTable) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (firstPhaseTable_mass)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem first_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (q : O → ℂ) (K : O → α → β → ℂ) :
    (∑ z∈rows,q z*∑ i∈S,∑ j∈T,
      ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
        (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*K z i j)=
      ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑ z∈rows,(q z*ρ e)*∑ i∈S,∑ j∈T,
              ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) z)*
                star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                  gaussRow (b j) (hb j) (-z)))*K z i j := by
  simp_rw [finite_first_children S T a b ha hb hpa hpb c d e r ρ hρ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem whole_kernel_first_child_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i,0≤M i)
    (hV : ∀ i y,V i y≠0 → |y|≤M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,0<R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j})),
      (∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1) →
      (∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1) →
      ∀ (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ),
      (∀ x y,ρ (x*y)=ρ x*ρ y) → ‖ρ e‖≤1 →
      ∀ (q : O → ℂ) (u : α → ℝ) (v : β → ℝ) (ρ₀ x : O → ℝ),
      (∀ z∈rows,‖q z‖≤1) →
      (∀ z∈rows,‖V 0 (ρ₀ z)‖≤1) → (∀ z∈rows,‖V 1 (x z)‖≤1) →
      ∀ (U : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₁ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₂ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ χ : RayCharacter,∀ t : ℝ,
        (gaussEnergy S a ha (fun i =>
          divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
            columnPhase (V 2) (u i) t) U K).re≤(B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ ξ : RayCharacter,∀ t : ℝ,
        (gaussEnergy T b hb (fun j =>
          divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) ξ j*
            star (columnPhase (V 3) (v j) t)) U K).re≤(B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A*‖∑ z∈rows,q z*∑ i∈S,∑ j∈T,
        ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
          (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*
            wholeKernel W V R (ρ₀ z) (x z) (u i) (v j)‖≤
        C*∑ L∈divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_reflected_gauss_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T a b ha hb hpa hpb c d e r ρ hρ hρe q u v ρ₀ x hq hV₀ hV₁ U K hK hU hmajor
    B₁ B₂ hB₁ hB₂ hleft hright
  rw [first_row_children rows S T a b ha hb hpa hpb c d e r ρ hρ]
  apply finite_first_ray_divisor_bound _ _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ)
    (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹))
    u v ρ₀ x (fun z => q z*ρ e)
    (fun z hz => by rw [norm_mul];exact (mul_le_of_le_one_left (norm_nonneg _) (hq z hz)).trans hρe)
    hV₀ hV₁ U K hK hU hmajor (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL)
    (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentFirstChildBound

end

end OAI

end Source878

/- Original source: OAI/NumberTheory/DirichletL/Moments/FirstPhysicalSource.lean; sha256: 71421215f1e4f0e2c5d5f56a750795520935626f73607599ea55803e94485aec -/
section Source879
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

def columns (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O)):Finset (Ideal O):=
  (residualPool D hD (supportedColumns S)).filter (fun I=>IsCoprime C I)

lemma column_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))
    (a:columns C D hD S):Supported (a:Ideal O):=
  residualPool_supported D hD S ⟨a.val,(Finset.mem_filter.mp a.property).1⟩

def element (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):O:=
  CompletedGauss.primaryGenerator a

lemma element_span (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Ideal.span {element C D hD S a}=a:=primary_span_supported a (column_supported C D hD S a)

lemma element_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Supported (Ideal.span {element C D hD S a}):=by
  rw [element_span];exact column_supported C D hD S a

lemma element_primary (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    goodLambda^2∣element C D hD S a-1:=
  (CompletedGauss.primaryGenerator_spec a (supported_primaryGenerator_ne_zero a
    (column_supported C D hD S a))).2

lemma active_span_dvd (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D):Ideal.span {activeConductor C D}∣C:=by
  have hh:=activeConductor_span_dvd C D
  rw [(fixed_common_parts C D hC hD hCD).1] at hh
  exact hh

lemma element_coprime_active (C D B:Ideal O)(hC:C≠0)(hD:D≠0)(hB:B≠0)
    (hCD:primeSupport C=primeSupport D)(S:Finset (Ideal O))(a:columns C B hB S):
    IsCoprime (element C B hB S a) (activeConductor C D):=by
  rw [←Ideal.isCoprime_span_singleton_iff,element_span]
  exact (Finset.mem_filter.mp a.property).2.symm.of_isCoprime_of_dvd_right (active_span_dvd C D hC hD hCD)

def coefficient (η:Character)(m A:O)(t:ℝ)(c:Ideal O→ℂ)(D:Ideal O)
    (I:Ideal O):ℂ:=c (D*I)*CenteredMomentHeckeExpansion.rowWeight η m A 1 t I

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D)):ℂ:=
  (UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)

def block (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
          (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def scalar (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))(K A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  inactiveWeight C D E * ((k:ℂ)*canonicalNormalizedGauss (activePrime C D)
    (activeCoprime C D) (activeGood C D hC) (activeExponent C D)/
      ((‖eisEmbedding (activeConductor C D)‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))

theorem block_eq_whole (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0<K)(hK₀:0<K₀)(hH₀:0<H₀)(hA₀:0<A₀)(hB₀:0<B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖eisEmbedding r‖^2)/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
            (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)):=by
  dsimp only
  have he:primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E≠0:=
    supported_element_ne_zero _ (subsetGenerator_supported C D hC E)
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
  unfold block scalar
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hcop:IsCoprime (element C C hC.1 S a) (element C D hD.1 S b)↔
      IsCoprime (a:Ideal O) (b:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,element_span,element_span]
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true,hcop]
    have hh:=dilated_frequency_whole_kernel (activePrime C D) (activeCoprime C D)
      (activeGood C D hC) (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)
      (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
      (element C C hC.1 S a) (element C D hD.1 S b)
      (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
      ((hcop.mpr hab).mul_right (element_coprime_active C D C hC.1 hD.1 hC.1 hCD S a))
      (element_coprime_active C D D hC.1 hD.1 hD.1 hCD S b)
      _ hk h (hrows h hh) W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
    dsimp only at hh
    change inactiveWeight C D E * (_*_*_*_)=_
    calc
      _=inactiveWeight C D E*(coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (dilatedFrequency (activePrime C D) (activeCoprime C D) (activeGood C D hC)
          (activeExponent C D) (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
          (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2) h *
        windows V _ _ _ _ K₀ H₀ A₀ B₀ * EisensteinSchwartzPoisson.paperRadialFourier W _):=by
          dsimp [dilatedFrequency,activeFunction,activeConductor];ring
      _=_:=by rw [hh];dsimp only [activeConductor];ring
  · simp [hab,hcop]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end Source879
