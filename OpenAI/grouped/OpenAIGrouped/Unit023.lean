import OpenAIGrouped.Unit022
import OpenAIGrouped.Unit017
import OpenAIGrouped.Unit016
import OpenAIGrouped.Unit019
import OpenAIGrouped.Unit021
import OpenAIGrouped.Unit011
import OpenAIGrouped.Unit015
import OpenAIGrouped.Unit013
import OpenAIGrouped.Unit018

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainGlobalActual.lean; sha256: 2303be8a4fe4fc71cc96f76445d16263616e03dce34ef54e952f2b4aa6c1788f -/
section Source920
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalBound

 theorem global_polynomial_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,Cm,hCm,hm⟩:=profile_strip_decay a b ha (1/2) 2 6
  obtain ⟨Cg,hCg,hg⟩:=original_upper_strip (3/10) (by norm_num)
  let E:=HeckeReciprocalBound.bound 2
  have hE:0≤E:=tsum_nonneg (fun _=>norm_nonneg _)
  let C:ℝ:=Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)
  have hC:0<C:=div_pos (mul_pos hCm (add_pos_of_pos_of_nonneg
    (mul_pos hCg (by positivity)) (mul_nonneg hE Real.pi_pos.le))) (by positivity)
  refine ⟨S,C,hC,?_⟩
  intro W hWs χ hχ D freq hD
  let Q:ℝ:=χ.modulus.absNorm
  let V:ℝ:=3+|freq|
  let B:ℝ:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB:0≤B:=apply_nonneg _ _
  have hQ:1≤Q:=by
    dsimp [Q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤V:=by dsimp [V]; linarith [abs_nonneg freq]
  have hQ0:0≤Q:=zero_le_one.trans hQ
  have hrad:((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)≤Q:=radical_norm_le_modulus χ
  have hrad0:0≤((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ):=Nat.cast_nonneg _
  have hcost:Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)≤Q:=by
    calc
      _≤Q^(3/5:ℝ)*Q^((1/10+(3/10)):ℝ):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hrad0 hrad (by norm_num)) (Real.rpow_nonneg hQ0 _)
      _=Q:=by rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]; norm_num
  have hgrowth (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      ‖series χ false ((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)‖≤(Cg*Q*V^2)*(1+|t|)^2:=by
    have hs:-(1/10:ℝ)≤(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).re:=by simp [HeckeDyadic.shift]; linarith [hx.1]
    have hh:=hg χ hχ _ hs
    have him:(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).im=t-freq:=by simp [HeckeDyadic.shift,sub_eq_add_neg]
    rw [him] at hh
    have ht:3+|t-freq|≤V*(1+|t|):=by
      dsimp [V]
      have hab:=abs_sub t freq
      nlinarith [abs_nonneg t,abs_nonneg freq,mul_nonneg (abs_nonneg t) (abs_nonneg freq)]
    apply hh.trans
    change Cg*Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)*
      (3+|t-freq|)^2≤_
    have hc:=mul_le_mul (mul_le_mul_of_nonneg_left hcost hCg.le)
      (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (mul_nonneg hCg.le hQ0)
    convert hc using 1 <;> ring
  have hb:=finite_strip_bound χ hχ W a b ha hWs (W.smooth ⊤) D freq (Cm*B) (Cg*Q*V^2)
    hD (mul_nonneg hCm.le hB) (by positivity) (hm W hWs) hgrowth
  have hQV:1≤Q*V^2:=one_le_mul_of_one_le_of_one_le hQ (one_le_pow₀ hV)
  have he:E≤E*(Q*V^2):=le_mul_of_one_le_right hE hQV
  apply hb.trans
  dsimp only [C]
  change _≤Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)*B*Q*V^2
  have hCe: Cm*B*E*Real.pi≤Cm*B*(E*(Q*V^2))*Real.pi:=by gcongr
  dsimp only [E] at hCe ⊢
  calc
    _≤(1/(2*Real.pi))*
      (Cm*B*(Cg*Q*V^2)*Real.pi+3*(Cm*B)*(Cg*Q*V^2)+
       Cm*B*(HeckeReciprocalBound.bound 2*(Q*V^2))*Real.pi):=
      mul_le_mul_of_nonneg_left (add_le_add_right hCe _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentPlainGlobalActual

end

end OAI

end Source920

/- Original source: OAI/NumberTheory/DirichletL/Moments/InductionEnergy.lean; sha256: 010e75c398c3a7a7a50399baa3b293371367ec45a6fd7b81f9662be6e787ce44 -/
section Source921
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma plain_absolute (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b B X:ℝ)
    (hb:0≤b) (hB:0≤B) (hX:0<X) (hs:Function.support W⊆Set.Iic b)
    (hW:∀x,‖W x‖≤B) : ‖rowTwistedSum η m A z W t X‖≤(128*b*B)*X := by
  rw [rowTwistedSum_eq_weight]
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) B (mul_nonneg hb hX.le) hB (by change rowWeight η m A z t (0:Ideal O)*_=0; rw [map_zero,zero_mul])
    (fun I=>by rw [norm_mul]; exact (mul_le_mul (rowWeight_norm_le_one_all η m A z t I)
      (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun I hi=>(div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hi)))
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma positive_squared_absolute (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i) := by
  let L:ℝ:=(128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i)
  let T:ℝ:=X₁*X₂*∏i,P i
  have hL:0≤L:=mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hB i)))
  have hT:0<T:=mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hsum:‖(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏i,rowSlot η m A z (S i) (β i) t‖≤L*T := by
    rw [norm_mul,norm_mul,norm_prod]
    have hp:=Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>norm_nonneg (rowSlot η m A z (S i) (β i) t))
      (fun i _=>rowSlot_bound η m A z (S i) (β i) t (b i*P i) (B i)
        (mul_nonneg (hb i) (hP i).le) (hB i) (hβ i) (hN i))
    have hq:=mul_le_mul
      (mul_le_mul (plain_absolute η m A z t W₁ b₁ B₁ X₁ hb₁ hB₁ hX₁ hs₁ hW₁)
        (plain_absolute η m A z t W₂ b₂ B₂ X₂ hb₂ hB₂ hX₂ hs₂ hW₂) (norm_nonneg _) (by positivity))
      hp (by positivity) (by positivity)
    apply hq.trans_eq
    simp only [mul_left_comm (B _) (b _),mul_assoc,Finset.prod_mul_distrib]
    dsimp [L,T]
    simp only [Finset.prod_mul_distrib]
    ring
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _≤(L*T)^2/T:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hT.le
    _=L^2*T:=by field_simp

omit [DecidableEq ι] in
theorem energy_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K≤
      diagonalControl Φ*max 1 K*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)) := by
  let E:ℝ:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    positive_squared_absolute η m A z t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂
      hX₁ hX₂ hs₁ hs₂ hW₁ hW₂ S β P b B hP hb hB hβ hN
  have hs:=bounded_radial_summable
    (fun z:O=>positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K hK
  have hbnd:=hs.tsum_le_tsum (g:=fun z:O=>E*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left E)
  rw [tsum_mul_left] at hbnd
  exact hbnd.trans ((mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) hE).trans_eq (mul_comm _ _))

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI

end Source921

/- Original source: OAI/NumberTheory/DirichletL/Moments/BottomStage.lean; sha256: daca85093d88bf17cbab0b0d483b6f988b68d71971b1846efd44bdd6a27bb4cb -/
section Source922
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

 def positiveEnergy (s:Data ι) (r:Radial) : ℝ :=
  CenteredMomentInductionEnergy.energy s.η s.m s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P
    s.X₁ s.X₂ r.keep r.profile r.scale

 def profileMass (s:Data ι) (B₁ B₂:ℝ) : ℝ :=
  ((128*max 0 s.b₁*B₁)*(128*max 0 s.b₂*B₂)*(∏i,128*max 0 (s.hi i)*s.M i))^2

 theorem actual_absolute (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂) :
    positiveEnergy s r≤diagonalControl r.profile*max 1 r.scale*profileMass s B₁ B₂*
      (s.X₁*s.X₂*∏i,s.P i) := by
  have hs₁:Function.support s.W₁⊆Set.Iic (max 0 s.b₁):=
    by
      intro x hx
      change x≤max 0 s.b₁
      have hs:x≤s.b₁:=s.support₁ hx
      exact hs.trans (le_max_right 0 s.b₁)
  have hs₂:Function.support s.W₂⊆Set.Iic (max 0 s.b₂):=
    by
      intro x hx
      change x≤max 0 s.b₂
      have hs:x≤s.b₂:=s.support₂ hx
      exact hs.trans (le_max_right 0 s.b₂)
  have hN:∀i,∀I∈s.slots i,s.coefficient i I≠0 →
      (Ideal.absNorm I:ℝ)≤max 0 (s.hi i)*s.P i:=by
    intro i I hI hn
    have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=by
      intro hw
      apply hn
      simp only [Data.coefficient,hw,mul_zero]
    have hs:=s.support i hw
    exact (div_le_iff₀ (s.P_pos i)).mp (hs.2.trans (le_max_right _ _))
  have hh:=energy_absolute s.η s.m s.A s.t s.W₁ s.W₂
    (max 0 s.b₁) (max 0 s.b₂) B₁ B₂ s.X₁ s.X₂ (le_max_left _ _) (le_max_left _ _) hB₁ hB₂
    s.X₁_pos s.X₂_pos hs₁ hs₂ hW₁ hW₂
    s.slots s.coefficient s.P (fun i=>max 0 (s.hi i)) s.M s.P_pos
    (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i)) s.coefficient_bound
    hN r.keep r.profile r.scale r.scale_pos
  exact hh.trans_eq (by unfold profileMass;ring)

 theorem actual_bottom_band (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂)
    (Z m M σ:ℝ) (hZ:1<Z) (hK:1≤r.scale) (hm:m≤σ)
    (hrow:r.scale≤Z^m) (hsource:s.X₁*s.X₂*∏i,s.P i≤Z^M) :
    positiveEnergy s r≤(diagonalControl r.profile*profileMass s B₁ B₂)*Z^(M+σ) := by
  have hh:=actual_absolute s r B₁ B₂ hB₁ hB₂ hW₁ hW₂
  rw [max_eq_right hK] at hh
  have hp:0≤profileMass s B₁ B₂:=sq_nonneg _
  have hd:0≤diagonalControl r.profile:=diagonalControl_nonneg _
  have hs:0≤s.X₁*s.X₂*∏i,s.P i:=(mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))).le
  have hpow:r.scale*(s.X₁*s.X₂*∏i,s.P i)≤Z^(M+σ):=by
    apply (mul_le_mul hrow hsource hs (Real.rpow_nonneg (by linarith) _)).trans
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply hh.trans
  calc
    _=(diagonalControl r.profile*profileMass s B₁ B₂)*(r.scale*(s.X₁*s.X₂*∏i,s.P i)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hpow (mul_nonneg hd hp)

end SevenEighths.CenteredMomentBottomStage

end

end OAI

end Source922

/- Original source: OAI/NumberTheory/DirichletL/Moments/CoreFloor.lean; sha256: 1188d36e5d356fc2c0dc9ad25320b485b145d4f451fe85f45716f1866d2e5df4 -/
section Source923
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

 theorem zero_energy_eq (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

 theorem zero_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂)(hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r≤
      diagonalControl r.profile*max 1 r.scale*((128*b₁*B₁)*(128*b₂*B₂))^2*(X₁*X₂):=by
  rw [zero_energy_eq]
  have h:=energy_absolute (ι:=Fin 0) η m A t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂
    hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
    (fun _=>∅) (fun _=>0) (fun _=>1) (fun _=>1) (fun _=>1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    r.keep r.profile r.scale r.scale_pos
  simpa only [Fin.prod_univ_zero,mul_one,mul_assoc] using h

 theorem zero_padded_core (η:Character) (mask A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial)(Z m q n₁ n₂ ρ δ:ℝ)(hZ:1<Z)(hm:0≤m)(hq:0≤q)
    (hscale:r.scale=Z^m)(hfloor:m+q≤ρ)(hcore:n₁+n₂≤m+q+δ):
    zeroEnergy η mask A t W₁ W₂ (Z^n₁) (Z^n₂) r≤
      (diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*Z^(m+q+ρ+δ):=by
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have h:=zero_absolute η mask A t W₁ W₂ b₁ b₂ B₁ B₂ (Z^n₁) (Z^n₂)
    hb₁ hb₂ hB₁ hB₂ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    hs₁ hs₂ hW₁ hW₂ r
  rw [hscale,max_eq_right (Real.one_le_rpow hZ.le hm)] at h
  have hp:Z^m*(Z^n₁*Z^n₂)≤Z^(m+q+ρ+δ):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply h.trans
  calc
    _=(diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*(Z^m*(Z^n₁*Z^n₂)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (mul_nonneg (diagonalControl_nonneg _) (sq_nonneg _))

 theorem whole_slot_norm {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A z:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
    (S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)(P:ι→ℝ)(hP:∀i,0<P i):
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2=
      ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2 *
        (∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i):=by
  have hp:0<∏i,P i:=Finset.prod_pos (fun i _=>hP i)
  unfold positiveSlotRow zeroRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos (mul_pos hX₁ hX₂) hp),
    CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos hX₁ hX₂)]
  rw [norm_mul,norm_prod,mul_pow,Finset.prod_div_distrib,Finset.prod_pow]
  ring

 theorem slot_energy_reduction {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)
    (P:ι→ℝ)(hP:∀i,0<P i)(r:Radial)(E:ℝ)
    (hslots:∀z,r.keep z→(∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i)≤E):
    energy η m A t W₁ W₂ S β P X₁ X₂ r.keep r.profile r.scale≤
      E*zeroEnergy η m A t W₁ W₂ X₁ X₂ r:=by
  obtain ⟨B,hB⟩:=product_bounded (ι:=Fin 0) η m A t (Real.sqrt (X₁*X₂):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ (fun _=>∅) (fun _=>0)
  have hz:∀z,‖zeroRow η m A z t W₁ W₂ X₁ X₂‖≤B:=by
    simpa [zeroRow] using hB
  have hsum:=bounded_radial_summable _ B hz r.keep r.profile r.scale r.scale_pos
  obtain ⟨B',hB'⟩:=product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hspos:=bounded_radial_summable _ B' hB' r.keep r.profile r.scale r.scale_pos
  change Summable (fun z:O=>if r.keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) at hspos
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hspos.tsum_le_tsum _ (hsum.mul_left E)
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk]
    rw [whole_slot_norm η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ S β P hP]
    have hb:=mul_le_mul_of_nonneg_left (hslots z hk)
      (sq_nonneg ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖)
    have hh:=mul_le_mul_of_nonneg_right hb (r.nonneg z)
    nlinarith only [hh]
  · simp [hk]

end SevenEighths.CenteredMomentCoreFloor

end

end OAI

end Source923

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainGlobalEnergy.lean; sha256: 57fd327c348fdc6d27d08b0ec13d2ea27657eb119acfb67918e147e476f4383e -/
section Source924
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentPlainGlobalEnergy
open HeckeFamily HeckeDyadic CenteredMomentCoreFloor
open CenteredMomentPlainGlobalActual CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentDetectorDictionary
open HeckeInverseAmplification CompletedHeight CenteredMomentHeckeHeight
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentAbsoluteEnergy
local notation "O"=>HeckeFamily.O

 theorem plain_height_norm (χ:Character)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(t X:ℝ)(hX:0<X):
    ‖(Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X‖=
      ‖polynomial χ false W X 0 t‖:=by
  have hp:(normPowerProfile W a b ha hs hW t:ℝ→ℂ)=twistProfile W 0 t:=by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm (Complex.I) (t:ℂ)]
    ring
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hi:idealSum χ (normPowerProfile W a b ha hs hW t) X=
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X:=by
    simp [idealSum,twistedIdealSum]
  rw [hi]
  have he:(Real.sqrt X:ℂ)⁻¹*((X:ℂ)^(Complex.I*t)*
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X)=
      (X:ℂ)^(Complex.I*t)*polynomial χ false W X 0 t:=by
    rw [←polynomial_twistProfile,←hp,plain_zero_height _ _ X hX]
    ring
  rw [he,norm_mul,norm_real_imaginary_power X t hX,one_mul]

 theorem zero_row_norm (η χ:Character)(mask A z:O)
    (hrow:∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)
    (W₁ W₂:ℝ→ℂ)(a b:ℝ)(ha:0<a)(hs₁:Function.support W₁⊆Set.Icc a b)
    (hs₂:Function.support W₂⊆Set.Icc a b)(hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    ‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖=
      ‖polynomial χ false W₁ X₁ 0 t‖*‖polynomial χ false W₂ X₂ 0 t‖:=by
  unfold zeroRow
  rw [rowTwistedSum_eq η χ mask A z hrow,rowTwistedSum_eq η χ mask A z hrow,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  have he:(Real.sqrt X₂:ℂ)⁻¹*(Real.sqrt X₁:ℂ)⁻¹*
      (twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂)=
      ((Real.sqrt X₁:ℂ)⁻¹*twistedIdealSum χ W₁ t X₁)*
      ((Real.sqrt X₂:ℂ)⁻¹*twistedIdealSum χ W₂ t X₂):=by ring
  rw [he,norm_mul,plain_height_norm χ W₁ a b ha hs₁ hW₁ t X₁ hX₁,
    plain_height_norm χ W₂ a b ha hs₂ hW₂ t X₂ hX₂]

 theorem radial_bound_on_keep (F:O→ℂ)(r:Radial)(B:ℝ)(hB:0≤B)
    (hF:∀z,r.keep z→‖F z‖≤B):
    (∑'z:O,if r.keep z then ‖F z‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0)≤
      diagonalControl r.profile*max 1 r.scale*B^2:=by
  have hb:∀z,‖(if r.keep z then F z else 0)‖≤B:=by
    intro z
    by_cases h:r.keep z
    · simpa only [ite_eq_left h] using hF z h
    · simpa only [ite_eq_right h,norm_zero] using hB
  have hs:=bounded_radial_summable _ B hb r.keep r.profile r.scale r.scale_pos
  have heq:(fun z:O=>if r.keep z then
      ‖(if r.keep z then F z else 0)‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0)=
      (fun z:O=>if r.keep z then ‖F z‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0):=by
    funext z
    split_ifs <;> rfl
  rw [heq] at hs
  have hh:=hs.tsum_le_tsum (g:=fun z:O=>B^2*‖r.profile (‖eisEmbedding z‖^2/r.scale)‖) (fun z=>by
    split_ifs with hk
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z hk) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable r.profile r.scale r.scale_pos).mul_left (B^2))
  rw [tsum_mul_left] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (radial_weight_lattice_bound_all r.profile r.scale r.scale_pos) (sq_nonneg B)).trans_eq (by ring))

 theorem zero_all_lengths_floor (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(mask A:O)(r:Radial)(χ:O→Character),
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→∀n,elementCoeff (χ z) n=
        CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)→
    ∀(Z m q ρ Cscale t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→0≤Cscale→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Cscale*Z^(m+q))→
    zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤
      C*Cscale^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hpoly⟩:=global_polynomial_bound a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ η mask A r χ hχ hrow Z m q ρ Cscale t X₁ X₂ hZ hm hq hCs hscale hfloor hX₁ hX₂ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let V:=3+|t|
  let Q:=Cscale*Z^(m+q)
  have hQ:0≤Q:=mul_nonneg hCs (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  let B:=C^2*(B₁*B₂)*Q^2*V^4
  have hB:0≤B:=by dsimp [B]; positivity
  have hpoint (z:O)(hz:r.keep z):‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖≤B:=by
    rw [zero_row_norm η (χ z) mask A z (hrow z hz) W₁ W₂ a b ha hs₁ hs₂
      (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ (zero_lt_one.trans_le hX₁) (zero_lt_one.trans_le hX₂)]
    have hb₁:=hpoly W₁ hs₁ (χ z) (hχ z hz) X₁ t hX₁
    have hb₂:=hpoly W₂ hs₂ (χ z) (hχ z hz) X₂ t hX₂
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 t‖≤C*B₁*Q*V^2:=
      hb₁.trans (by dsimp [V]; gcongr; exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 t‖≤C*B₂*Q*V^2:=
      hb₂.trans (by dsimp [V]; gcongr; exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hb:=radial_bound_on_keep (fun z=>zeroRow η mask A z t W₁ W₂ X₁ X₂) r B hB hpoint
  change zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤_ at hb
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at hb
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd:=diagonalControl_nonneg r.profile
  apply hb.trans
  calc
    _=(C^4*Cscale^4*diagonalControl r.profile*(B₁*B₂)^2*V^8)*(Z^m*(Z^(m+q))^4):=by
      dsimp [B,Q]; ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentPlainGlobalEnergy

end

end OAI

end Source924

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainPositiveScale.lean; sha256: b0d5a465a1920466257c365f7a8a2f66051b8fbd9d1ee224fc2be9d0cf5b88d9 -/
section Source925
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentPlainPositiveScale
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalActual CenteredMomentPlainGlobalEnergy
open CenteredMomentHeckeTwist CenteredMomentDetectorDictionary

 theorem small_polynomial (χ:Character)(W:SchwartzMap ℝ ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(D freq:ℝ)(hD:0<D)(hD1:D≤1):
    ‖polynomial χ false W D 0 freq‖≤
      (128*max 0 b)*(SchwartzMap.seminorm ℝ 0 0 W):=by
  let B:=SchwartzMap.seminorm ℝ 0 0 W
  have hB:0≤B:=apply_nonneg _ _
  have hWs':Function.support (W:ℝ→ℂ)⊆Set.Icc a (max 0 b):=by
    intro x hx
    exact ⟨(hWs hx).1,(hWs hx).2.trans (le_max_right _ _)⟩
  have hs:=twistedIdealSum_absolute χ W a (max 0 b) B ha (le_max_left _ _) hB hWs' (W.smooth ⊤)
    (fun x=>SchwartzMap.norm_le_seminorm ℝ W x) freq D hD
  rw [←plain_height_norm χ W a b ha hWs (W.smooth ⊤) freq D hD,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hsq:(Real.sqrt D)^2=D:=Real.sq_sqrt hD.le
  have hroot:0<Real.sqrt D:=Real.sqrt_pos.mpr hD
  have hle:Real.sqrt D≤1:=by exact (Real.sqrt_le_one).mpr hD1
  have he:(Real.sqrt D)⁻¹*((128*max 0 b*B)*D)=(128*max 0 b*B)*Real.sqrt D:=by
    calc
      _=(128*max 0 b*B)*((Real.sqrt D)⁻¹*(Real.sqrt D*Real.sqrt D)):=by rw [←pow_two,hsq];ring
      _=_:=by rw [inv_mul_cancel_left₀ hroot.ne']
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hle

 theorem global_positive_scale (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Set.Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,0<D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,C,hC,hg⟩:=global_polynomial_bound a b ha
  let S':Finset (ℕ×ℕ):=insert (0,0) S
  let C':ℝ:=C+128*max 0 b
  have hC':0<C':=add_pos_of_pos_of_nonneg hC (by positivity)
  refine ⟨S',C',hC',?_⟩
  intro W hWs χ hχ D freq hD
  have hB:0≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hsup:S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) W
  have hzero:SchwartzMap.seminorm ℝ 0 0 W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (s:=S') (i:=(0,0)) (x:=W) (Finset.mem_insert_self (0,0) S)
  have hQ:1≤(χ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤(3+|freq|)^2:=one_le_pow₀ (by linarith [abs_nonneg freq])
  by_cases hD1:1≤D
  · apply (hg W hWs χ hχ D freq hD1).trans
    gcongr
    dsimp [C']; linarith [le_max_left (0:ℝ) b]
  · have hh:=small_polynomial χ W a b ha hWs D freq hD (le_of_lt (lt_of_not_ge hD1))
    apply hh.trans
    calc
      _≤C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W):=by
        apply mul_le_mul _ hzero (apply_nonneg _ _) hC'.le
        dsimp [C'];linarith
      _≤(C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))*
          ((χ.modulus.absNorm:ℝ)*(3+|freq|)^2):=
        le_mul_of_one_le_right (mul_nonneg hC'.le hB) (one_le_mul_of_one_le_of_one_le hQ hV)
      _=_:=by ring

end SevenEighths.CenteredMomentPlainPositiveScale

end

end OAI

end Source925

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionNegligible.lean; sha256: 7081015bb3bc5d7ef84192cf1ba0753d5b12ab96db544376bad6dbef28891d2c -/
section Source926
namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson

lemma normalized_power_eq (Y : ℝ) (hY : 0<Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

theorem actual_reflected_small_negligible (a b xi saving : ℝ) (ha : 0<a) (hxi : 0<xi) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Z^(-xi) →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max (2:ℝ) (saving/xi+1/2))
  have hB2 : 2≤B := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hB))
  have hBp : 0≤(B:ℝ)-1/2 := by have := (le_max_left _ _).trans_lt hB;linarith
  have hsav : saving≤xi*((B:ℝ)-1/2) := by
    have hh := (le_max_right _ _).trans_lt hB
    have hh' : saving/xi≤(B:ℝ)-1/2 := by linarith
    exact (div_le_iff₀ hxi).mp hh' |>.trans_eq (mul_comm _ _)
  obtain ⟨n,hn⟩ := actual_reflected_absolute_bound a b ha B hB2
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply (hbound η t Y hY).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [normalized_power_eq Y hY B]
  calc
    _≤(Z^(-xi))^((B:ℝ)-1/2) := Real.rpow_le_rpow hY.le hYZ hBp
    _=Z^((-xi)*((B:ℝ)-1/2)) := (Real.rpow_mul hz.le _ _).symm
    _≤Z^(-saving) := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem actual_reflected_upper_negligible (a b xi saving L Cscale : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hCscale : 0<Cscale) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨n,hn⟩ := actual_reflected_discarded_bound a b ha A 2 (by omega)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hCscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*(1+‖t‖)^n*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A := hbound η t Y _ hY hR
    _≤C*(1+‖t‖)^n*(Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*(1+‖t‖)^n*Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end Source926

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionTailMass.lean; sha256: 1a3fedf5e78b254dc4fdf1582f7372efddd7ad9dd9761dd096e6a64620619c33 -/
section Source927
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

lemma dual_scale_bounds (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S)
    (H : SmoothIdeal S) (Q X U : ℝ) (hQ : 0<Q) (hX : 0<X)
    (hcap : Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤U*X) :
    0<Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val) ∧
    Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)≤U := by
  have hd := subset_product_norm_pos D (fun P hP=>hS P (hD hP))
  have hh := norm_pos H.val
  refine ⟨by positivity,?_⟩
  calc
    _≤Q*(Ideal.absNorm (∏P∈D,P):ℝ)/X :=
      div_le_div_of_nonneg_left (by positivity) hX
        (by nlinarith [restoration_norm_one S H])
    _≤Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (subset_norm_le S D hS hD) hQ.le) hX.le
    _≤U := (div_le_iff₀ hX).mpr hcap

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : Character)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB

theorem actual_deleted_discarded_negligible (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
        (η ηi χ : Character)(t Q X Z : ℝ),1≤Z → 0<Q → 0<X →
        Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
        let F := fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x
        (∀D∈S.powerset,Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0)) ∧
        ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0‖≤
          C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_reflected_upper_negligible a b xi saving L Cscale ha hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound ε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro S hS η ηi χ t Q X Z hZ hQ hX hcap
  dsimp only
  have hh := hDb S hS η ηi
    (fun E H=>HeckeDyadic.polynomial χ false
      (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
        paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*(1+‖t‖)^n*Z^(-saving)) (by positivity) (by
      intro E hE H
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X (Cscale*Z^L) hQ hX hcap
      exact hCb χ t _ Z hZ hy.1 hy.2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI

end Source927

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedAnnuli.lean; sha256: 4a067e3fbaad129c3fac07ed6245a5dd7084f5c99f96dbaab430f6686b5f555d -/
section Source928
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem logWindow_tsupport : tsupport logWindow ⊆ Icc (-Real.log 4) 0 :=
  closure_minimal logWindow_support isClosed_Icc

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

def logWindowSchwartz : 𝓢(ℝ,ℂ) := logWindow_compact.toSchwartzMap logWindow_smooth

theorem logWindow_derivative_window (i : ℕ) (v : ℝ)
    (hi : ‖iteratedFDeriv ℝ i logWindow v‖ ≠ 0) :
    1/4 ≤ Real.exp v ∧ |v| ≤ Real.log 4 := by
  have hv := logWindow_tsupport (support_iteratedFDeriv_subset i (norm_ne_zero_iff.mp hi))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  refine ⟨hl ▸ Real.exp_le_exp.mpr hv.1, abs_le.mpr ⟨hv.1,?_⟩⟩
  exact hv.2.trans (Real.log_nonneg (by norm_num))

theorem logWindow_derivative_bound (K : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ i≤K, ∀v : ℝ, ‖iteratedFDeriv ℝ i logWindow v‖≤C := by
  let C := 1+∑ i∈Finset.range (K+1), SchwartzMap.seminorm ℝ 0 i logWindowSchwartz
  have hsum := Finset.sum_nonneg (s:=Finset.range (K+1))
    (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 i) logWindowSchwartz)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro i hi v
  have hb := SchwartzMap.le_seminorm' ℝ 0 i logWindowSchwartz v
  have hc := Finset.single_le_sum (s:=Finset.range (K+1))
    (f:=fun j=>SchwartzMap.seminorm ℝ 0 j logWindowSchwartz)
    (fun j _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 j) logWindowSchwartz)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i logWindowSchwartz v‖≤C
  simpa only [pow_zero, one_mul] using hb.trans (by dsimp [C];linarith)

def reflected (W : ℝ→ℂ) (t : ℝ) : ℝ→ℂ :=
  paperRadialFourier (CompletedHeight.normTwistedSource W t)

theorem reflected_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiffOn ℝ ∞ (reflected W t) (Ioi 0) := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold reflected
  rw [←he]
  exact paperRadialFourier_contDiffOn _

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def logProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected W t) s logWindow_compact logWindow_smooth
    (reflected_smooth W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t v : ℝ) :
    logProfile W a b ha hs hW s hs0 t v =
      annularProfile (reflected W t) s (Real.exp v) := rfl

theorem logProfile_tsupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) :
    tsupport (logProfile W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected W t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem logProfile_finite_seminorm (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀s : ℝ, ∀hs0 : 0<s, ∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logProfile W a b ha hs hW s hs0 t) ≤
        C*(1+‖t‖)^J/(1+s)^B := by
  let K := H.sup Prod.snd
  obtain ⟨CW,hCW,hwin⟩ := logWindow_derivative_bound K
  obtain ⟨J,hJ⟩ := reflected_profile_height_control a b ha B K
  let D := 1+∑z∈H,(Real.log 4)^z.1*
    (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : 0<D := by
    have hn : 0≤∑z∈H,(Real.log 4)^z.1*
        (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW) := by positivity
    dsimp [D];linarith
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hEuler⟩ := hJ W hs hW
  refine ⟨D*CF/(1/4:ℝ)^B,by positivity,?_⟩
  intro s hs0 t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzK : z.2≤K := Finset.le_sup hz
  have hb := positive_log_uniform_seminorm logWindow (reflected W t)
    s (1/4) (Real.log 4) CW (CF*(1+‖t‖)^J) B z.2 z.1
    logWindow_compact logWindow_smooth (reflected_smooth W a b ha hs hW t)
    hs0 (by norm_num) (by norm_num) hlog hCW.le (by positivity)
    (fun i hi v => hwin i (hi.trans hzK) v)
    (fun v hv => by obtain ⟨i,hi,hn⟩:=hv;exact logWindow_derivative_window i v hn)
    (fun i hi x hx => hEuler t i (hi.trans hzK) x hx.le)
  have hd : (Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)≤D := by
    have h := Finset.single_le_sum (s:=H)
      (f:=fun z=>(Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW))
      (fun z _ => by positivity) hz
    dsimp [D];linarith
  have hb' : (1/4:ℝ)^B*(1+s)^B*
      SchwartzMap.seminorm ℝ z.1 z.2 (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J) := by
    apply hb.trans
    rw [←Finset.sum_mul, ←mul_assoc]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hb'' : SchwartzMap.seminorm ℝ z.1 z.2
      (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J)/((1/4:ℝ)^B*(1+s)^B) :=
    (le_div_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb')
  exact hb''.trans_eq (by ring)

theorem annularProfile_support (F : ℝ→ℂ) (s : ℝ) :
    Function.support (annularProfile F s) ⊆ Icc (1/4) 1 := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_low x (le_of_not_ge hn)])
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_high x (le_of_not_ge hn)])

theorem annularProfile_zero (F : ℝ→ℂ) (s x : ℝ)
    (hx : x≤1/4 ∨ 1≤x) : annularProfile F s x=0 := by
  rcases hx with hx|hx
  · simp [annularProfile,annulus_zero_low x hx]
  · simp [annularProfile,annulus_zero_high x hx]

theorem annular_partition (F : ℝ→ℂ) (x : ℝ) (hx : 0<x) :
    (∑' n : ℤ,annularProfile F (dyadicScale n) (x/dyadicScale n))=F x := by
  have he (n : ℤ) : annularProfile F (dyadicScale n) (x/dyadicScale n)=
      (dyadicWeight n x:ℂ)*F x := by
    simp [annularProfile,dyadicWeight,mul_div_cancel₀,ne_of_gt (dyadicScale_pos n)]
  simp_rw [he]
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition x hx]
  simp

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0<dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (hf : ∀j,0≤f j) (hb : ∀j,f j≤q^j) (L : ℕ) :
    Summable (fun j=>f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=>q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=>hf (j+L)) (fun j=>hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=>hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=>annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=>annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=>annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤A) (hAB : A+1≤B) :
    Summable (fun j:ℕ=>annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=>annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=>annularMass_nonneg _ _) (fun j=>annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

theorem logProfile_dyadic_seminorm_sum (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) (hB : 2≤B) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
      Summable (fun n:ℤ=>Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)) ∧
      (∑'n:ℤ,Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t))≤
        C*(1+‖t‖)^J := by
  obtain ⟨J,hJ⟩ := logProfile_finite_seminorm a b ha H B
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hbound⟩ := hJ W hs hW
  have hmass := annularMass_summable B hB
  have hmass0 : 0≤∑'n:ℤ,annularMass B n := tsum_nonneg (annularMass_nonneg B)
  refine ⟨CF*(1+∑'n:ℤ,annularMass B n),by positivity,?_⟩
  intro t
  let f := fun n:ℤ=>Real.sqrt (dyadicScale n)*
    H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)
  have hf0 : ∀n,0≤f n := fun n=>
    mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hb : ∀n,f n≤(CF*(1+‖t‖)^J)*annularMass B n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound _ (dyadicScale_pos n) t)
      (Real.sqrt_nonneg (dyadicScale n))
    exact h.trans_eq (by unfold annularMass;ring)
  have hg := hmass.mul_left (CF*(1+‖t‖)^J)
  have hf := Summable.of_nonneg_of_le hf0 hb hg
  refine ⟨hf,(hf.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [show 0≤CF*(1+‖t‖)^J by positivity]

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI

end Source928

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedSeries.lean; sha256: 269aefaefad76d9792471893415586ce061cf52d8a88a85c7753aad4155e9e62 -/
section Source929
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

lemma dyadic_ideal_partition (η : Character) (F : ℝ→ℂ) (Y : ℝ) (hY : 0<Y) (I : NI) :
    (∑'n : ℤ,dyadicIdealTerm η F Y I n)=idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y) := by
  have he (n : ℤ) : dyadicIdealTerm η F Y I n=
      (dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*(idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    unfold dyadicIdealTerm
    ring
  simp_rw [he]
  have hp : 0<(I.val.absNorm:ℝ)/Y := div_pos (HeckeDyadic.norm_pos I) hY
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition _ hp]
  simp

theorem normalized_annular_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false F Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have habs := dyadic_ideal_absolute η F hF Y hY
  have hs := habs.of_norm
  have he (n : ℤ) : (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,dyadicIdealTerm η F Y I n := by
    rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
      polynomial_plain _ _ _ hY]
    congr 1
    apply tsum_congr
    intro I
    simp only [dyadicIdealTerm,dyadicWeight]
    ring
  simp_rw [he]
  refine ⟨hs.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η F Y hY]
  congr 1
  rw [hs.tsum_comm]
  exact tsum_congr (fun I=>(dyadic_ideal_partition η F Y hY I).symm)

theorem actual_reflected_annular_series (η : Character) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
        (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*Y) 0 0 := by
  exact normalized_annular_series η _ (reflected_decayTwo W) Y hY

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI

end Source929

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedTruncation.lean; sha256: a58e26a4689f63838bb7276945fc29c5cd3f1e28e743ee197069230aad629fd1 -/
section Source930
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) (A : Set ℤ) :
    Summable (fun n : ℤ=>if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=>if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring

def retainedAnnuli (R Y : ℝ) (hY : 0<Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0<Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le

theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_ofPred_eq,ite_eq_left ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI

end Source930

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalPrimitive.lean; sha256: 686c4713b5ea8bd81f76c30a43f1e362934f342e55d0d4a4ee262737b14c4bf2 -/
section Source931
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentNaturalPrimitive
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def redundantSet (M C : Ideal O) : Finset (Ideal O) := primeSupport M\primeSupport C

def redundantIdeal (M C : Ideal O) : Ideal O := ∏P∈redundantSet M C,P

lemma redundantSet_prime (M C : Ideal O) : ∀P∈redundantSet M C,Prime P :=
  fun _ h=>support_prime (Finset.mem_sdiff.mp h).1

lemma redundantSet_subset (M C : Ideal O) : redundantSet M C⊆primeSupport M :=
  Finset.sdiff_subset

lemma prime_mem_support_iff (M P : Ideal O) (hM : M≠0) (hP : Prime P) :
    P∈primeSupport M ↔ P∣M := by
  simp only [primeSupport,Multiset.mem_toFinset,Ideal.mem_normalizedFactors_iff hM]
  exact ⟨fun h=>Ideal.dvd_iff_le.mpr h.2,fun h=>⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp h⟩⟩

lemma mem_redundantSet (M C P : Ideal O) (hC : C≠0) :
    P∈redundantSet M C ↔ P∈primeSupport M ∧ ¬P∣C := by
  constructor
  · intro h
    obtain ⟨hp,hc⟩ := Finset.mem_sdiff.mp h
    exact ⟨hp,fun hd=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mpr hd)⟩
  · rintro ⟨hp,hc⟩
    exact Finset.mem_sdiff.mpr ⟨hp,fun h=>hc ((prime_mem_support_iff C P hC (support_prime hp)).mp h)⟩

lemma redundantIdeal_squarefree (M C : Ideal O) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal O) : redundantIdeal M C≠0 :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal O) : primeSupport (redundantIdeal M C)=redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

lemma redundantIdeal_coprime (M C : Ideal O) (hC : C≠0) : IsCoprime (redundantIdeal M C) C := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc=>(Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C*redundantIdeal M C∣M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C.absNorm*(redundantIdeal M C).absNorm≤M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal O) (hM : M≠0) :
    IsCoprime I M ↔ ∀P∈primeSupport M,IsCoprime I P := by
  have hprod (s : Multiset (Ideal O)) : IsCoprime I s.prod ↔ ∀P∈s,IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal O))
    | cons a s ih => simp only [Multiset.prod_cons,IsCoprime.mul_right_iff,Multiset.mem_cons,
        forall_eq_or_imp,ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport,Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀P∈redundantSet M C,IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM,?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC,hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P∈primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP,hPC⟩)

theorem idealCoeff_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (I : Ideal O) :
    idealCoeff χ I=idealCoeff (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)) I := by
  rw [hmask I,idealCoeff_excludePrimes]
  have hm := coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC : IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz : idealCoeff ψ I=0 := by simpa only [hC,ite_false] using idealCoeff_source_mask ψ I
    simp only [hz,ite_self]

theorem polynomial_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (inverse : Bool) (W : ℝ→ℂ) (D σ t : ℝ) :
    HeckeDyadic.polynomial χ inverse W D σ t=
      HeckeDyadic.polynomial (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)) inverse W D σ t := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [idealCoeff_natural_deletion χ ψ hmod hmask I.val]

theorem exists_natural_primitive (χ : Character) :
    ∃ψ : Character,χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (χ.residue≠1 → ψ.residue≠1) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I : Ideal O,idealCoeff χ I=idealCoeff
        (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
          (redundantSet_prime χ.modulus ψ.modulus)) I := by
  obtain ⟨ψ,hmod,hprim,_,hmask⟩ := exists_primitive_character χ
  refine ⟨ψ,hmod,hprim,?_,redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    idealCoeff_natural_deletion χ ψ hmod hmask⟩
  intro hχ hψ
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr hψ)

end SevenEighths.CenteredMomentNaturalPrimitive
end

end OAI

end Source931

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalReflection.lean; sha256: 88c7ffebcec9fec0072da228342b8867b56634b07b9a4fe45f956b8231336305 -/
section Source932
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

lemma polynomial_coeff_congr (χ ψ : Character)
    (h : ∀I,idealCoeff χ I=idealCoeff ψ I) (W : ℝ→ℂ) (X : ℝ) :
    HeckeDyadic.polynomial χ false W X 0 0=HeckeDyadic.polynomial ψ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [h]

lemma inverse_deletion_coeff (χ ψ : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (h : ∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I)
    (I : Ideal O) : idealCoeff χ.inverse I=idealCoeff (ψ.inverse.excludePrimes S hS) I := by
  rw [idealCoeff_inverse_conj,h,idealCoeff_excludePrimes,idealCoeff_excludePrimes,
    idealCoeff_inverse_conj]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn : ψ.residue≠1) :
    ∃G : ℂ,‖G‖=1 ∧ ∀(S : Finset (Ideal O))(hS : ∀P∈S,Prime P)
      (W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      HeckeDyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H : SmoothIdeal S,
          reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  rcases ψ with ⟨M,hM,χ,hu,p,hp0,hpm⟩
  obtain ⟨c,hc⟩ := Submodule.IsPrincipal.principal M
  change M=Ideal.span {c} at hc
  subst M
  have hc0 : c≠0 := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hM
  let : NeZero c := ⟨hc0⟩
  refine ⟨TraceCharacter.normalizedGauss c χ,TraceCharacter.normalizedGauss_norm c χ hp,?_⟩
  intro S hS W X hX
  have hh := primitive_deleted_reflection c χ hu hp hn S hS W X hX
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hh
  exact hh

theorem original_natural_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      let hS := redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I) ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩ := exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩ := primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro W X hX
  have hh := hreflection _ (redundantSet_prime χ.modulus ψ.modulus) W X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_inverse_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false (paperRadialFourier W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩ := original_natural_reflection χ hn
  refine ⟨ψ,G,hprim,hne,hG,hnorm,?_⟩
  intro W X hX
  rw [(hreflect W X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.inverse _
    (inverse_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end SevenEighths.CenteredMomentNaturalReflection

end

end OAI

end Source932

/- Original source: OAI/NumberTheory/DirichletL/Moments/TwistedReflection.lean; sha256: d360d4588e06e592b5384b3c5912dfe2aaec4aacbe85180a06dd39308e1a4b55 -/
section Source933
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem actual_original_twisted_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(_ha : 0<a)(_hs : Function.support W⊆Set.Icc a b)
        (_hW : ContDiff ℝ ∞ W)(omega X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 omega=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false
                (paperRadialFourier (CompletedHeight.normTwistedSource W (omega/(2*Real.pi))))
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,hreflect⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W a b ha hs hW omega X hX
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi)) : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W (omega/(2*Real.pi)) := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW _ x
  have hh := hreflect (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi))) X hX
  rw [he] at hh
  have ht : 2*Real.pi*(omega/(2*Real.pi))=omega := by field_simp
  rw [←ht,polynomial_twisted_source χ W X (omega/(2*Real.pi)) hX]
  simpa only [ht] using hh

end SevenEighths.CenteredMomentTwistedReflection

end

end OAI

end Source933

/- Original source: OAI/NumberTheory/DirichletL/Moments/RetainedReflection.lean; sha256: b96a97b0a57902c2013eb42a63c27f3552dd89088ddc147f2c544459e86b9641 -/
section Source934
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma masked_decayTwo (F : ℝ→ℂ) (hF : DecayTwo F) (w : ℝ→ℝ)
    (hw : ∀x,0≤w x ∧ w x≤1) : DecayTwo (fun x=>(w x:ℂ)*F x) := by
  obtain ⟨D,hD,hb⟩ := hF
  refine ⟨D,hD,?_⟩
  intro x hx
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x).1]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) (hw x).2) (sq_nonneg x)).trans (hb x hx)

lemma column_retained_discarded (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false F Y 0 0=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0+
      HeckeDyadic.polynomial η false (fun x=>(discardedWeight R x:ℂ)*F x) Y 0 0 := by
  have hr := plain_summable η _ (masked_decayTwo F hF _ (retainedWeight_bounds R)) Y hY
  have hd := plain_summable η _ (masked_decayTwo F hF _ (discardedWeight_bounds R)) Y hY
  simp only [CenteredMomentReflectionDeletion.norm] at hr hd
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,
    ←mul_add,←hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro I
  have hp := retained_add_discarded R (norm I/Y) (div_pos (norm_pos I) hY)
  simp only [CenteredMomentReflectionDeletion.norm] at hp ⊢
  rw [←mul_add,←add_mul,←Complex.ofReal_add,hp,Complex.ofReal_one,one_mul]

lemma bounded_columns (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F) :
    ∃C : ℝ,0≤C ∧ ∀Y U : ℝ,0<Y → Y≤U →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*U^(3/2:ℝ) := by
  obtain ⟨D,hD,hF⟩ := hF
  obtain ⟨C,hC,hb⟩ := plain_rapid_bound 2 (by omega)
  refine ⟨C*D,by positivity,?_⟩
  intro Y U hY hYU
  apply (hb η F D Y hD hY hF).trans
  rw [normalized_power_eq Y hY 2]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le hYU (by norm_num)) (by positivity)

lemma reflected_column_summable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η ηi χ : Character) (F : ℝ→ℂ) (hF : DecayTwo F) (Q X : ℝ)
    (hQ : 0<Q) (hX : 0<X) (D : Finset (Ideal O)) (hD : D∈S.powerset) :
    Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
      HeckeDyadic.polynomial χ false F
        (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0) := by
  obtain ⟨C,hC,hb⟩ := bounded_columns χ F hF
  obtain ⟨K,hK,hKb⟩ := coefficient_column_bound 1 (by norm_num)
  let U := Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X
  have hu : 0<U := div_pos (mul_pos hQ (subset_product_norm_pos S hS)) hX
  exact (hKb S hS η ηi (fun E H=>HeckeDyadic.polynomial χ false F
    (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*U^(3/2:ℝ)) (by positivity) (by
      intro E hE H
      have hscale := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X U hQ hX (by
        dsimp [U]
        rw [div_mul_cancel₀ _ hX.ne'])
      exact hb _ U hscale.1 hscale.2)).1 D hD

theorem original_retained_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X R : ℝ)(_hX : 0<X),
        let Q := (ψ.modulus.absNorm:ℝ)
        let Y := fun (D : Finset (Ideal O))(H : SmoothIdeal S)=>Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)
        HeckeDyadic.polynomial χ false W X 0 0=
          G*((∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0)+
            ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0) := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W X R hX
  dsimp only
  rw [heq W X hX]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo W
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  rw [←hr.tsum_add hd]
  apply tsum_congr
  intro H
  have hY := (dual_scale_bounds _ D hS (Finset.mem_powerset.mp hD) H
    (ψ.modulus.absNorm:ℝ) X ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈redundantSet χ.modulus ψ.modulus,P):ℝ)/X)
    hQ hX (by rw [div_mul_cancel₀ _ hX.ne'])).1
  change coefficient ψ ψ.inverse _ D H*HeckeDyadic.polynomial χ.inverse false
    (paperRadialFourier W) _ 0 0=_
  rw [column_retained_discarded χ.inverse _ hF R _ hY,mul_add]

end SevenEighths.CenteredMomentRetainedReflection

end

end OAI

end Source934

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedProfileMeasure.lean; sha256: 5f90497567035bbdc06fa40e714c310507947e909ab73f591544443f52e54bf6 -/
section Source935
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem actual_profile_separation (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier (CompletedHeight.normTwistedSource W t)
          (s*Real.exp y)=∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨n,hn⟩ := CenteredMomentComparisonReflection.reflected_profile_height_control
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨(C+1)*D,by positivity,?_⟩
  intro t s hs0
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : ContDiffOn ℝ ∞ (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Set.Ioi 0) := by
    rw [←he]
    exact paperRadialFourier_contDiffOn _
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep _ hF (D*(1+‖t‖)^n) (by positivity)
    (fun j hj x hx=>hDb t j hj x hx.le) s hs0
  refine ⟨density,?_,hi,hm.trans ?_,fun v=>(hp v).trans ?_⟩
  · intro y
    simpa using hid (fun _ : Unit=>y)
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]

theorem row_density_energy {ι : Type*} [Fintype ι]
    (density φ : ι→ℝ→ℂ) (rho : ℝ→ℝ) (w : ℝ→ℝ)
    (hrho : ∀v,0<rho v) (hw : ∀v,0<w v)
    (hpoint : ∀i v,‖density i v‖≤rho v)
    (hint : ∀i,Integrable (fun v=>density i v*φ i v))
    (hmeasure : Integrable (fun v=>rho v*w v))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀v,(∑i,‖φ i v‖^2)≤E*(w v)^2) :
    (∑i,‖∫v : ℝ,density i v*φ i v‖^2)≤E*(∫v : ℝ,rho v*w v)^2 := by
  let B (v : ℝ) : ℂ := (rho v*w v:ℝ)
  let F (i : ι) (v : ℝ) : ℂ := density i v/B v*φ i v
  have hB0 (v : ℝ) : B v≠0 := Complex.ofReal_ne_zero.mpr (mul_pos (hrho v) (hw v)).ne'
  have hBn (v : ℝ) : ‖B v‖=rho v*w v := by
    exact Complex.norm_of_nonneg (mul_pos (hrho v) (hw v)).le
  have he (i : ι) (v : ℝ) : B v*F i v=density i v*φ i v := by
    dsimp only [F]
    field_simp [hB0 v]
  have hFn (i : ι) (v : ℝ) : ‖F i v‖≤‖φ i v‖/w v := by
    dsimp only [F]
    rw [norm_mul,norm_div,hBn]
    calc
      _≤(rho v/(rho v*w v))*‖φ i v‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hpoint i v) (mul_pos (hrho v) (hw v)).le) (norm_nonneg _)
      _=_ := by field_simp [(hrho v).ne', (hw v).ne']
  have hb (v : ℝ) : (∑i,‖F i v‖^2)≤E := by
    calc
      _≤∑i,(‖φ i v‖/w v)^2 := Finset.sum_le_sum (fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hFn i v) 2)
      _=(∑i,‖φ i v‖^2)/(w v)^2 := by simp only [div_pow,Finset.sum_div]
      _≤E := (div_le_iff₀ (sq_pos_of_pos (hw v))).mpr (henergy v)
  have hh := CompletedGauss.finite_integral_energy_bound B F E hE
    (by simpa only [hBn] using hmeasure) (fun i=>by simpa only [he] using hint i) hb
  simpa only [he,hBn] using hh

theorem row_density_energy_two {ι : Type*} [Fintype ι]
    (b₁ b₂ : ι→ℝ→ℂ) (φ : ι→ℝ→ℝ→ℂ) (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0<rho₁ v) (hr₂ : ∀v,0<rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤rho₂ v)
    (hi₁ : ∀i,Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)))
    (hi₂ : ∀i x,Integrable (fun y=>b₂ i y*φ i x y))
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (hb : ∀x y,(∑i,‖φ i x y‖^2)≤E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖∫x : ℝ,b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  have hh := row_density_energy b₁ (fun i x=>∫y : ℝ,b₂ i y*φ i x y)
    rho₁ w₁ hr₁ hw₁ hp₁ hi₁ hm₁ (E*(∫y : ℝ,rho₂ y*w₂ y)^2) (by positivity) (by
      intro x
      have ht := row_density_energy b₂ (fun i y=>φ i x y) rho₂ w₂ hr₂ hw₂
        hp₂ (fun i=>hi₂ i x) hm₂ (E*(w₁ x)^2) (by positivity) (hb x)
      exact ht.trans_eq (by ring))
  exact hh.trans_eq (by ring)

def logWindow (V : ℝ→ℂ) (x : ℝ) : ℂ := if 0<x then V (Real.log x) else 0

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : Character) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  have hp (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_self,neg_zero,
    Complex.cpow_zero,mul_one]
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,ite_eq_left (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

lemma logWindow_support (V : ℝ→ℂ) (M : ℝ)
    (hV : ∀y,V y≠0 → |y|≤M) :
    Function.support (logWindow V)⊆Set.Icc (Real.exp (-M)) (Real.exp M) := by
  intro x hx
  change logWindow V x≠0 at hx
  by_cases hxp : 0<x
  · have hv : V (Real.log x)≠0 := by simpa only [logWindow,ite_eq_left hxp] using hx
    have hh := abs_le.mp (hV _ hv)
    constructor
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.1
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.2
  · exact False.elim (hx (by simp only [logWindow,ite_eq_right hxp]))

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : Character) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  exact finite_annular_separation V F s X hX density hsep η S hs hc

theorem actual_plain_profile_measure (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀(η : Character)(X : ℝ),0<X →
          HeckeDyadic.polynomial η false (fun x=>logWindow V x*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)) X 0 0 =
          ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A J
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro t s hs0
  obtain ⟨density,hsep,hi,hm,hp⟩ := hb t s hs0
  exact ⟨density,(fun η X hX=>plain_annular_separation V _ M s X hX hV density hsep η),hi,hm,hp⟩

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI

end Source935

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedPairEnergy.lean; sha256: 6441ba108ab49e9e276d70eae5ee5a9f310ca5a37b0b28b88e236c497ba0148b -/
section Source936
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

theorem paired_profile_energy {ι : Type*} [Fintype ι]
    (χ ψ : ι→Character) (P : ι→ℂ) (V₁ V₂ : ℝ→ℂ) (M₁ M₂ : ℝ)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (F₁ F₂ : ι→ℝ→ℂ) (s₁ s₂ X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i) (hX₂ : ∀i,0<X₂ i)
    (b₁ b₂ : ι→𝓢(ℝ,ℂ))
    (hsep₁ : ∀i y,V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*b₁ i v)
    (hsep₂ : ∀i y,V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*b₂ i v)
    (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0<rho₁ v) (hr₂ : ∀v,0<rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤rho₂ v)
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
      HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
        E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖HeckeDyadic.polynomial (χ i) false (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) (X₁ i) 0 0 *
      HeckeDyadic.polynomial (ψ i) false (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) (X₂ i) 0 0 * P i‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  let T₁ (i : ι) (x : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)
  let T₂ (i : ι) (y : ℝ) := HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)
  let φ (i : ι) (x y : ℝ) := T₁ i x*T₂ i y*P i
  have hi₂ (i : ι) (x : ℝ) : Integrable (fun y=>b₂ i y*φ i x y) := by
    have hi := (plain_density_integrable V₂ M₂ (X₂ i) (hX₂ i) hV₂ (ψ i) (b₂ i)).const_mul (T₁ i x*P i)
    apply hi.congr
    filter_upwards [] with y
    dsimp [φ,T₂]
    ring
  have he₂ (i : ι) (x : ℝ) : (∫y : ℝ,b₂ i y*φ i x y)=
      T₁ i x*(∫y : ℝ,b₂ i y*T₂ i y)*P i := by
    rw [←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [φ]
    ring
  have hi₁ (i : ι) : Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)) := by
    simp_rw [he₂]
    have hi := (plain_density_integrable V₁ M₁ (X₁ i) (hX₁ i) hV₁ (χ i) (b₁ i)).mul_const
      ((∫y : ℝ,b₂ i y*T₂ i y)*P i)
    apply hi.congr
    filter_upwards [] with x
    dsimp [T₁]
    ring
  have hh := row_density_energy_two (fun i=>(b₁ i:ℝ→ℂ)) (fun i=>(b₂ i:ℝ→ℂ)) φ
    rho₁ rho₂ w₁ w₂ hr₁ hr₂ hw₁ hw₂ hp₁ hp₂ hi₁ hi₂ hm₁ hm₂ E hE henergy
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [plain_annular_separation V₁ (F₁ i) M₁ (s₁ i) (X₁ i) (hX₁ i) hV₁ (b₁ i) (hsep₁ i) (χ i),
      plain_annular_separation V₂ (F₂ i) M₂ (s₂ i) (X₂ i) (hX₂ i) hV₂ (b₂ i) (hsep₂ i) (ψ i)]
  simp_rw [he₂]
  congr 1
  rw [←integral_mul_const,←integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [T₁,T₂]
  ring

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI

end Source936

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedUniformPair.lean; sha256: cc7bb17c701f40c0f21690789c69ab8058e81e1eedbfc747b8a55c25bcf997ce -/
section Source937
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

def heightScale (A n : ℕ) (s t : ℝ) : ℝ := (1+s)^A/(1+‖t‖)^n

def normalizedReflected (V W : ℝ→ℂ) (A n : ℕ) (s t x : ℝ) : ℂ :=
  logWindow V x*((heightScale A n s t:ℝ):ℂ)*
    paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)

def envelope (C : ℝ) (J : ℕ) (v : ℝ) : ℝ := C/(1+v^2)/(1+‖v‖)^J

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0<s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

lemma envelope_pos (C : ℝ) (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (C : ℝ) (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (C : ℝ) (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (C : ℝ) (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0<s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    convert hh using 1 ; rw [pow_add] ; ring
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  simpa only [envelope,mul_comm] using hb

theorem actual_pair_uniform (V₁ V₂ : ℝ→ℂ) (M₁ M₂ a₁ b₁ a₂ b₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂) (A J₁ J₂ : ℕ) :
    ∃n₁ n₂ : ℕ,∀W₁ W₂ : ℝ→ℂ,
      Function.support W₁⊆Set.Icc a₁ b₁ → ContDiff ℝ ∞ W₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₂ →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s₁ s₂ t₁ t₂ X₁ X₂ : ι→ℝ),
        (∀i,0<s₁ i) → (∀i,0<s₂ i) → (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      ∀E : ℝ,0≤E →
      (∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
        HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
          E*((1+‖x‖)^J₁)^2*((1+‖y‖)^J₂)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)) (X₁ i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false (normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)) (X₂ i) 0 0 * P i‖^2)≤C*E := by
  obtain ⟨n₁,h₁⟩ := actual_profile_separation V₁ M₁ a₁ b₁ hM₁ hV₁ ha₁ A (J₁+2)
  obtain ⟨n₂,h₂⟩ := actual_profile_separation V₂ M₂ a₂ b₂ hM₂ hV₂ ha₂ A (J₂+2)
  refine ⟨n₁,n₂,?_⟩
  intro W₁ W₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨C₁,hC₁,hb₁⟩ := h₁ W₁ hs₁ hW₁
  obtain ⟨C₂,hC₂,hb₂⟩ := h₂ W₂ hs₂ hW₂
  refine ⟨(C₁*Real.pi)^2*(C₂*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s₁ s₂ t₁ t₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ E hE henergy
  choose d₁ hid₁ hi₁ hm₁ hp₁ using fun i=>hb₁ (t₁ i) (s₁ i) (hs₁ i)
  choose d₂ hid₂ hi₂ hm₂ hp₂ using fun i=>hb₂ (t₂ i) (s₂ i) (hs₂ i)
  let e₁ (i : ι) : ℂ := heightScale A n₁ (s₁ i) (t₁ i)
  let e₂ (i : ι) : ℂ := heightScale A n₂ (s₂ i) (t₂ i)
  let F₁ (i : ι) (x : ℝ) := e₁ i*paperRadialFourier (CompletedHeight.normTwistedSource W₁ (t₁ i)) x
  let F₂ (i : ι) (x : ℝ) := e₂ i*paperRadialFourier (CompletedHeight.normTwistedSource W₂ (t₂ i)) x
  have hsep₁ (i : ι) (y : ℝ) : V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*(e₁ i • d₁ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₁ y*logPhase v y)*(e₁ i*d₁ i v))=
        (fun v=>e₁ i*((V₁ y*logPhase v y)*d₁ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₁ i y]
    dsimp [F₁]
    ring
  have hsep₂ (i : ι) (y : ℝ) : V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*(e₂ i • d₂ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₂ y*logPhase v y)*(e₂ i*d₂ i v))=
        (fun v=>e₂ i*((V₂ y*logPhase v y)*d₂ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₂ i y]
    dsimp [F₂]
    ring
  have hh := paired_profile_energy χ ψ P V₁ V₂ M₁ M₂ hV₁ hV₂ F₁ F₂ s₁ s₂ X₁ X₂ hX₁ hX₂
    (fun i=>e₁ i • d₁ i) (fun i=>e₂ i • d₂ i) hsep₁ hsep₂
    (envelope C₁ J₁) (envelope C₂ J₂) (fun x=>(1+‖x‖)^J₁) (fun y=>(1+‖y‖)^J₂)
    (envelope_pos C₁ hC₁ J₁) (envelope_pos C₂ hC₂ J₂) (by intro x;positivity) (by intro y;positivity)
    (fun i=>normalized_density_bound A n₁ J₁ (s₁ i) (t₁ i) C₁ (hs₁ i) (d₁ i) (hp₁ i))
    (fun i=>normalized_density_bound A n₂ J₂ (s₂ i) (t₂ i) C₂ (hs₂ i) (d₂ i) (hp₂ i))
    (envelope_integrable C₁ J₁) (envelope_integrable C₂ J₂) E hE henergy
  rw [envelope_integral,envelope_integral] at hh
  have heq : E*(C₁*Real.pi)^2*(C₂*Real.pi)^2=((C₁*Real.pi)^2*(C₂*Real.pi)^2)*E := by ring
  rw [heq] at hh
  have hf₁ (i : ι) : normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)=
      (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₁,e₁]
    ring
  have hf₂ (i : ι) : normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)=
      (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₂,e₂]
    ring
  simp_rw [hf₁,hf₂]
  exact hh

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI

end Source937

/- Original source: OAI/NumberTheory/DirichletL/Moments/OneReflectionEnergy.lean; sha256: 5207dcc99784ef63830a04aa317314a4eac96c18fce7ac741c3411e8e0b41ba9 -/
section Source938
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionEnergy
open HeckeFamily CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentComparisonReflection
open EisensteinSchwartzPoisson

lemma polynomial_inverse_plain (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false W X 0 0=
      conj (HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0) := by
  rw [polynomial_plain _ _ _ hX,polynomial_plain _ _ _ hX,map_mul,map_inv₀,
    Complex.conj_ofReal,Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro I
  rw [map_mul,idealCoeff_inverse_conj,Complex.conj_conj]

lemma polynomial_inverse_norm (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    ‖HeckeDyadic.polynomial χ.inverse false W X 0 0‖=
      ‖HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0‖ := by
  rw [polynomial_inverse_plain χ W X hX,Complex.norm_conj]

theorem actual_one_uniform (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s t X Y omega : ι→ℝ)(Wshort : ℝ→ℂ),
        (∀i,0<s i) → (∀i,0<X i) →
      ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V W A n (s i) (t i)) (X i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤C*E := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A (J+2)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨(C*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s t X Y omega Wshort hs hX E hE henergy
  choose d hid hi hm hp using fun i=>hb (t i) (s i) (hs i)
  let e (i : ι) : ℂ := heightScale A n (s i) (t i)
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (CompletedHeight.normTwistedSource W (t i)) x
  let Q (i : ι) := HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*Q i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*FourierBridge.logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*FourierBridge.logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*FourierBridge.logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (normalizedReflected V W A n (s i) (t i)) (X i) 0 0*Q i=
      ∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : normalizedReflected V W A n (s i) (t i)=
        (fun x=>logWindow V x*F i (s i*x)) := by
      funext x
      dsimp [normalizedReflected,F,e]
      ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (Q i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope C J)
    (fun v=>(1+‖v‖)^J) (envelope_pos C hC J) (by intro v;positivity)
    (fun i=>normalized_density_bound A n J (s i) (t i) C (hs i) (d i) (hp i)) hint
    (envelope_integrable C J) E hE (by
      intro v
      simpa only [φ,Q,mul_assoc] using henergy v)
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  simpa only [Q,mul_assoc,mul_comm E] using hh

end SevenEighths.CenteredMomentOneReflectionEnergy

end

end OAI

end Source938

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedNormalization.lean; sha256: 9444eec77d9397ac5da68747ceac85a157daad9a87dd5f4d1e44f91af0b9975f -/
section Source939
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentReflectedNormalization
open HeckeFamily CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson

lemma actual_log_window :
    CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow=
      (fun x : ℝ=>(annulus x:ℂ)) := by
  funext x
  unfold CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow
  split_ifs with hx
  · rw [Real.exp_log hx]
  · rw [annulus_zero_low x (by linarith)]
    rfl

lemma polynomial_const (χ : Character) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*HeckeDyadic.polynomial χ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  have he (I : HeckeDyadic.NonzeroIdeal) :
      HeckeDyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*HeckeDyadic.summand χ false W X 0 0 I := by
    unfold HeckeDyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (W : ℝ→ℂ) (B n : ℕ) (s t x : ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ : Character) (W : ℝ→ℂ) (B n : ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*HeckeDyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        HeckeDyadic.polynomial χ false
          (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual W B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]

end SevenEighths.CenteredMomentReflectedNormalization

end

end OAI

end Source939

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalReflectionApproximation.lean; sha256: d14a4f2c3d03a7dfdb9a2b12464c42ec310d45b6a4a8d5171421b704f027156d -/
section Source940
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentRetainedReflection CenteredMomentTwistedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def finiteAnnularColumn (η : Character) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

lemma finiteAnnularColumn_eq (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dite_eq_left hY]
  exact (retained_finite_series η F hF R Y hY).symm

def retainedOriginal (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
    finiteAnnularColumn χ.inverse
      (paperRadialFourier (CompletedHeight.normTwistedSource W t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

theorem actual_original_retained_approximation (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(χ : Character),χ.residue≠1 →
        ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
        ∀(X t Z : ℝ),0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            G*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
            C*(χ.modulus.absNorm:ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_deleted_discarded_negligible a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro χ hχ
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_retained_reflection χ hχ
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro X t Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  let Wt := CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t
  have heWt : (Wt : ℝ→ℂ)=CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : DecayTwo (paperRadialFourier (CompletedHeight.normTwistedSource W t)) := by
    rw [←heWt]
    exact reflected_decayTwo Wt
  have hret : retainedOriginal χ ψ W X (Z^(xi/2)) t=
      ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(retainedWeight (Z^(xi/2)) x:ℂ)*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
    unfold retainedOriginal
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro H
    rw [finiteAnnularColumn_eq _ _ hF _ _
      (dual_scale_bounds S D hS (Finset.mem_powerset.mp hD) H _ X _ hQ hX hcap').1]
  have hsource := heq Wt X (Z^(xi/2)) hX
  dsimp only at hsource
  rw [heWt] at hsource
  rw [polynomial_twisted_source χ W X t hX,hsource,←hret]
  rw [mul_add,add_sub_cancel_left,norm_mul,hG,one_mul]
  have hb := (hCb S hS ψ ψ.inverse χ.inverse t _ X Z hZ hQ hX hcap').2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hε.le

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI

end Source940

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionWeightedEnergy.lean; sha256: 3eb494a30c23a02076acdc038c9b79680fb6e54934d2d3893eeeb2b7ff7eea5c -/
section Source941
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

abbrev Index (S : Finset (Ideal O)) := (S.powerset × SmoothIdeal S) × ℤ

def baseIndex (S : Finset (Ideal O)) : Index S :=
  ((⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩,unitSmooth S),0)

def signedWeight (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

lemma signedWeight_norm (η ηi : Character) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

lemma signedWeight_base (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ) :
    signedWeight η ηi S B (baseIndex S)=(annularMass B 0:ℂ) := by
  simp only [signedWeight,baseIndex,coefficient_empty_unit,one_mul]

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)

lemma sum_iSup_le_of_selection {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (g : ∀i,α i→ℝ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,g i (a i))≤E) :
    (∑i,⨆a,g i a)≤E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((Fintype.card ι:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  choose a ha using fun i => exists_lt_of_lt_ciSup
    (show (⨆a,g i a)-δ < (⨆a,g i a) by linarith)
  have hh : (∑i,⨆a,g i a) ≤ ∑i,(g i (a i)+δ) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [ha i]
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  have he : ((Fintype.card ι:ℝ)+1)*δ=ε := by
    dsimp [δ]
    field_simp
  have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  have hb := hselection a
  simp only [Finset.card_univ] at hh
  nlinarith

lemma selection_point_bound {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (f : ∀i,α i→ℂ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) (i : ι) (a : α i) :
    ‖f i a‖^2≤E := by
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>‖f j (Function.update base i a j)‖^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  exact (by simpa using hh : ‖f i a‖^2≤∑j,‖f j (Function.update base i a j)‖^2).trans
    (hselection (Function.update base i a))

theorem weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (w f : ∀i,α i→ℂ) (M E : ℝ) (_hM : 0≤M)
    (hs : ∀i,Summable (fun a=>‖w i a‖))
    (hm : ∀i,(∑'a,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∀i,Summable (fun a=>‖w i a*f i a‖)) ∧
      (∑i,‖∑'a,w i a*f i a‖^2)≤M^2*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  let v (i : ι) : ℝ := ⨆a,‖f i a‖^2
  have hbd (i : ι) : BddAbove (Set.range (fun a=>‖f i a‖^2)) :=
    ⟨E,by rintro _ ⟨a,rfl⟩;exact selection_point_bound base f E hselection i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^2≤v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0≤v i := (sq_nonneg _).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖≤Real.sqrt (v i) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 i)).mpr (hv i a)
  have hw (i : ι) : Summable (fun a=>‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (v i))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a,w i a*f i a‖≤M*Real.sqrt (v i) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (v i)))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    (∑i,‖∑'a,w i a*f i a‖^2) ≤ ∑i,(M*Real.sqrt (v i))^2 :=
      Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hsum i) 2)
    _ = M^2*∑i,v i := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a=>‖f i a‖^2) E hselection) (sq_nonneg M)

theorem finite_weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (s : ∀i,Finset (α i)) (w f : ∀i,α i→ℂ)
    (M E : ℝ) (hM : 0≤M) (hm : ∀i,(∑a∈s i,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∑i,‖∑a∈s i,w i a*f i a‖^2)≤M^2*E := by
  let w' (i : ι) (a : α i) : ℂ := if a∈s i then w i a else 0
  have hs (i : ι) : Summable (fun a=>‖w' i a‖) := by
    apply summable_of_ne_finset_zero (s:=s i)
    intro a ha
    simp [w',ha]
  have hmass (i : ι) : (∑'a,‖w' i a‖)≤M := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    calc
      (∑a∈s i,‖w' i a‖) = ∑a∈s i,‖w i a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w',ha]
      _ ≤ M := hm i
  have hh := (weighted_selection_energy base w' f M E hM hs hmass hselection).2
  have he (i : ι) : (∑'a,w' i a*f i a)=∑a∈s i,w i a*f i a := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    apply Finset.sum_congr rfl
    intro a ha
    simp [w',ha]
  simpa only [he] using hh

lemma masked_signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    Summable (fun a=>‖mask a*signedWeight η ηi S B a‖) := by
  apply (signedWeight_summable_norm η ηi S hS B hB).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

lemma masked_signedWeight_mass_le (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    (∑'a,‖mask a*signedWeight η ηi S B a‖)≤∑'a,‖signedWeight η ηi S B a‖ := by
  apply (masked_signedWeight_summable_norm η ηi S hS B hB mask hm).tsum_le_tsum
    _ (signedWeight_summable_norm η ηi S hS B hB)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

theorem actual_masked_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀(mask f : ∀i,Index (S i)→ℂ),(∀i a,‖mask i a‖≤1) →
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i,‖∑'a,(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^2) ≤
        C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0≤R := by linarith
  let M := C*R^(ε/2)
  have hM : 0≤M := by dsimp [M];positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a,‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖)≤M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh := weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i a=>mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/2))^2=R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

theorem actual_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f : ∀i,Index (S i)→ℂ,
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,h⟩ := actual_masked_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  simpa only [norm_one,one_mul] using
    h S hS η ηi B hB R E hR hcap (fun _ _=>1) f (by intro i a;simp) hselection

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI

end Source941

/- Original source: OAI/NumberTheory/DirichletL/Moments/RetainedWeightedSource.lean; sha256: a3096f19636f78b7eafecd3288c7def52a9f3c360ccdb6cc81e1ecb001132105 -/
section Source942
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectedNormalization
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

abbrev sourcePrimes (χ ψ : Character) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : Character) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))

def retainedColumn (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ)) : ℂ :=
  if a.2∈retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2) then
    HeckeDyadic.polynomial χ.inverse false
      (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale a.2) t)
      (dyadicScale a.2*dualScale χ ψ X a.1.1 a.1.2) 0 0 * P
  else 0

lemma retainedColumn_zero (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ))
    (ha : a.2∉retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2)) :
    retainedColumn χ ψ W X R t hX B n P a=0 := by
  simp only [retainedColumn,ite_eq_right ha]

theorem finiteAnnularColumn_normalized (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H)*P =
    (((1+‖t‖)^n:ℝ):ℂ)*∑'k : ℤ,(annularMass B k:ℂ)*
      retainedColumn χ ψ W X R t hX B n P ((D,H),k) := by
  rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX D H),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H))
      (fun k hk=>by simp only [retainedColumn,ite_eq_right hk,mul_zero]),
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,ite_eq_left hk,actual_annular_normalization]
  ring

theorem retainedOriginal_eq_weighted (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖)) :
    retainedOriginal χ ψ W X R t*P =
      (((1+‖t‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes χ ψ),
        signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
          retainedColumn χ ψ W X R t hX B n P a := by
  rw [signed_series_reindex ψ ψ.inverse (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'H : SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
        R ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr
  intro H
  change (coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [mul_assoc,tsum_mul_left]
  ring

theorem retainedOriginal_fiber_summable (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖))
    (D : (sourcePrimes χ ψ).powerset) :
    Summable (fun H : SmoothIdeal (sourcePrimes χ ψ)=>
      ‖(coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
        finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
          R (dualScale χ ψ X D H))*P‖) := by
  have hh := ((hs.of_norm.prod.prod_factor D).mul_left (((1+‖t‖)^n:ℝ):ℂ)).norm
  apply hh.congr
  intro H
  congr 1
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [signedWeight,mul_assoc,tsum_mul_left]
  ring

theorem actual_retained_weighted_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(χ ψ : ι→Character)(W : ι→ℝ→ℂ)(X R t : ι→ℝ)
        (hX : ∀i,0<X i)(B : ι→ℕ)(n : ℕ)(P : ι→ℂ),
      (∀i,2≤B i) → ∀(T Rcap E : ℝ),0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀a : ∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) (a i)‖^2)≤E) →
      (∀i,Summable (fun a : Index (sourcePrimes (χ i) (ψ i))=>
        ‖signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
          retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a‖)) ∧
      (∀i,retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i =
        (((1+‖t i‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes (χ i) (ψ i)),
          signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
            retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a) ∧
      (∀i,∀D : (sourcePrimes (χ i) (ψ i)).powerset,
        Summable (fun H : SmoothIdeal (sourcePrimes (χ i) (ψ i))=>
          ‖(coefficient (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) D.val H*
            finiteAnnularColumn (χ i).inverse
              (paperRadialFourier (CompletedHeight.normTwistedSource (W i) (t i)))
              (R i) (dualScale (χ i) (ψ i) (X i) D H))*P i‖)) ∧
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2) ≤
        C*Rcap^ε*(1+T)^(2*n)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ W X R t hX B n P hB T Rcap E hT ht hRcap hcap hselection
  let f (i : ι) := retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i)
  have he := hbound (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).inverse)
    B hB Rcap E hRcap hcap f hselection
  have hid (i : ι) := retainedOriginal_eq_weighted (χ i) (ψ i) (W i) (X i) (R i) (t i)
    (hX i) (B i) n (P i) (he.1 i)
  refine ⟨he.1,hid,?_,?_⟩
  · intro i D
    exact retainedOriginal_fiber_summable (χ i) (ψ i) (W i) (X i) (R i) (t i)
      (hX i) (B i) n (P i) (he.1 i) D
  · let z (i : ι) := ∑'a : Index (sourcePrimes (χ i) (ψ i)),
        signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*f i a
    have hn (i : ι) :
        ‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖=(1+‖t i‖)^n*‖z i‖ := by
      rw [hid i,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have hp (i : ι) : (1+‖t i‖)^n≤(1+T)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht i]) n
    calc
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2)
          = ∑i,((1+‖t i‖)^n*‖z i‖)^2 := by simp_rw [hn]
      _ ≤ ∑i,((1+T)^n*‖z i‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) 2
      _ = ((1+T)^n)^2*∑i,‖z i‖^2 := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ ((1+T)^n)^2*(C*Rcap^ε*E) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
      _ = C*Rcap^ε*(1+T)^(2*n)*E := by rw [←pow_mul,Nat.mul_comm n 2];ring

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI

end Source942

/- Original source: OAI/NumberTheory/DirichletL/Moments/ScaleSupremum.lean; sha256: f33b661fde8707624ece210028118bfc09570a562225715c6901c39b61a22b73 -/
section Source943
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def scaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ inv W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ inv W S) (scaleSum χ inv (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ inv J) using 1
    · rfl
    · change coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ inv J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ inv W S l=polynomial χ inv W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 0 *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 0 * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    scaleSum (χ i) false (scaleTest W j) S x *
      scaleSum (ψ i) false (scaleTest V k) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) false (scaleTest W j) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    scaleSum_eq_polynomial (ψ i) false (scaleTest V k) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((scaleSum_continuous (χ i) false _ S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((scaleSum_continuous (ψ i) false _ T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (scaleSum_deriv (χ i) false W S (hW.differentiable (by simp)) x).mul_const
        (scaleSum (ψ i) false (scaleTest V k) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((scaleSum_deriv (ψ i) false V T (hV.differentiable (by simp)) y).const_mul
        (scaleSum (χ i) false (scaleTest W j) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 0 *
          polynomial (ψ i) false V (Real.exp y) 0 0 * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    scaleSum (χ i) false W S p.1 * scaleSum (ψ i) false V T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((scaleSum_continuous (χ i) false W S hW.continuous).comp continuous_fst).mul
      ((scaleSum_continuous (ψ i) false V T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      F i (x,y)=polynomial (χ i) false W (Real.exp x) 0 0 *
        polynomial (ψ i) false V (Real.exp y) 0 0 * P i := by
    dsimp only [F]
    rw [scaleSum_eq_polynomial (χ i) false W S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      scaleSum_eq_polynomial (ψ i) false V T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI

end Source943

/- Original source: OAI/NumberTheory/DirichletL/Moments/FrequencyScaleSupremum.lean; sha256: 53e319f9d263bd549b043e0301180a92a46045c09085a1480288bd5b88c40f49 -/
section Source944
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge FourierBridge
open CenteredMomentScaleSupremum (scaleTest scaleTest_continuous scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def frequencyScaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem frequencyScaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (frequencyScaleSum χ inv W freq S) := by
  unfold frequencyScaleSum
  fun_prop

theorem frequencyScaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (frequencyScaleSum χ inv W freq S) (frequencyScaleSum χ inv (scaleProfile W) freq S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-t)))
        ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))) using 1
    · rfl
    · change (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [frequencyScaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [frequencyScaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0<x) :
    (((x/Real.exp l : ℝ):ℂ)^(-shift 0 freq))=
      logPhase (freq/(2*Real.pi)) (-l)*logPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,logPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      logPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

theorem frequencyScaleSum_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    ‖frequencyScaleSum χ inv W freq S l‖=‖polynomial χ inv W (Real.exp l) 0 freq‖ := by
  rw [frequencyScaleSum_eq_polynomial χ inv W freq S l hc,norm_mul,logPhase_norm,one_mul]

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 (freq₁ i) *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 (freq₂ i) * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x *
      frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    frequencyScaleSum_norm (χ i) false (scaleTest W j) (freq₁ i) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    frequencyScaleSum_norm (ψ i) false (scaleTest V k) (freq₂ i) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((frequencyScaleSum_continuous (χ i) false _ (freq₁ i) S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((frequencyScaleSum_continuous (ψ i) false _ (freq₂ i) T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (frequencyScaleSum_deriv (χ i) false W (freq₁ i) S (hW.differentiable (by simp)) x).mul_const
        (frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((frequencyScaleSum_deriv (ψ i) false V (freq₂ i) T (hV.differentiable (by simp)) y).const_mul
        (frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,norm_mul,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  simp only [norm_mul]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
          polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    frequencyScaleSum (χ i) false W (freq₁ i) S p.1 * frequencyScaleSum (ψ i) false V (freq₂ i) T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((frequencyScaleSum_continuous (χ i) false W (freq₁ i) S hW.continuous).comp continuous_fst).mul
      ((frequencyScaleSum_continuous (ψ i) false V (freq₂ i) T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      ‖F i (x,y)‖^2=‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2 := by
    dsimp only [F]
    simp only [norm_mul]
    rw [frequencyScaleSum_norm (χ i) false W (freq₁ i) S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      frequencyScaleSum_norm (ψ i) false V (freq₂ i) T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ freq₁ freq₂ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI

end Source944

/- Original source: OAI/NumberTheory/DirichletL/Moments/OneReflectionScaleEnergy.lean; sha256: 48093c6739e095ac4e31ff11ca2b8b340a78e897770ae94f327798ae290b4fd3 -/
section Source945
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

lemma annular_inverse_frequency_norm (χ : Character) (X v : ℝ) (hX : 0<X) :
    ‖polynomial χ.inverse false
      (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
      X 0 (2*Real.pi*v)‖=
    ‖polynomial χ false (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v)‖ := by
  rw [actual_log_window]
  have hh := HeckeInverseAmplification.polynomial_inverse_norm χ false
    (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v) hX
  simpa only [Complex.conj_ofReal,neg_mul,neg_neg] using hh

theorem actual_one_rowwise_scales (a b : ℝ) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)
      (s t lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Icc lo hi) → (∀i,ly i∈Icc low high) →
      (∀i,0<s i) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Icc lo hi,∀y∈Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong A n (s i) (t i))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionEnergy.actual_one_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) a b hlog hwindow ha A J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hbound⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P s t lx ly omega Wshort c d lo hi low high E hd hshort hshortsmooth
    hlh hlw hlx hly hspos hE henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i).inverse false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by
      rw [←pow_mul,Nat.mul_comm J 2]
    calc
      _ = ∑i,‖polynomial (χ i) false (fun z : ℝ=>(annulus z:ℂ))
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul,annular_inverse_frequency_norm (χ i) _ v (Real.exp_pos _)]
      _ ≤ (1+2*(hi-lo))*((1+2*(high-low))*(E*(1+‖v‖)^(2*J))) := hh
      _ = _ := by rw [hp];ring
  have hh := hbound (fun i=>(χ i).inverse) χ P s t (fun i=>Real.exp (lx i))
    (fun i=>Real.exp (ly i)) omega Wshort hspos (fun i=>Real.exp_pos _)
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) (mul_nonneg hdx (mul_nonneg hdy hE)) hfixed
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI

end Source945

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectionRetainedLength.lean; sha256: 0a4d0ca94d0ae90e562034756662ed3af3b4236e2d863a51b8fbdb321018e980 -/
section Source946
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤M/4) (hreflection : reflected≤M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0≤M) (hz : 0≤z) (hk : 3/4≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤14*M/15+xi := by
  have hkz : 7/2*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤M/21 := by linarith
  constructor <;> nlinarith

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI

end Source946

/- Original source: OAI/NumberTheory/DirichletL/Moments/ReflectedChoiceEnergy.lean; sha256: c2685baf06e8d7b05c526635896345e743fa1dfda65c5a216eb7ae106dbb3ba0 -/
section Source947
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => HeckeFamily.O

theorem actual_independent_profile_choices (a b : ℝ) (ha : 0<a) (B J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (t ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong B n (s i (u i)) (t i))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionScaleEnergy.actual_one_rowwise_scales a b ha B J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ α χ P s X keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hE henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb χ P' (fun i=>s i (u i)) t lx ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hE he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end SevenEighths.CenteredMomentReflectedChoiceEnergy

end

end OAI

end Source947

/- Original source: OAI/NumberTheory/DirichletL/Moments/RetainedComparisonEnergy.lean; sha256: 7a24ae6bae9c710916e5d648f58c26091daf3b202cba534ab7a1c9853d5b2f06 -/
section Source948
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentRetainedComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedChoiceEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_retained_fixed_profile_energy (a b epsilon : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(χ ψ : ι→Character)(P : ι→ℂ)(X R t ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high E T Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (X i) (R i) (t i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := actual_independent_profile_choices a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cp,hCp,hp⟩ := hn Wlong hs hW
  refine ⟨Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ χ ψ P X R t ly omega Wshort c d lo hi low high E T Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hE hT ht hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp χ P s Y keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hE henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) Wlong (X i) (R i) (t i) (hX i) B n (P' i) (u i)‖^2)≤
        Cp*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun _=>Wlong) X R t hX (fun _=>B) n P' (fun _=>hB)
    T Rcap _ hT ht hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [P',←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentRetainedComparisonEnergy

end

end OAI

end Source948

/- Original source: OAI/NumberTheory/DirichletL/Moments/NaturalRetainedEnergy.lean; sha256: 883a4a0c0c86d80b5648f811a8d727d2b71b5bc836d4376fdfa711a55dd4d123 -/
section Source949
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentNaturalRetainedEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentRetainedComparisonEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (a b epsilon Cscale xi : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (Z^along) (Z^(xi/4)) (t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨n,hn⟩ := actual_retained_fixed_profile_energy a b epsilon ha hepsilon B J hB
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ ψ P t omega Wshort c d M along bshort E T Rcap hd hshort hshortsmooth
    hnatural hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) t (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    E T Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hE hT ht hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentNaturalRetainedEnergy

end

end OAI

end Source949

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalReflectionEnergy.lean; sha256: 4a62c123c1f47b8bafc77859dc8c1923e125c6faa7f312451d069f76ee43b190 -/
section Source950
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionEnergy
open HeckeFamily CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_sq_comparison (a b : ℂ) : ‖a‖^2≤2*‖b‖^2+2*‖a-b‖^2 := by
  have he : a=b+(a-b) := by ring
  have hh : ‖a‖≤‖b‖+‖a-b‖ := by nth_rw 1 [he];exact norm_add_le _ _
  nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a-b),sq_nonneg (‖b‖-‖a-b‖)]

theorem actual_original_energy_to_retained (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(X t : ι→ℝ)(P : ι→ℂ)(T Z Rcap : ℝ),0≤T → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,‖t i‖≤T) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2)≤
            2*(∑i,‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2)+
            C*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_original_retained_approximation a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro X t P T Z Rcap hT hZ hR hX ht hmod hsource
  let B := C*Rcap^ε*(1+T)^n*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)-
        G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)‖≤B := by
    apply (happrox i (X i) (t i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le) hC.le)
      (pow_le_pow_left₀ (by positivity) (by simpa only [Real.norm_eq_abs,add_comm] using add_le_add_left (ht i) 1) n) (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2≤
      2*‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i)
      ((G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i-
        (G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz,←pow_mul]
    rw [Nat.mul_comm n 2]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentOriginalReflectionEnergy

end

end OAI

end Source950

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalComparisonEnergy.lean; sha256: 809f12da392f4461638971c7873a5458205f6120df2db56be930184a088c7dbf -/
section Source951
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentNaturalRetainedEnergy CenteredMomentOriginalReflectionEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false Wlong (Z^along) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_natural_retained_energy a b epsilon Cscale xi ha hepsilon hscale hxi B J hB
  obtain ⟨ne,hne⟩ := actual_original_energy_to_retained a b (xi/2) saving L Cscale epsilon
    ha (by positivity) hscale hepsilon
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hr⟩ := hn Wlong hs hW
  obtain ⟨D,hD,ho⟩ := hne Wlong hs hW
  refine ⟨2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ P t omega Wshort c d M along bshort E T Rcap hχ hd hshort hshortsmooth
    hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal (fun _=>Z^along) t Q T Z Rcap hT hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) ht hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 χ ψ P t omega Wshort c d M along bshort E T Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hE hT ht hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOriginalComparisonEnergy

end

end OAI

end Source951

/- Original source: OAI/NumberTheory/DirichletL/Moments/RadialPolynomialEnergy.lean; sha256: 267d2a22f9ff59f852f4b77f3c50b3f1ae2b2e44fd302691bf92a4a59b738541 -/
section Source952
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability ConcreteTraceCRT
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    FourierBridge.logPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,FourierBridge.logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma pair_radial_summable (χ : O→Character) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b c d X Y Pbound : ℝ)
    (hb : 0≤b) (hd : 0≤d) (hX : 0<X) (hY : 0<Y)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end SevenEighths.CenteredMomentRadialPolynomialEnergy

end

end OAI

end Source952

/- Original source: OAI/NumberTheory/DirichletL/Moments/OriginalRadialComparison.lean; sha256: 73cf7ccff4079321e94cdc40cbffb8371f532936445c85c8e3cfc483b8b5eda8 -/
section Source953
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalComparisonEnergy CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

def radialEnergy (F : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma sqrt_weight (a p : ℂ) (u : ℝ) (hu : 0≤u) :
    ‖a*(p*(Real.sqrt u:ℂ))‖^2=‖a*p‖^2*u := by
  rw [←mul_assoc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hu]

lemma finite_weighted (rows : Finset O) (keep : O→Prop) (F : O→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z : ↥(rows.filter keep),‖F z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)‖^2)=
    ∑z∈rows,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  simp_rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
  rw [Finset.sum_coe_sort (rows.filter keep) (fun z:O=>‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re),Finset.sum_filter]

theorem actual_original_radial_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (_hb : 0≤b) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(χ : O→Character)(P : O→ℂ)(t omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀z,keep z → ‖t z‖≤T) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨n,ne,h⟩:=actual_original_comparison a b epsilon Cscale xi saving L ha hepsilon hscale hxi B J hB
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,D,hC,hD,h⟩:=h Wlong hs hW
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ P t omega keep Φ K Pbound Wshort c d M along bshort E T Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>χ z) weightedP (fun z=>t z) (fun z=>omega z)
    Wshort c d M along bshort E T Rcap (fun z=>hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=>hmod z (hmem z)) hE hT (fun z=>ht z (hmem z)) hRcap
    (fun z=>hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
      finite_weighted rows keep (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ] at hh
    apply hh.trans
    apply add_le_add
    · apply le_of_eq;ring
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  · intro v j k x hx
    have hschild:=pair_radial_summable χ P (fun _=>-2*Real.pi*v) omega
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (scaleTest Wshort k)
      (1/4) 1 c d (Real.exp x) (Z^bshort) Pbound (by norm_num) hd
      (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j)
      (scaleTest_support _ _ _ hshort k) hP keep Φ K hK
    simp only [weightedP,←mul_assoc]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) Φ K hΦ]
    exact (hschild.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (henergy v j k x hx)

end SevenEighths.CenteredMomentOriginalRadialComparison

end

end OAI

end Source953

/- Original source: OAI/NumberTheory/DirichletL/Moments/PlainPositiveEnergy.lean; sha256: bd057b382981779d05ae9a6164efeae620e7672e9965c9eb7bab2ef0c72c9189 -/
section Source954
namespace OAI

noncomputable section
open scoped Classical SchwartzMap BigOperators
namespace SevenEighths.CenteredMomentPlainPositiveEnergy
open HeckeFamily HeckeDyadic CenteredMomentPlainPositiveScale CenteredMomentPlainGlobalEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem actual_radial_pair_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(χ:O→Character)(r:Radial)(R X₁ X₂ freq₁ freq₂:ℝ),0≤R→0<X₁→0<X₂→
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤R)→
    radialEnergy (fun z=>polynomial (χ z) false W₁ X₁ 0 freq₁*
      polynomial (χ z) false W₂ X₂ 0 freq₂) r.keep r.profile r.scale≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*R^4*
        (3+|freq₁|)^4*(3+|freq₂|)^4:=by
  obtain ⟨S,C,hC,hg⟩:=global_positive_scale a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R X₁ X₂ freq₁ freq₂ hR hX₁ hX₂ hχ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let B:=C^2*(B₁*B₂)*R^2*(3+|freq₁|)^2*(3+|freq₂|)^2
  have hB:0≤B:=by dsimp [B];positivity
  have hp (z:O)(hz:r.keep z):
      ‖polynomial (χ z) false W₁ X₁ 0 freq₁*polynomial (χ z) false W₂ X₂ 0 freq₂‖≤B:=by
    rw [norm_mul]
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 freq₁‖≤C*B₁*R*(3+|freq₁|)^2:=
      (hg W₁ hs₁ (χ z) (hχ z hz) X₁ freq₁ hX₁).trans (by gcongr;exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 freq₂‖≤C*B₂*R*(3+|freq₂|)^2:=
      (hg W₂ hs₂ (χ z) (hχ z hz) X₂ freq₂ hX₂).trans (by gcongr;exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hh:=radial_bound_on_keep _ r B hB hp
  exact hh.trans_eq (by dsimp [B];ring)

end SevenEighths.CenteredMomentPlainPositiveEnergy

end

end OAI

end Source954

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformReflectionProfile.lean; sha256: c4874f972c06a73241c6a15d50fa9a42a74406e729073ba210ef0b91b4011c88 -/
section Source955
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentUniformReflectionProfile
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentOneReflectionEnergy

theorem source_separation (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀G : 𝓢(ℝ,ℂ),∀D : ℝ,0<D →
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤D → ∀s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier G (s*Real.exp y)=
          ∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*D ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*D) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨H,K,hK,hEuler⟩ := paperRadialFourier_euler_source_weighted_bound
    A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep (paperRadialFourier G)
    (paperRadialFourier_contDiffOn G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst : C*(K*D)≤((C+1)*K)*D := by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=>by simpa using hid (fun _ : Unit=>y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem actual_one_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := source_separation V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=>hb (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (G i) x
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))=
        (fun x=>logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert hh using 1
  ring

lemma inverse_annular_frequency (χ : Character) (V : ℝ→ℂ)
    (hreal : ∀y,conj (V y)=V y) (X v : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false (logWindow V) X 0 (2*Real.pi*v)=
      conj (HeckeDyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr (x : ℝ) : conj (logWindow V x)=logWindow V x := by
    unfold logWindow
    split_ifs <;> simp [hreal]
  have ht : (fun x=>conj (CompletedHeight.normTwistedSource (logWindow V) v x))=
      CompletedHeight.normTwistedSource (logWindow V) (-v) := by
    funext x
    simp only [CompletedHeight.normTwistedSource,map_mul,hr]
    exact congrArg (fun z=>z*logWindow V x) (SecondPassIntegration.logPhase_conjugate v _)
  rw [CenteredMomentTwistedReflection.polynomial_twisted_source χ.inverse _ X v hX,
    polynomial_inverse_plain χ _ X hX,ht,
    ←CenteredMomentTwistedReflection.polynomial_twisted_source χ _ X (-v) hX]
  congr 2
  ring

theorem actual_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  apply hbound G (fun i=>(χ i).inverse) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖HeckeDyadic.polynomial (χ i).inverse false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [inverse_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v

lemma paperRadialFourier_real_smul (c : ℝ) (G : 𝓢(ℝ,ℂ)) (x : ℝ) :
    paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) x=(c:ℂ)*paperRadialFourier G x := by
  rw [paperRadialFourier_eq_ray,paperRadialFourier_eq_ray]
  simp only [map_smul,smul_apply,Complex.real_smul]

lemma polynomial_const_mul (χ : Character) (W : ℝ→ℂ) (X σ omega : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X σ omega=
      c*HeckeDyadic.polynomial χ false W X σ omega := by
  unfold HeckeDyadic.polynomial
  have he : (fun I : HeckeDyadic.NonzeroIdeal=>
      HeckeDyadic.summand χ false (fun x=>c*W x) X σ omega I)=
      (fun I=>c*HeckeDyadic.summand χ false W X σ omega I) := by
    funext I
    unfold HeckeDyadic.summand
    ring
  rw [he,tsum_mul_left]
  ring

lemma reflected_polynomial_real_smul (χ : Character) (V : ℝ→ℂ)
    (G : 𝓢(ℝ,ℂ)) (s X c : ℝ) (A : ℕ) :
    HeckeDyadic.polynomial χ false
      (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) (s*x)) X 0 0=
      (c:ℂ)*HeckeDyadic.polynomial χ false
        (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x)) X 0 0 := by
  simp_rw [paperRadialFourier_real_smul]
  have he : (fun x=>logWindow V x*((1+s)^A:ℂ)*((c:ℂ)*paperRadialFourier G (s*x)))=
      (fun x=>(c:ℂ)*(logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x))) := by
    funext x
    ring
  rw [he,polynomial_const_mul]

theorem detector_source_control (H : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃D : ℝ,0<D ∧ ∀reverse : Bool,∀k : ℕ,k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (((1+‖t‖)^n)⁻¹ • CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t)≤D := by
  obtain ⟨n,D,hD,hb⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,D,hD,?_⟩
  intro reverse k hk σ hσ t
  rw [map_smul_eq_mul,Real.norm_of_nonneg (by positivity : 0≤((1+‖t‖)^n)⁻¹)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(1+‖t‖)^n)).mpr
    (by simpa only [mul_comm] using hb reverse k hk σ hσ t)

theorem detector_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(reverse : ι→Bool)(k : ι→ℕ)(σ t : ι→ℝ),
      (∀i,k i≤2) → (∀i,σ i∈Set.Icc (0:ℝ) 1) →
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*
        (((1+‖t i‖)^n:ℝ):ℂ)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier
          (CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)) (s i*x))
        (X i) 0 0*P i‖^2)≤C*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_inverse_uniform V M hM hV hreal A J
  obtain ⟨n,D,hD,hcontrol⟩ := detector_source_control H
  refine ⟨n,C*D^2,by positivity,?_⟩
  intro ι _ reverse k σ t hk hσ χ P s X hs hX E hE henergy
  let G (i : ι) := CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)
  let w (i : ι) : ℝ := (1+‖t i‖)^n
  have hw (i : ι) : 0<w i := by dsimp [w];positivity
  have hh := hb (fun i=>(w i)⁻¹ • G i) χ (fun i=>(w i:ℂ)*P i) s X hs hX D E hD hE
    (fun i=>hcontrol (reverse i) (k i) (hk i) (σ i) (hσ i) (t i))
    (by intro v;simpa only [w,mul_assoc] using henergy v)
  have he (i : ι) : HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier ((w i)⁻¹ • G i : 𝓢(ℝ,ℂ)) (s i*x))
      (X i) 0 0*((w i:ℂ)*P i)=
      HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x)) (X i) 0 0*P i := by
    rw [reflected_polynomial_real_smul,Complex.ofReal_inv]
    have hne : (w i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw i).ne'
    rw [mul_mul_mul_comm,inv_mul_cancel₀ hne,one_mul]
  simp_rw [he] at hh
  simpa only [G] using hh

end SevenEighths.CenteredMomentUniformReflectionProfile

end

end OAI

end Source955

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformReflectionScale.lean; sha256: 3be91756b785cf4c64c8dbb2c18aece50aa4205eb25b1c9ea72630048ee61872 -/
section Source956
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentUniformReflectionScale
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy CenteredMomentUniformReflectionProfile
open CenteredMomentReflectedNormalization

theorem actual_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0<s i) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=actual_inverse_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound G χ (fun i=>polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=>Real.exp (lx i)) hspos (fun i=>Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert hh using 1

end SevenEighths.CenteredMomentUniformReflectionScale

end

end OAI

end Source956

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformReflectionChoices.lean; sha256: 088528a73b61d35ae733adc19437cd3c66cae681c987baa515424531cc2ee51d -/
section Source957
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionChoices
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionScale

theorem actual_independent_choices (B J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*paperRadialFourier (G i) (s i (u i)*x))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_rowwise_scales B J
  refine ⟨H,C,hC,?_⟩
  intro ι _ α G χ P s X keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hD hE hGD henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb G χ P' (fun i=>s i (u i)) lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hD hE hGD he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

end SevenEighths.CenteredMomentUniformReflectionChoices

end

end OAI

end Source957

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformReflectionApproximation.lean; sha256: 9b6dac0da1e786885c4c0339f9781fc5ebf6f52e1dc8e902f87551881a412d5b -/
section Source958
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentRetainedReflection CenteredMomentOriginalReflectionApproximation
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem discarded_bound (A B : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y R : ℝ),
      0<Y → 0<R →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨H,D,hD,hDb⟩ := paperRadialFourier_euler_source_weighted_bound (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨H,K*D,mul_pos hK hD,?_⟩
  intro G χ Y R hY hR
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier G x‖≤
      D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := by
    intro x hx
    have hh := hDb G 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)
    R (by positivity) hR hf
  exact (hKb χ _ ((D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)/R^A)
    Y (by positivity) hY hm).trans_eq (by ring)

theorem discarded_negligible (xi saving L Cscale : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨H,C,hC,hbound⟩ := discarded_bound A 2 (by omega)
  refine ⟨H,C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro G χ Y Z hZ hY hYZ
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A :=
      hbound G χ Y _ hY hR
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem deleted_discarded_negligible (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))
      (S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)(η ηi χ : Character)(Q X Z : ℝ),
      1≤Z → 0<Q → 0<X → Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
      let F := fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x
      (∀D∈S.powerset,Summable (fun I : SmoothIdeal S=>coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0)) ∧
      ‖∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
          (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := discarded_negligible xi saving L Cscale hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound epsilon hepsilon
  refine ⟨H,D*C,mul_pos hD hC,?_⟩
  intro G S hS η ηi χ Q X Z hZ hQ hX hcap
  dsimp only
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hh := hDb S hS η ηi
    (fun E I=>HeckeDyadic.polynomial χ false
      (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm I.val)) 0 0)
    (C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving)) (by positivity) (by
      intro E hE I
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) I Q X (Cscale*Z^L) hQ hX hcap
      exact hCb G χ _ Z hZ hy.1 hy.2)
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

def retainedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    finiteAnnularColumn χ.inverse (paperRadialFourier G) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))

def discardedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    HeckeDyadic.polynomial χ.inverse false (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0

lemma retainedSchwartz_eq (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    retainedSchwartz χ ψ G X R=
      let S := redundantSet χ.modulus ψ.modulus
      ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0 := by
  unfold retainedSchwartz
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro I
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ (reflected_decayTwo G) _ _ (by positivity)]

lemma restoration_summable (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    let S := redundantSet χ.modulus ψ.modulus
    ∀D∈S.powerset,
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) R
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))) ∧
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0) := by
  dsimp only
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo G
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  refine ⟨hr.congr ?_,hd⟩
  intro I
  have hN := subset_product_norm_pos D (fun P hP=>hS P ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ hF _ _ (by positivity)]

theorem original_split (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X R : ℝ),0<X →
        HeckeDyadic.polynomial χ false G X 0 0=
          g*(retainedSchwartz χ ψ G X R+discardedSchwartz χ ψ G X R) := by
  obtain ⟨ψ,g,hp,hnp,hg,hcap,h⟩ := original_retained_reflection χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X R hX
  rw [retainedSchwartz_eq χ ψ G X R hX]
  exact h G X R hX

theorem actual_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := deleted_discarded_negligible xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hsplit⟩ := original_split χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  rw [hsplit G X (Z^(xi/2)) hX,mul_add,add_sub_cancel_left,norm_mul,hg,one_mul]
  have hb := (hCb G S hS ψ ψ.inverse χ.inverse _ X Z hZ hQ hX hcap').2
  apply hb.trans
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hepsilon.le

lemma retainedSchwartz_uniformTwisted (χ ψ : Character) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t X R : ℝ) :
    retainedSchwartz χ ψ (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X R=
      retainedOriginal χ ψ W X R t := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold retainedSchwartz retainedOriginal
  rw [he]

theorem actual_twisted_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(ha : 0<a)(hs : Function.support W⊆Set.Icc a b)
        (hW : ContDiff ℝ ∞ W)(t X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
          g*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)*
            (χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro W a b ha hs hW t X Z hX hZ hmod
  have hh := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X Z hX hZ hmod
  rw [retainedSchwartz_uniformTwisted] at hh
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have ht := CenteredMomentTwistedReflection.polynomial_twisted_source χ W X t hX
  rw [←he] at ht
  rw [←ht] at hh
  exact hh

theorem detector_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀reverse : Bool,∀k : ℕ,k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t X Z : ℝ,
        0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        let G := CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*(χ.modulus.absNorm:ℝ)^epsilon*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  obtain ⟨n,D,hD,hcontrol⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,C*D,mul_pos hC hD,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro reverse k hk σ hσ t X Z hX hZ hmod
  dsimp only
  apply (hbound _ X Z hX hZ hmod).trans
  have he := hcontrol reverse k hk σ hσ t
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (by positivity :
      0≤(χ.modulus.absNorm:ℝ)^epsilon)) (by positivity : 0≤Z^(-saving))
  exact hh.trans_eq (by ring)

end SevenEighths.CenteredMomentUniformReflectionApproximation

end

end OAI

end Source958

/- Original source: OAI/NumberTheory/DirichletL/Moments/UniformRetainedEnergy.lean; sha256: b90a4944fc69258f01dbf57424f5db1bb6e2aa9bfca3989ce963c9e5291a15f9 -/
section Source959
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformRetainedEnergy
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionChoices CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentReflectedUniformPair
open CenteredMomentReflectedNormalization

lemma twisted_zero (W:ℝ→ℂ) : CompletedHeight.normTwistedSource W 0=W := by
  funext x
  simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]

lemma normalized_zero (G:𝓢(ℝ,ℂ)) (B:ℕ) (s:ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow G B 0 s 0=
      (fun x=>(annulus x:ℂ)*((1+s)^B:ℂ)*paperRadialFourier G (s*x)) := by
  funext x
  simp only [normalizedReflected,heightScale,pow_zero,div_one,twisted_zero,actual_log_window]
  push_cast
  rfl

lemma retained_zero (χ ψ:Character) (G:𝓢(ℝ,ℂ)) (X R:ℝ) :
    retainedOriginal χ ψ G X R 0=retainedSchwartz χ ψ G X R := by
  unfold retainedOriginal retainedSchwartz
  rw [twisted_zero]

theorem actual_retained_uniform_energy (epsilon : ℝ)
    (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(X R ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high D E Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := actual_independent_choices B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R ly omega Wshort c d lo hi low high D E Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp G χ P s Y keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hD hE hGD henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (P' i) (u i)‖^2)≤
        Cp*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,normalized_zero,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun i=>(G i:ℝ→ℂ)) X R (fun _=>0) hX (fun _=>B) 0 P' (fun _=>hB)
    0 Rcap _ le_rfl (fun _=>by simp) hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [retained_zero,P',Nat.mul_zero,pow_zero,mul_one,←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentUniformRetainedEnergy

end

end OAI

end Source959
