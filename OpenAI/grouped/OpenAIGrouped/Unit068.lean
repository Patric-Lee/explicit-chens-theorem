import OpenAIGrouped.Unit067
import OpenAIGrouped.Unit065
import OpenAIGrouped.Unit063
import OpenAIGrouped.Unit061
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit066
import OpenAIGrouped.Unit057
import OpenAIGrouped.Unit058

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstDyadicPriorityBudget.lean; sha256: 0d2d24dff0699095b6cf087919caadf1219187adb240187c35ed0d28814cb349 -/
section Source2720
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_priority_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤Lcap)(hb:0≤b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)(_hF0:0≤Fmax)(_hFcap:Fmax≤Lcap)
      (_heta:0≤eta)(_heta1:eta≤1)(_htau:0≤tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_budget om Φ a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  apply henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights w₁
      ((physicalScales (Z^r) k.1 k.2.1) 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hleft k hk z)
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights w₂
      ((physicalScales (Z^r) k.1 k.2.1) 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hright k hk z)

end SevenEighths.InverseMoment

end

end OAI

end Source2720

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstDyadicTail.lean; sha256: 5ad9cbe01a06abb11a15d247025496243daa3727c432178c2802c56d1ec6d259 -/
section Source2721
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_first_dyadic_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
    (hMm:0≤Mmax) (hFm:0≤Fmax) (heta:0≤eta) (htau:0<tau) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (weights:σ→ι→ℂ)
      (extra₁ extra₂:CubeCoordinates ι→Finset ι)
      (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (Z M r ell V Γ G₁ G₂:ℝ),
      1<Z → 2≤Z^eta → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤r → r+3*ell+V≤Fmax →
      0≤Γ → 0≤G₁ → 0≤G₂ →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta)) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
          (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*65536*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hbin hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
    hadm hb₁ hb₂ hI0 hIF ha hslots hw he₁ he₂ ht₁ ht₂ hs₁ hs₂
  have hz:0<Z:=zero_lt_one.trans hZ
  let B:=Z^(ell+eta)
  let L:=Z^(r+eta)
  let E:=65536*(Cm*(B^2*L)*G₁)*(Cm*(B^2*L)*G₂)*
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving')
  have hB:1≤B:=Real.one_le_rpow hZ.le (by linarith)
  have hL:0<L:=Real.rpow_pos_of_pos hz _
  have hE:0≤E:=by dsimp [E,B,L];positivity
  have hextra (extra:CubeCoordinates ι→Finset ι) (he:∀b∈bs,extra b⊆b.support)
      (b:CubeCoordinates ι) (hb:b∈bs):primeProductNorm p (extra b)≤B^2:=
    (primeProductNorm_mono p hp (he b hb)).trans
      (cube_whole_support_dyad p hp b B (zero_le_one.trans hB) (hb₁ b hb) (hb₂ b hb))
  have hlocal (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels)
      (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
        (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
        (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
        (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:1≤x):x≤Z^(firstDyadicExponent Z x+eta):=
      (first_dyadic_bounds Z eta x hZ hbin hx).2.2
    have hlower (x:ℝ) (hx:1≤x):Z^(firstDyadicExponent Z x-eta)≤x:=by
      exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : firstDyadicExponent Z x-eta≤firstDyadicExponent Z x)).trans
        (first_dyadic_bounds Z eta x hZ hbin hx).2.1
    have hjpos:0<‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (firstDyadicExponent Z (primeProductNorm p C))
      (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>firstDyadicExponent Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_ge_one p hp D)) (hlower _ (primeProductNorm_ge_one p hp C))
      (hlower _ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)))
    simpa only [firstLocalPhysicalTail,firstDyadicPhysicalCutoff,firstDyadicRadius,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)
    hB hL (Real.one_le_rpow hZ.le (by linarith)) hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2) hlocal
  apply he.trans
  have hexp:B^9*L^4*Z^(V+eta)*Z^(-saving')≤Z^(-saving):=by
    dsimp [B,L]
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [saving']
    norm_num
    linarith
  have hm:=mul_le_mul_of_nonneg_left hexp
    (show 0≤Ca*65536*Cm^2*Ct*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) from by positivity)
  convert hm using 1
  · dsimp only [E]
    norm_num
    ring

end SevenEighths.InverseMoment

end

end OAI

end Source2721

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstZeroSource.lean; sha256: 0e2972346427e4da9faa96df8133fcd6b642b1857902d7a88546c33045a0c6f8 -/
section Source2722
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
include hinj hc in
theorem first_variable_zero_common_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ L K : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hL : 0<L)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hH₁ : ∀U,‖H₁ U‖≤G₁) (hH₂ : ∀U,‖H₂ U‖≤G₂) (hsupp : ∀U,H₁ U≠0→primeProductNorm p U≤L) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(L))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    H₁ H₂ W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    have hz : H₁ (b.rightDivisor∪C)=0 := by
      by_contra hh
      exact hbnd ((primeProductNorm_mono p hp Finset.subset_union_right).trans (hsupp _ hh))
    have hz' : z C I=0 := by
      dsimp only [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
      split_ifs <;> simp [hz]
    rw [hz',mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (L)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I) H₁ H₂ W K
      rw [ite_eq_left hb] at hz
      have hz' : ‖z C I‖≤G₁*G₂ * |K| * ‖paperRadialFourier W 0‖ := by
        apply hz.trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hH₁ _) (hH₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz' (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (L)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end
theorem full_variable_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀b∈bs,∀U,‖H₁ b U‖≤G₁) → (∀b∈bs,∀U,‖H₂ b U‖≤G₂) → (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (H₁ b) (H₂ b) W K‖≤
      C*B^(1+ε)*(L)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W Γ G₁ G₂ L K B F hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hH₁ hH₂ hsupp
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (H₁ b) (H₂ b) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(L))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact first_variable_zero_common_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (H₁ b) (H₂ b) W Γ G₁ G₂ L K hΓ hG₁ hG₂ hL (ha b hb) (hH₁ b hb) (hH₂ b hb) (hsupp b hb)
    _ = ((bs.filter good).card:ℝ)*((128*(L))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(L))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2722

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstMarkedZeroSource.lean; sha256: 44254b46ca334005b29157ed15476d5be02f5797918b254683a3a660d5a0c3b3 -/
section Source2723
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_marked_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (coeff:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ)
      (extra₁ extra₂ : CubeCoordinates ι→Finset ι)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖coeff b D I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,coeff b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W K‖≤
      C*B^(1+ε)*L*F*Γ*((B^2*L)^ε)^2*(G₁*G₂ * |K| * ‖paperRadialFourier W 0‖) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_variable_first_zero_bound ε hε
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cz*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    test₁ test₂ extra₁ extra₂ slots lists a W Γ G₁ G₂ L K B F
    hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff hslots ha
    he₁ he₂ htest₁ htest₂ hs₁ hs₂
  have hB0 : 0≤B := le_trans zero_le_one hB
  have hextra (extra : CubeCoordinates ι→Finset ι) (he : ∀b∈bs,extra b⊆b.support)
      (b : CubeCoordinates ι) (hb : b∈bs) : primeProductNorm p (extra b)≤B^2 :=
    (primeProductNorm_mono p hp (he b hb)).trans (cube_whole_support_dyad p hp b B hB0 (hb₁ b hb) (hb₂ b hb))
  have ht₁ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₁ b∪U)*test₁ b U‖≤Cm*(B^2*L)^ε*G₁ :=
    hmark p hp hcop slots lists a hslots ha (extra₁ b) (test₁ b) (B^2) G₁ L
      (sq_nonneg _) hG₁ hL.le (hextra extra₁ he₁ b hb) (htest₁ b hb) (hs₁ b hb)
  have ht₂ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₂ b∪U)*test₂ b U‖≤Cm*(B^2*L)^ε*G₂ :=
    hmark p hp hcop slots lists a hslots ha (extra₂ b) (test₂ b) (B^2) G₂ L
      (sq_nonneg _) hG₂ hL.le (hextra extra₂ he₂ b hb) (htest₂ b hb) (hs₂ b hb)
  have hh := hzero p hp hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W
    Γ (Cm*(B^2*L)^ε*G₁) (Cm*(B^2*L)^ε*G₂) L K B F
    hΓ (by positivity) (by positivity) hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff ht₁ ht₂
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2)
  exact hh.trans_eq (by ring)

end SevenEighths.InverseMoment

end

end OAI

end Source2723

/- Original source: OAI/NumberTheory/DirichletL/Descent/ReopenedZeroEnergy.lean; sha256: 9779e9afd5c6385f34a1d17809838ebada30e94fa7c887ca67ea9722a94c4020 -/
section Source2724
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_reopened_marked_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (W:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Γ G L K B F:ℝ),
      0≤Γ → 0≤G → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ u‖≤1) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖W (primeProductNorm p U)‖≤G) →
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤L) →
      ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ K)‖≤
      C*B^(1+ε)*L*F*Γ^2*((B^2*L)^ε)^2*(G^2*|K| *‖paperRadialFourier Φ 0‖) := by
  obtain ⟨C,hC,he⟩ := full_marked_first_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G L K B F
    hΓ hG hL hB hF hΨ hQ hn hFlabels hβ hslots ha hW hs
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hcoeff := reopenedPairCoefficient_bound Q labels β Γ hΓ hβ
  have hh := he p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (fun _ U=>W (primeProductNorm p U))
    (fun _ U=>W (primeProductNorm p U))
    (fun b=>b.rightExponent.support) (fun b=>b.leftExponent.support)
    slots lists a Φ (Γ^2) G G L K B F (sq_nonneg _) hG hG hL hB hF hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun b hb'=> (hb b hb').1) (fun b hb'=> (hb b hb').2)
    hn hFlabels (fun b hb C hC I hI=>hcoeff b hb C I hI) hslots ha
    (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hs) (fun _ _=>hs)
  simpa only [reopenedPhysicalSourceSum,Finset.union_comm,pow_two] using hh

end SevenEighths.InverseMoment

end

end OAI

end Source2724

/- Original source: OAI/NumberTheory/DirichletL/Descent/OriginalZeroPhysical.lean; sha256: 949656ab2d5edb66aec022425b8ccd6a95459ef0aad484800bcdf8677b7646b5 -/
section Source2725
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_first_zero_physical (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
      (Z M r ell V eta Γ G:ℝ),1<Z→0≤ell+eta→0≤V+eta→0≤Γ→0≤G→
      (∀u,‖Ψ u‖≤1)→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀U,‖W (primeProductNorm p U)‖≤G)→
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta))→
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ (Z^M))‖≤
        C*Γ^2*G^2*‖paperRadialFourier Φ 0‖*Z^(M-ell+3*eta+ε*(5*ell+2*r+7*eta)):=by
  obtain ⟨C,hC,he⟩:=original_reopened_marked_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Z M r ell V eta Γ G
    hZ hell hV hΓ hG hΨ hQ hn hlabels hβ hslots ha hW hs
  have hz:0<Z:=zero_lt_one.trans hZ
  have hb:=he p hp hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G
    (Z^(r+eta)) (Z^M) (Z^(ell+eta)) (Z^(V+eta)) hΓ hG
    (Real.rpow_pos_of_pos hz _) (Real.one_le_rpow hZ.le hell) (Real.one_le_rpow hZ.le hV)
    hΨ hQ hn hlabels hβ hslots ha hW hs
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.le _)).trans
  apply le_of_eq
  rw [abs_of_pos (Real.rpow_pos_of_pos hz M)]
  have hp2 (x:ℝ):(Z^x)^2=Z^(2*x):=by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
  rw [hp2,←Real.rpow_add hz,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,hp2]
  calc
    _=(C*Γ^2*G^2*‖paperRadialFourier Φ 0‖)*
      (Z^(-r-2*ell-V)*Z^((ell+eta)*(1+ε))*Z^(r+eta)*Z^(V+eta)*
        Z^(2*((2*(ell+eta)+(r+eta))*ε))*Z^M):=by ring
    _=_:=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

end SevenEighths.InverseMoment

end

end OAI

end Source2725

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstDyadicOriginalBranches.lean; sha256: 99daa5d838b03b7eb8da4b8cdf6a414ca3a3500e3e5477b0bc47aa0ad6f6815c -/
section Source2726
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight SecondPassIntegration FourierBridge
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤b)(hMm:0≤Mmax)(hFm:0≤Fmax)(heta:0≤eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤Z^eta→0≤M→M≤Mmax→0≤ell→0≤V→ (-eta≤r) → (r+3*ell+V≤Fmax)→0≤Γ→b≤Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤Ctail*Γ^2*Z^(-saving):=by
  obtain ⟨Cz,hCz,hzero⟩:=original_first_zero_physical eps heps
  obtain ⟨s,Ct,hCt,htail⟩:=full_first_dyadic_marked_rapid_tail Mmax Fmax eta tau saving hMm hFm heta htau
  let G:=SchwartzMap.seminorm ℝ 0 0 om
  let Cz':=Cz*G^2*‖paperRadialFourier rowMajorant 0‖
  let Ct':=Ct*G^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)
  refine ⟨Cz',Ct',by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ hbin hM hMmax hell hV hr hF hΓ hb hΨ hQ hn hlabels hβ hslots hw W mark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hG:0≤G:=apply_nonneg _ _
  have hW:∀U,‖W (primeProductNorm p U)‖≤G:=by
    intro U
    simp only [W,normTwistedSource,norm_mul,logPhase_norm,one_mul]
    exact om.norm_le_seminorm ℝ _
  have hsupport:∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta):=by
    intro U hU
    have hnon:om (primeProductNorm p U/Z^r)≠0:=by
      intro hh
      exact hU (by simp [W,normTwistedSource,hh])
    have hle:primeProductNorm p U≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
    apply hle.trans
    calc
      b*Z^r≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  have hzero':=hzero p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights W rowMajorant
    Z M r ell V eta Γ G hZ (by linarith) (by linarith) hΓ hG hΨ hQ hn hlabels hβ hslots hw hW hsupport
  have hcb:=reopenedCubeFamily_cube_norms p Q _ hQ
  have htail':=htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    Ψ Ψ m m slots lists weights (fun q=>q.rightExponent.support) (fun q=>q.leftExponent.support)
    (fun _ U=>W (primeProductNorm p U)) (fun _ U=>W (primeProductNorm p U)) rowMajorant Z M r ell V
    (Γ^2) G G hZ hbin hM hMmax hell hV hr hF (sq_nonneg _) hG hG hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun q hq=>(hcb q hq).1) (fun q hq=>(hcb q hq).2)
    hn hlabels (fun q hq C _ I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ q hq C I hI)
    hslots hw (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hsupport) (fun _ _=>hsupport)
  constructor
  · simpa only [mark,Finset.union_comm,Cz',G,mul_assoc,mul_left_comm,mul_comm] using hzero'
  · simpa only [mark,reopenedPhysicalSourceSum,Ct',pow_two,mul_assoc,mul_left_comm,mul_comm] using htail'

end SevenEighths.InverseMoment

end

end OAI

end Source2726

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstDyadicFullEnergy.lean; sha256: e5165973b95ff4763c9dcf8308297cb02e19e282d5098fc5b844fa664ff010a3 -/
section Source2727
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤Lcap)(hMmax:0≤Mmax)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C Czero Ctail:ℝ,0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Mmax)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_priority_budget om rowMajorant a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,hret⟩:=he eps heps J
  obtain ⟨Cz,Ct,hCz,hCt,hbranches⟩:=original_dyadic_zero_tail om b Mmax Lcap eta tau (saving+eta) eps
    (fun y hy=>(hs hy).2) hMmax hcap heta htau heps
  refine ⟨C,Cz,Ct,hC,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Benergy
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hB hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have hK:0<Z^M:=Real.rpow_pos_of_pos hz _
  have he':=original_global_physical_energy p hp hcop hg hinj hc hpr pool Q hQpool labels hn β Ψ m mark W
    (Z^M) Y hK cutoff (fun _ _ _ _ _ _ _=>Real.rpow_nonneg hz.le _)
    (fun x hx _ _=>first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ x hx)
    (fun _=>1) (by intro i;norm_num)
  have hret':=hret p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Lcap Γ
    (Z^M) theta Benergy hZ hbin hM hF hQ hrcap hellcap hcap le_rfl heta heta1 htau.le htau1 hΨ hΓ hK hB hsf hn hβ hleft hright
  obtain ⟨hz',ht'⟩:=hbranches p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ1 hbin hM hMcap hell hV hr hF hΓ hbZ hΨ hQ hn hlabels hβ hslots hweights
  have hfactor:Z^(-r-2*ell-V)≤Z^eta:=Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have htail:Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q D I=>
        canonicalCubeDualTail p hp hcop hg pool q D Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (reopenedPhysicalCutoff p q I (cutoff q D I)))‖≤Ct*Γ^2*Z^(-saving):=by
    have ht'':_≤Ct*Γ^2*Z^(-(saving+eta)):=ht'
    apply (mul_le_mul hfactor ht'' (norm_nonneg _) (Real.rpow_nonneg hz.le _)).trans
    apply le_of_eq
    rw [show Z^eta*(Ct*Γ^2*Z^(-(saving+eta)))=(Ct*Γ^2)*(Z^eta*Z^(-(saving+eta))) by ring,
      ←Real.rpow_add hz]
    congr 2
    ring
  have hall:=mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hz.le (-r-2*ell-V))
  simp only [mul_add] at hall
  apply hall.trans
  have hr':Z^(-r-2*ell-V)*((Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant (Z^M) Y cutoff (fun _=>1)‖)≤
      C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Lcap+15*eta+tau)*eps+eps):=by
    simpa only [mul_assoc] using hret'
  exact add_le_add (add_le_add hz' hr') htail

end SevenEighths.InverseMoment

end

end OAI

end Source2727

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongSource.lean; sha256: 15470a71e9a98d153ccf86a46cdae2e32acd60d748910f215af76db5f44b28c4 -/
section Source2728
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation FourierBridge CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

theorem long_frequency_profile
    {ι:Type*}(p:ι→O)(hp:∀i,p i≠0)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)
    (Z r ξ:ℝ)(hZ:0<Z)(T:Finset ι) :
    frequencyTwist V ξ (columnLog p (Z^r) T)=
      normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
        (primeProductNorm p T/Z^r) := by
  rw [normTwistedSource,radialFromLog_column p hp V (V.smooth ⊤) A hV _ (Real.rpow_pos_of_pos hZ r)]
  simp only [frequencyTwist_apply,columnLog]

theorem long_marked_source_eq
    {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(β:(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m f z:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)(Z r ξ:ℝ)(hZ:0<Z) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (T∪v.support)*
        frequencyTwist V ξ (columnLog p (Z^r) T)) z =
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (v.support∪T)*
        normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
          (primeProductNorm p T/Z^r)) z := by
  congr 1
  funext v T
  rw [long_frequency_profile p hp V A hV Z r ξ hZ T,Finset.union_comm T v.support]

theorem marked_long_filter
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights=
      markedReopenedCubeBin S D (progressingCubes S D H₀ Q) Ψ m f z W X H₀ slots lists weights := by
  unfold markedReopenedCubeBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hz:largeCubeCoefficient H₀ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hv,(largeCubeCoefficient_support H₀ _ hh).2⟩)
  simp only [hz,zero_mul]

theorem long_cube_progress
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell:ℝ)(hZ:1<Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-1/Real.log Z≤ell+V := by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨hv,hlower⟩:=Finset.mem_filter.mp hv
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:=Real.log_le_log (Real.rpow_pos_of_pos hz _) (hlower.trans (hupper v hv))
  rw [Real.log_rpow hz,Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz] at he
  have hlog:=Real.log_pos hZ
  have hd: (cutoff-ell-V)*Real.log Z≤1:=by nlinarith
  have hh:cutoff-ell-V≤1/Real.log Z:=(le_div_iff₀ hlog).mpr hd
  linarith

theorem long_cube_progress_with_slack
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell eta:ℝ)(hZ:1<Z)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-eta≤ell+V := by
  have h:=long_cube_progress S D Q Z cutoff V ell hZ hne hupper
  have hh:1/Real.log Z≤eta:=(div_le_iff₀ (Real.log_pos hZ)).mpr (by simpa only [mul_comm] using hlog)
  linarith

theorem short_sum_zero_of_label_large
    (Ψ:O→*ℂ)(W:ℝ→ℂ)(mark:Ideal O→ℂ)(X Z cutoff V:ℝ)
    (hZ:1≤Z)(hV:cutoff≤V) :
    markedShortCompletedSum Ψ W X (Z^(cutoff-V)) mark=0 := by
  have ht:Z^(cutoff-V)≤1:=by
    have he:=Real.rpow_le_rpow_of_exponent_le hZ (show cutoff-V≤0 by linarith)
    simpa only [Real.rpow_zero] using he
  unfold markedShortCompletedSum
  trans ∑' _ : Ideal O,(0:ℂ)
  · apply tsum_congr
    intro I
    by_cases hi:I=0
    · subst I
      simp
    rw [ite_eq_right (not_lt.mpr (ht.trans (norm_at_least_one I hi)))]
  · exact tsum_zero

end SevenEighths.InverseMoment

end

end OAI

end Source2728

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongNormalization.lean; sha256: e134b8b53e5effd2f0e150118501fd31bd1b22a73c078a62bad1f0509c83a6ae -/
section Source2729
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem child_ball_unit_mem (u:Oˣ)(R:ℝ)(k:O) :
    (u:O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:Oˣ)(R:ℝ)(f:O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · intro x hx y hy he
    exact mul_left_cancel₀ u.ne_zero he
  · intro y hy
    refine ⟨((u⁻¹:Oˣ):O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    rw [←mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  · intros
    rfl

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(I:Ideal O)(hI:primaryGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (idealGenerator I) (span_idealGenerator I) hI
  let P:O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:O):
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2=
      P (((u^4:Oˣ):O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  simp only [he]
  exact hrot.symm

theorem normalized_energy_le_actual_family
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(C:ℝ)(hC:0≤C)(hw:∀I∈labels,0≤weight I ∧ weight I≤C)
    (W:ℝ→ℂ)(X Z F K:ℝ)(hZ:0<Z)(hK:0<K) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 K) weight W X Z F ≤
      Z^(-F)*C*rowFamilyEnergy labels (fun I k=>
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) K := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  have he : (∑ I∈labels,weight I*(Z^(-F)*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2))=
      Z^(-F)*(∑ I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  have hball:=finite_nonzero_row_energy_le_majorant
    (fun k=>finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X)
    (nonzeroChildFrequencyBall 1 K) K hK
    (by intro k hk
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).2)
    (by intro k hk hn
        have hh:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).1
        simp only [hn,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh)
  exact (mul_le_mul_of_nonneg_right (hw I hI).2 (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hball hC)

end SevenEighths.InverseMoment

end

end OAI

end Source2729

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongWeight.lean; sha256: 5fee752620b88ccac142922dbea1e6ba629c2bc90953d8e4d90b0100f2a3f95f -/
section Source2730
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤Z→V≤L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤Z^V→secondLabelWeight K I≤C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤C*Z^eps:=by gcongr

theorem normalized_second_energy_le_actual_family (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,goodLambda∉Ideal.span {p i})
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (W:ℝ→ℂ)(X Z F V R:ℝ),1≤Z→0<R→V≤L→
      (∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W X Z F≤
        C*Z^(-F+eps)*rowFamilyEnergy labels (fun I k=>
          finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) R := by
  obtain ⟨C,hC,hh⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg pool Ψ m slots lists a labels hlabels W X Z F V R hZ hR hV hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=normalized_energy_le_actual_family p hp hcop hg pool Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (admissible_supported (hlabels I hI)))
    (secondLabelWeight K) (C*Z^eps) (by positivity)
    (fun I hI=>⟨by unfold secondLabelWeight;positivity,
      hh Z V hZ hV I (hlabels I hI).1 (hnorm I hI)⟩) W X Z F R hz hR
  convert hb using 1
  rw [Real.rpow_add hz]
  ring

end SevenEighths.InverseMoment

end

end OAI

end Source2730

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongBins.lean; sha256: 361e42d600b50a7c65e96a3b3c8ee0b16c99ff78344944a39a2b6355752fbec9 -/
section Source2731
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_family_binned
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(hWc:HasCompactSupport W)
    (b X H₀ K:ℝ)(hX:0<X)(hK:0<K)(hW:∀t,W t≠0→t≤b)(hD:b*X≤D)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    rowFamilyEnergy labels (fun I z=>outsideCanonicalMarkedRow S D hbad Ψ m
      (idealGenerator I) z slots lists a W X) K ≤
    2*X*(rowFamilyEnergy labels (fun I z=>
      markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)) K+
      (cubeLogRange b X).card*∑j∈cubeLogRange b X,
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a) K) := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK]
  have he:∀I z,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W X‖^2 ≤
      2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2) := by
    intro I z
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b X H₀ slots lists a
      hbad hSp hWc hX hW hD
    have hs:(∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)=
        ∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [marked_long_filter S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a]
    rw [hs] at hh
    exact hh
  calc
    _≤∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
      (rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re *
      (2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (he I z) (rowMajorant_nonneg _)
    _=_ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_left_comm _ _ _
      · simp_rw [Finset.sum_comm (s:=(firstFrequencyDisk (2*K)).erase 0) (t:=cubeLogRange b X)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        ring

end SevenEighths.InverseMoment

end

end OAI

end Source2731

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongCount.lean; sha256: f1bbfb2acdb2b8d3ebf1869c234543c1395dbbb2af04aa3b33c4fdad2f13b846 -/
section Source2732
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open CanonicalRowCompletion SecondPassArithmetic

theorem actual_cube_bin_count (b L eps:ℝ)(hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀X Z:ℝ,0≤X→1≤Z→X≤Z^L→
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^eps := by
  have hLp:0<L+1:=by linarith
  have hd:0<3*eps/(L+1):=by positivity
  obtain ⟨C,hC,hh⟩:=cubeLogRange_sq_small_power b (3*eps/(L+1)) hb hd
  refine ⟨C,hC,?_⟩
  intro X Z hX hZ hXL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hscale:(Z^((L+1)/3))^3=Z^(L+1) := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  have hpow:(Z^((L+1)/3))^(3*eps/(L+1))=Z^eps := by
    rw [←Real.rpow_mul hz.le]
    congr 1
    field_simp
  have hbnd:=hh X (Z^((L+1)/3)) hX (Real.one_le_rpow hZ (by positivity))
    (by rw [hscale];exact hXL.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
  simpa only [hpow] using hbnd

end SevenEighths.InverseMoment

end

end OAI

end Source2732

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongCoefficient.lean; sha256: 809dc6fec469dab5af2e623e76f29766440af8500491ad8dc62c8113ef2ea06f -/
section Source2733
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualLongCoefficient {ι:Type*}(p:ι→O)(Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)
    (I:Ideal O)(v:ι→₀ℕ) : ℂ :=
  separatedCubeCoefficient
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ v

theorem actualLongCoefficient_uniform (eps:ℝ)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}(p:ι→O)(_hp:∀i,p i≠0)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)
      (m:O)(H₀ B ξ:ℝ)(I:Ideal O)(v:ι→₀ℕ),0<B→
      B≤‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2→
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B→
      ‖actualLongCoefficient p Ψ m H₀ B ξ I v‖≤C*(Real.exp 1*B)^eps := by
  obtain ⟨C,hC,hbound⟩:=reopenedCubeCoefficient_small_power eps heps
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro ι p hp Ψ hΨ m H₀ B ξ I v hB hlo hhi
  have hne:Ideal.span {primeProduct p v.support v}≠0 := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i hi=>pow_ne_zero _ (hp i))
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hlo hhi
  have hh:=hbound H₀ (rowTwist Ψ m (idealGenerator I) 1)
    (rowTwist_norm Ψ hΨ m (idealGenerator I) 1) _ hne
  have hb:‖reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p v.support v})‖≤C*(Real.exp 1*B)^eps :=
    hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi heps.le) hC.le)
  have hs:=separatedCubeCoefficient_bound
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ
    (C*(Real.exp 1*B)^eps) hB (by positivity) v hlo hhi hb
  unfold actualLongCoefficient
  convert hs using 1 ; ring

theorem actualLongCoefficient_complete
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)(I:Ideal O)
    (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    actualLongCoefficient (poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D))
      Ψ (m*excludedGenerator S) H₀ B ξ I v=
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1)
        (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v := by
  simp only [actualLongCoefficient,cubeIdeal_eq_primeProduct_span _
    (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]

end SevenEighths.InverseMoment

end

end OAI

end Source2733

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongFull.lean; sha256: 3c1a8f4feb59d86172933d65efb4c4ffd9735ee9ac6e1ca9f345aa676df31174 -/
section Source2734
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_long_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤Lcap)(hMmax:0≤Mmax)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃Ccoef C Czero Ctail:ℝ,0<Ccoef ∧ 0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hbinExp:Real.exp 1≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Mmax)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖eisEmbedding (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*Z^ell)
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Benergy*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(-saving) := by
  obtain ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=
    original_dyadic_full_energy om a b ha hs Lcap Mmax eta tau saving hcap hMmax hb heta heta1 htau htau1
  refine ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform eps heps
  obtain ⟨C,Czero,Ctail,hC,hCzero,hCtail,hfull⟩:=he eps heps J
  refine ⟨Ccoef,C,Czero,Ctail,hCcoef,hC,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ Benergy hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hΨ hB hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤Ccoef*(Real.exp 1*Z^ell)^eps := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^eps) ξ Benergy hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hΨ (by positivity) hB hsf hn hβ hlabels hslots hweights hleft hright

end SevenEighths.InverseMoment

end

end OAI

end Source2734

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongIntegral.lean; sha256: 1ace9c318e741ec03009f02dd78dec47408c99e4334f5148070a6a3b8dd4a772 -/
section Source2735
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem actual_long_bin_normalized_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Z r cubeLength Vheight H₀ K E : ℝ) (d : ℕ)
    (hZ : 0 < Z) (hD : b*(Z^(r+3*cubeLength))≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, (Z^cubeLength) ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*(Z^cubeLength))
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, Z^(-r-2*cubeLength-Vheight)*rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    Z^(-Vheight)*rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W (Z^(r+3*cubeLength)) H₀ slots lists weights) K ≤
      E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β:=fun I v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hcancel:Z^(r+2*cubeLength+Vheight)*Z^(-r-2*cubeLength-Vheight)=1 := by
    rw [←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hpoint:∀ξ:ℝ,rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ)
        Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K≤
      (Z^(r+2*cubeLength+Vheight)*E)*(1+|ξ|)^(2*d) := by
    intro ξ
    have hh:=mul_le_mul_of_nonneg_left (hsource ξ) (Real.rpow_nonneg hZ.le (r+2*cubeLength+Vheight))
    rw [←mul_assoc,hcancel,one_mul] at hh
    simpa only [mul_assoc] using hh
  have hX:Z^(r+3*cubeLength)=(Z^cubeLength)^3*Z^r := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  have hbnd:=markedReopenedCubeBin_energy S D hbad hSp Q labels Ψ m W a b ha hb hs hW V hV
    (Z^cubeLength) (Z^r) (Z^(r+3*cubeLength)) H₀ K (Z^(r+2*cubeLength+Vheight)*E) d
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hX hD hK (by positivity)
    hn hn' slots lists weights hpoint
  have hc:Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight)=1 := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ,←Real.rpow_neg hZ.le,
      ←Real.rpow_add hZ,←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hh:=mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hZ.le (-Vheight))
  apply hh.trans_eq
  calc
    _=(Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight))*
      E*(∫ξ:ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by ring
    _=_:=by rw [hc,one_mul]

end
end SevenEighths.InverseMoment

end OAI

end Source2735

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongCaller.lean; sha256: 4528b2ecce32768cce0c91695dd5119a02fff5179895383540cfe79b1eb9aff6 -/
section Source2736
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem normalized_complete_marked_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z→0<R→V≤L→(∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      (∀t,W t≠0→t≤b)→b*Z^N≤D→
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W (Z^N) Z (N+V)≤
      2*C*Z^(-V+eps)*(
        rowFamilyEnergy labels (fun I z=>markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W (Z^N) H₀
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)) R+
        (cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
          rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
            (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
            Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R) := by
  obtain ⟨C,hC,hh⟩:=normalized_second_energy_le_actual_family K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀
    hZ hR hV hnorm hW hD
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=hh (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels hlabels W
    (Z^N) Z (N+V) V R hZ hR hV hnorm
  have hsplit:=actual_marked_family_binned S D hbad hSp labels Ψ m W hWc
    b (Z^N) H₀ R (Real.rpow_pos_of_pos hz _) hR hW hD slots lists a
  have hcost: C*Z^(-(N+V)+eps)*(2*Z^N)=2*C*Z^(-V+eps) := by
    calc
      _=2*C*(Z^(-(N+V)+eps)*Z^N):=by ring
      _=2*C*Z^(-V+eps):=by rw [←Real.rpow_add hz];congr 2;ring
  apply hb.trans
  have he:=mul_le_mul_of_nonneg_left hsplit (show 0≤C*Z^(-(N+V)+eps) by positivity)
  rw [←mul_assoc,hcost] at he
  exact he

end SevenEighths.InverseMoment

end

end OAI

end Source2736

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongAggregate.lean; sha256: cb0d2ffb8c4b7c02e87632e081eb343629110eb13c221e2b07daae0400d236ca -/
section Source2737
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

 theorem actual_marked_bin_empty
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (he:¬(progressingCubes S D H₀ Q).Nonempty) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a=0 := by
  rw [marked_long_filter,Finset.not_nonempty_iff_eq_empty.mp he]
  simp only [markedReopenedCubeBin,Finset.sum_empty]

theorem actual_large_bins_aggregate
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(b X H₀ R Z V E:ℝ)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (hbin:∀j∈cubeLogRange b X,
      (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty→
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E)
    (hE:0≤E) :
    Z^(-V)*((cubeLogRange b X).card*∑j∈cubeLogRange b X,
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R)≤
      ((cubeLogRange b X).card:ℝ)^2*E := by
  have hj (j:ℕ)(hj:j∈cubeLogRange b X) :
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E := by
    by_cases hn:(progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · exact hbin j hj hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simpa only [markedReopenedCubeBin,Finset.sum_empty,rowFamilyEnergy,
        nonzeroRowMajorantSum,norm_zero,zero_pow (by decide:2≠0),Complex.ofReal_zero,
        mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hE
  calc
    _=(cubeLogRange b X).card*∑j∈cubeLogRange b X,
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R := by rw [←Finset.mul_sum];ring
    _≤(cubeLogRange b X).card*∑_j∈cubeLogRange b X,E := by
      gcongr
      exact hj _ ‹_›
    _=_ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2737

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongFinite.lean; sha256: d6107c0c8f844020d6e0cfbeb82461cc80fe880a94a782cb6a15e096dcbf4d4e -/
section Source2738
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_finite_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z → 0<R → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2) ≤
      2*(Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2))+
      2*C*Z^(-V+eps)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R := by
  obtain ⟨C,hC,hweight⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let bins:=cubeLogRange b (Z^N)
  let short:=fun I z=>markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
    W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  let long:=fun j I z=>markedReopenedCubeBin S D
    (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
    Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a
  let ball:=nonzeroChildFrequencyBall 1 R
  have hpoint (I:Ideal O)(z:O):
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2≤
      2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2) := by
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b (Z^N) H₀ slots lists a
      hbad hSp hWc (Real.rpow_pos_of_pos hz _) hW hD
    convert hh using 1
    congr 2
    apply congrArg (fun x:ℝ=>(bins.card:ℝ)*x)
    apply Finset.sum_congr rfl
    intro j hj
    rw [marked_long_filter S D (activeCubeLogBin S D b (Z^N) j) Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a]
  have hlong (j:ℕ):
      (∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2)≤
      C*Z^eps*rowFamilyEnergy labels (long j) R := by
    rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hb:=finite_nonzero_row_energy_le_majorant (long j I) ball R hR
      (by intro z hz;rw [←eisEmbedding_norm_sq_eq_absNorm_span]
          simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).2)
      (by intro z hz he
          have hn:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).1
          simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hn)
    exact (mul_le_mul_of_nonneg_right (hweight Z V hZ hV I (hlabels I hI) (hnorm I hI))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hsum:=Finset.sum_le_sum (s:=labels) (fun I hI=>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=ball) (fun z hz=>hpoint I z))
      (show 0≤secondLabelWeight K I by unfold secondLabelWeight;positivity))
  have he:=mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le (-(N+V)))
  have hc:Z^(-(N+V))*Z^N=Z^(-V):=by rw [←Real.rpow_add hz];congr 1;ring
  have rearrange:
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈ball,
        2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2))=
      2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)+
      2*Z^(-V)*bins.card*∑j∈bins,∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2 := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp_rw [Finset.sum_comm (s:=ball) (t:=bins)]
    rw [Finset.sum_comm (s:=labels) (t:=bins)]
    simp only [←Finset.mul_sum,mul_assoc,mul_left_comm]
    rw [←hc]
    ring
  rw [rearrange] at he
  apply he.trans
  have hj:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=bins) (fun j hj=>hlong j))
    (show 0≤2*Z^(-V)*(bins.card:ℝ) by positivity)
  rw [←Finset.mul_sum] at hj
  have hpow:Z^(-V)*Z^eps=Z^(-V+eps):=(Real.rpow_add hz _ _).symm
  convert add_le_add_left hj (2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)) using 1 <;>
    dsimp [bins,short,long,ball] <;> (try rw [←hpow]) <;> ring

end SevenEighths.InverseMoment

end

end OAI

end Source2738

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongTotal.lean; sha256: 2d255b9b3c463c35cf950d0c2b376efbb632ef8e1078f494c633eff3be3b061a -/
section Source2739
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_energy_from_live_bins (K:ℕ)(b L eps:ℝ)
    (hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(Z N V R H₀ Eshort Elong:ℝ),
      1≤Z → 0<R → N≤L → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D → 0≤Elong →
      Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2)≤Eshort →
      (∀j∈cubeLogRange b (Z^N),
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤Elong) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2)≤
      2*Eshort+C*Z^eps*Elong := by
  obtain ⟨Cw,hCw,hw⟩:=actual_complete_finite_split K L (eps/2) hL (by positivity)
  obtain ⟨Cb,hCb,hbnd⟩:=actual_cube_bin_count b L (eps/2) hb hL (by positivity)
  refine ⟨2*Cw*Cb,by positivity,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc Z N V R H₀ Eshort Elong
    hZ hR hN hV hnorm hW hD hE hshort hlong
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:=hw S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have ha:=actual_large_bins_aggregate S D labels Ψ m W b (Z^N) H₀ R Z V Elong slots lists a hlong hE
  have hc:=hbnd (Z^N) Z (Real.rpow_nonneg hz.le _) hZ (Real.rpow_le_rpow_of_exponent_le hZ hN)
  have hh:Z^(eps/2)*Z^(eps/2)=Z^eps := by rw [←Real.rpow_add hz];congr 1;ring
  have hp:Z^(-V+eps/2)=Z^(-V)*Z^(eps/2):=Real.rpow_add hz _ _
  have ha':2*Cw*Z^(-V+eps/2)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
        Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤
      (2*Cw*Cb)*Z^eps*Elong := by
    have h1:=mul_le_mul_of_nonneg_left ha (show 0≤2*Cw*Z^(eps/2) by positivity)
    have h2:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE)
      (show 0≤2*Cw*Z^(eps/2) by positivity)
    have ht:=h1.trans h2
    rw [hp]
    convert ht using 1
    · ring
    · rw [←hh];ring
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_left hshort (by norm_num:0≤(2:ℝ))) ha')

end SevenEighths.InverseMoment

end

end OAI

end Source2739

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteState.lean; sha256: c383988283e3a3e02324a73c7211f71fe374cd1ba000490cb2e1ad6d850aaf83 -/
section Source2740
namespace OAI

noncomputable section

open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseReflectedPhase InverseTerminalWidths CompletedHeight
open InverseCanonicalShortAttachment InverseSecondFibers FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
universe v

theorem actual_complete_state_from_live_bins
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hWs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (L cstar eta eps:ℝ)(hL:0≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤cstar/100000)(heps:0<eps)(rmax K:ℕ) :
    ∃degree:ℕ,∀(q:ℕ)(_hq:q≠0),∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀{σ:Type v}[DecidableEq σ](m:O),m≠0 → ∀Z N V M z₀ margin cutoff:ℝ,
      Z₀≤Z → 0≤N → N≤L → 0≤V → V≤L → 0≤M → M≤L → z₀≤L →
      0≤cutoff → cutoff≤L → cutoff≤cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤rmax →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).Pairwise (fun i j=>Disjoint (lists i) (lists j)) →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀(theta:ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) → ∀E:ℝ,0≤E →
      let S:=reflectionExcludedPrimes q;
      let test:=normTwistedSource W theta;
      (∀j∈cubeLogRange hi (Z^N),
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j))
          Ψ m (idealGenerator I) z test (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤E) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a test (Z^N)‖^2)≤
      C*((1+‖theta‖)^degree*Z^(N+V-cstar/256)+Z^eps*E) := by
  obtain ⟨degree,hs⟩:=actual_complete_short_finite_uniform_degree lo hi hlo W hWs hW L cstar eta
    hL hcstar heta heta1 hetac rmax K
  obtain ⟨Cl,hCl,hl⟩:=actual_complete_energy_from_live_bins K hi L eps hhi hL heps
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨Cs,Z₀,hCs,hZ₀,hshort⟩:=hs q hq
  refine ⟨2*Cs+Cl,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff hZ hN hNL hV hVL hM hML hzL hcut hcutL hcutc
    hmN hmargin hreserve labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE
  dsimp only
  intro hbins
  have hz:0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hZ1:1≤Z:=(hZ₀.trans_le hZ).le
  let S:=reflectionExcludedPrimes q
  let test:=normTwistedSource W theta
  let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
  have htest:HasCompactSupport test:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((normTwistedSource_support W theta).trans hWs)
  have hupper:∀x,test x≠0 → x≤hi:=fun x hx=>(hWs (normTwistedSource_support W theta hx)).2
  have hT:∀z∈nonzeroChildFrequencyBall 1 (Z^M),z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^M := by
    intro z hz
    have hh:=(mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) z).mp hz
    constructor
    · intro he
      simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh
      exact hh.1
    · rw [←eisEmbedding_norm_sq_eq_absNorm_span]
      simpa only [one_mul] using hh.2
  have hshortbound:Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
      ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
        test (Z^N) (Z^(cutoff-V)) mark‖^2)≤Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256) := by
    by_cases hbig:cutoff≤V
    · have he (I:Ideal O)(z:O):markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) test (Z^N) (Z^(cutoff-V)) mark=0:=
        short_sum_zero_of_label_large _ _ _ _ _ _ _ hZ1 hbig
      simp only [he,norm_zero,zero_pow (by decide:2≠0),Finset.sum_const_zero,mul_zero]
      positivity
    · exact hshort m hm Z N V M z₀ margin (cutoff-V) cutoff hZ hN hV hM hML hVL hzL
        (by linarith) (by linarith) hmN hmargin hreserve (by linarith) (by linarith) hcutc
        labels hlabels (nonzeroChildFrequencyBall 1 (Z^M)) hT D hD slots hcard lists H
        hdis hH1 hH hprod Ψ hΨ hperiod theta a ha
  have hb:=hl S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q) labels
    (fun I hI=>(hlabels I hI).1.1) Ψ m slots lists a test htest Z N V (Z^M)
    (Z^(cutoff-V)) (Cs*(1+‖theta‖)^degree*Z^(N+V-cstar/256)) E
    hZ1 (Real.rpow_pos_of_pos hz _) hNL hVL (fun I hI=>(hlabels I hI).2.2)
    hupper hD hE hshortbound hbins
  apply hb.trans
  have hA:0≤(1+‖theta‖)^degree*Z^(N+V-cstar/256):=by positivity
  have hB:0≤Z^eps*E:=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI

end Source2740

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongGeometry.lean; sha256: 3c228ce6ac1113840375dd35e9327b5331f3e569e108e1f66794c91051c2c0f7 -/
section Source2741
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualCubeLength (Z:ℝ)(j:ℕ):ℝ:=Real.logb Z (normLogScale j)

theorem actualCubeLength_power (Z:ℝ)(hZ:1<Z)(j:ℕ) :
    Z^(actualCubeLength Z j)=normLogScale j :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normLogScale_pos j)

theorem actual_long_bin_geometry
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (b Z N V cutoff eta L:ℝ)(j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:eta≤1)
    (hV:0≤V)(hparent:N+V≤L)(hb:b≤Z^eta)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j)).Nonempty) :
    let ell:=actualCubeLength Z j;
    let r:=N-3*ell;
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j);
    0≤ell ∧ -eta≤r ∧ r≤L ∧ ell≤L ∧ r+3*ell+V≤L ∧ cutoff-eta≤ell+V ∧
      ∀v∈Q,Z^ell≤‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2≤Real.exp 1*Z^ell := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hp:Z^(actualCubeLength Z j)=normLogScale j:=actualCubeLength_power Z hZ j
  have hel:0≤actualCubeLength Z j:=Real.logb_nonneg hZ (normLogScale_ge_one j)
  have hnorm (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
      (hv:v∈activeCubeLogBin S D b (Z^N) j) :
      Z^(actualCubeLength Z j)≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) ∧
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*Z^(actualCubeLength Z j) := by
    rw [hp]
    exact activeCubeLogBin_norms S D b (Z^N) j v hv
  obtain ⟨v,hv⟩:=hne
  have hvbin: v∈activeCubeLogBin S D b (Z^N) j := (Finset.mem_filter.mp hv).1
  have hactive:= (Finset.mem_filter.mp hvbin).1
  have hcube:(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3≤b*Z^N :=
    (Finset.mem_filter.mp hactive).2
  have hsc:(Z^(actualCubeLength Z j))^3≤Z^(N+eta) := by
    calc
      _≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (hnorm v hvbin).1 3
      _≤b*Z^N:=hcube
      _≤Z^eta*Z^N:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(N+eta):=by rw [Real.rpow_add hz];ring
  rw [←Real.rpow_mul_natCast hz.le] at hsc
  have hscale:actualCubeLength Z j*3≤N+eta := (Real.rpow_le_rpow_left_iff hZ).mp hsc
  have hprogress:=long_cube_progress_with_slack S D (activeCubeLogBin S D b (Z^N) j)
    Z cutoff V (actualCubeLength Z j) eta hZ hlog ⟨v,hv⟩ (fun v hv=>(hnorm v hv).2)
  refine ⟨hel,by linarith,by linarith,by linarith,by linarith,hprogress,?_⟩
  intro u hu
  rw [cubeIdeal_primeProduct_norm _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  exact hnorm u (Finset.mem_filter.mp hu).1

end SevenEighths.InverseMoment

end

end OAI

end Source2741

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongCosts.lean; sha256: c621fc457e516eded9963006e3b80d621c3a4f0513d83fac1253a70128be752f -/
section Source2742
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment

theorem actual_long_coefficient_cost (Z ell L epsilon Ccoef:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon):
    (Ccoef*(Real.exp 1*Z^ell)^epsilon)^2≤
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hex:(Real.exp 1)^epsilon=Real.exp epsilon:=by rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,one_mul]
  have hex2:(Real.exp epsilon)^2=Real.exp (2*epsilon):=by rw [←Real.exp_nat_mul];norm_num
  have hid:(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2=
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*ell*epsilon) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _),hex,
      ←Real.rpow_mul hz.le,mul_pow,mul_pow,hex2,
      ←Real.rpow_mul_natCast hz.le]
    ring_nf
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  nlinarith

theorem actual_long_uniform_parent_cost (Z ell N V L epsilon Ccoef C A loss:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon)(hC:0≤C)(hA:0≤A):
    C*(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2*(1+A)*Z^((N-3*ell)+3*ell+V+loss)≤
      (C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*Z^(N+V+loss+2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have h:=actual_long_coefficient_cost Z ell L epsilon Ccoef hZ hell heps
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h hC) (by linarith:0≤1+A))
    (Real.rpow_nonneg hz.le ((N-3*ell)+3*ell+V+loss))
  apply hh.trans_eq
  have hpow:Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)=Z^(N+V+loss+2*L*epsilon):=by
    rw [←Real.rpow_add hz];congr 1;ring
  calc
    _=(C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*
        (Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)):=by ring
    _=_:=by rw [hpow]

theorem complete_state_power_absorption (Z F cstar eps loss C A height E:ℝ)
    (hZ:1≤Z)(hc:0≤cstar)(heps:0≤eps)(hloss:0≤loss)
    (hC:0≤C)(_hA:0≤A)(hheight:0≤height)
    (hE:E≤A*height*Z^(F+loss)):
    C*(height*Z^(F-cstar/256)+Z^eps*E)≤
      C*(1+A)*height*Z^(F+loss+eps) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:height*Z^(F-cstar/256)≤height*Z^(F+loss+eps):=by
    apply mul_le_mul_of_nonneg_left _ hheight
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have ht:Z^eps*E≤A*height*Z^(F+loss+eps):=by
    have hh:=mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hz.le eps)
    apply hh.trans_eq
    rw [Real.rpow_add hz (F+loss) eps]
    ring
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hs ht) hC
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI

end Source2742

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveExponentCaps.lean; sha256: 28bbe20264334b90897f71eddd09822c7c1fa9556a7a72adbd98cd4f20107937 -/
section Source2743
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma actual_dyadic_exponent_cap (Z eta x A:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x)(hcap:x≤Z^A):
    0≤dyadicExponent Z (dyadIndex x) ∧ dyadicExponent Z (dyadIndex x)≤A:=by
  have h:=first_dyadic_bounds Z eta x hZ hbin hx
  exact ⟨h.1,(Real.rpow_le_rpow_left_iff hZ).mp (h.2.1.trans hcap)⟩

theorem original_live_exponent_caps {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z r ell F eta tau theta b:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)
    (hF:0≤F)(hr:r≤F)(hell:ell≤F)(heta:0≤eta)(htau:0≤tau)(hb:b≤Z^eta)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤b):
    let Y:=Z^(2*F+15*eta+tau);
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
    ∀k∈liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),
      (∀i,0≤dyadicExponent Z (k.1 i) ∧ dyadicExponent Z (k.1 i)≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.1 ∧ dyadicExponent Z k.2.1≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.2 ∧ dyadicExponent Z k.2.2≤3*F+15*eta+tau):=by
  intro Y W source k hk
  have hz:0<Z:=zero_lt_one.trans hZ
  have hW:∀y,W y≠0→y≤Z^(r+eta):=by
    intro y hy
    have hh:om (y/Z^r)≠0:=by intro hh;exact hy (by simp [W,normTwistedSource,hh])
    calc
      y≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hh)
      _≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨⟨x,j⟩,hmem,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hmem
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  obtain ⟨h₁,h₂,h₃⟩:=InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K
    (Z^(r+eta)) (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) hQ hlabels hW x hx j hnon
  have hlow:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hsq:(Z^(ell+eta))^2=Z^(2*ell+2*eta):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;norm_num;ring
  have hA:Z^(r+eta)≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hB:(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hAB:Z^(r+eta)*(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hY:Y≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply actual_dyadic_exponent_cap Z eta _ _ hZ hbin (hlow i)
    apply (h₁ i).trans
    fin_cases i <;> first | exact hA | exact hAB | exact hB | exact hY
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin (primeProductNorm_ge_one p hp _) (h₂.trans hA)
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin
      (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)) (h₃.trans hB)

end SevenEighths.InverseMoment

end

end OAI

end Source2743

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveColumnScale.lean; sha256: 37a09bd5c516be209ef94f74a1dbee7f34682ca3ccbd26cb01edfa8b3cb20ef1 -/
section Source2744
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem first_profile_live_products (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0*q 2*q 5≤L ∧ q 1*q 2*q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  constructor
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 0)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 7)).trans (hW _ h₁)
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 1)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 8)).trans (hW _ h₂)

private theorem dyadic_column_scale {a c z X b : ℝ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hz : 1 ≤ z) (hprod : a * c * z ≤ b * X) :
    1 ≤ X / (dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z)) * b := by
  have hscale : dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z) ≤ a * c * z :=
    mul_le_mul
      (mul_le_mul (dyadIndex_bounds a ha).1 (dyadIndex_bounds c hc).1
        (dyadScale_pos _).le (zero_le_one.trans ha))
      (dyadIndex_bounds z hz).1 (dyadScale_pos _).le
      (mul_nonneg (zero_le_one.trans ha) (zero_le_one.trans hc))
  rw [div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)),
    one_mul, mul_comm X b]
  exact hscale.trans hprod

theorem original_live_column_scale {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K X b:ℝ)
    (_hX:0<X)(hW:∀y,W y≠0→y≤b*X)
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)):
    1≤physicalScales X k.1 k.2.1 7*b ∧ 1≤physicalScales X k.1 k.2.1 8*b:=by
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hzero
    exact hnon (by unfold sourceSummand;rw [hzero,mul_zero])
  have hb:=first_profile_live_products W Φ K (b*X) _ hq hW hprof
  constructor
  · change 1 ≤ X / (dyadScale (dyadIndex (leftNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 0) (hs 2) (primeProductNorm_ge_one p hp _) hb.1
  · change 1 ≤ X / (dyadScale (dyadIndex (rightNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 1) (hs 2) (primeProductNorm_ge_one p hp _) hb.2

end SevenEighths.InverseMoment

end

end OAI

end Source2744

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveRadiusPositive.lean; sha256: 0ec3edf5362679f3d0c374bf552e9aca3b3a663d1edf13ce2de6f7418933b7af -/
section Source2745
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem first_live_cell_radius_one {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y Z M r ell V eta tau:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (hlabels:∀I∈labels,I≠0):
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    ∀k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),1≤firstCellRadius Z M r ell V eta tau k.1 k.2.2:=by
  intro cutoff k hk
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  have hx:=(Finset.mem_product.mp hm).1
  have hweight:firstOriginalWeight p β cutoff x.1 x.2≠0:=by
    intro hh
    exact hnon (sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hh)
  have hrow:=original_weight_frequency p β cutoff x hweight
  obtain ⟨ho,hf⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hI,hfreq⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hf
  have hfreq0:x.2.2≠0:=(Finset.mem_erase.mp hfreq).1
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hI)
  have hn:= (mem_childFrequencyBall _ hE _ _).mp hrow
  have hone:=EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (mul_ne_zero hE hfreq0)
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    refine Finset.mem_filter.mpr ⟨?_,rfl⟩
    exact InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y _ _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)
  change 1≤firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact hone.trans hn

end SevenEighths.InverseMoment

end

end OAI

end Source2745

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstStepScalarCaps.lean; sha256: 33240702eacea3b5d2aca090ac641c842825c86f8d26d2d3cf212ea39ecc092c -/
section Source2746
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

 theorem first_step_scalar_caps (Z A M r ell V delta aa bb rr t j eta tau window b:ℝ)
    (hZ:1<Z)(hA:0≤A)(hM:0≤M)(hMcap:M≤A)(hr: -1≤r)(hrcap:r≤A)
    (hell:0≤ell)(hellcap:ell≤A)(hV:0≤V)(hVcap:V≤A)
    (hd:0≤delta)(hdcap:delta≤A)(haa:0≤aa)(haacap:aa≤A)
    (hbb:0≤bb)(hbbcap:bb≤A)(hrr:0≤rr)(_hrrcap:rr≤A)
    (ht:0≤t)(_htcap:t≤A)(hj:0≤j)(hjcap:j≤A)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hb:b≤Z^eta):
    let X:=Z^(r-aa-bb-t);
    let Y:=Z^(firstPhysicalHeight M r ell V delta bb j+12*eta+tau);
    X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
    b*X≤Z^(16*A+20) ∧ delta+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
    firstKappa M r ell V delta aa bb rr+(9/2:ℝ)*eta≤16*A+20 ∧
    (∀e:ℝ,e≤A→Z^(e+eta)≤Z^(16*A+20)):=by
  intro X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hX:X≤Z^A:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hX0:0≤X:=Real.rpow_nonneg hz.le _
  have hxy:X*Real.exp window≤Z^(A+1):=by
    calc
      _≤Z^A*Z^eta:=mul_le_mul hX hwindow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      _=Z^(A+eta):=(Real.rpow_add hz A eta).symm
      _≤Z^(A+1):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨hxy,?_,?_,?_,by linarith,?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · rw [show Y⁻¹=Z^(-(firstPhysicalHeight M r ell V delta bb j+12*eta+tau)) by
      dsimp [Y];rw [Real.rpow_neg hz.le]]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · calc
      b*X≤Z^eta*Z^A:=mul_le_mul hb hX hX0 (Real.rpow_nonneg hz.le _)
      _=Z^(eta+A):=(Real.rpow_add hz eta A).symm
      _≤Z^(16*A+20):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · unfold firstKappa
    linarith
  · intro e he
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith

theorem first_step_scalar_losses (A r ell aa bb rr t eta pi em ed:ℝ)
    (hA:0≤A)(hr:r≤A)(hell:ell≤A)(haa:0≤aa)(_hbb:0≤bb)(hbbA:bb≤A)
    (hrr:rr≤A)(_ht:0≤t)(htA:t≤A)(_heta:0≤eta)(heta1:eta≤1)
    (he:0≤em)(hd:0≤ed)(hpi:0≤pi)(hetaPi:6*eta≤pi)
    (hem:em*(20*A+30)≤pi/4)(hed:ed*(20*A+30)≤pi/4):
    em*(ell+rr/2+t+(16*A+20)+11*eta/2)≤pi ∧
    em*(r-aa-bb-t)+7*eta/2+ed*(3*ell+bb+t+5*eta)+
      2*em*(2*ell+bb+t+4*eta)≤pi+eta/2:=by
  have hm:=mul_le_mul_of_nonneg_left (show ell+rr/2+t+(16*A+20)+11*eta/2≤20*A+30 by linarith) he
  have h1:=mul_le_mul_of_nonneg_left (show r-aa-bb-t+2*(2*ell+bb+t+4*eta)≤20*A+30 by linarith) he
  have h2:=mul_le_mul_of_nonneg_left (show 3*ell+bb+t+5*eta≤20*A+30 by linarith) hd
  constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI

end Source2746

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveStepScalars.lean; sha256: 8b33b44f298e8f1e3dd294c8da2bce73ac2a2265c08e3295f840847cfd970fcd -/
section Source2747
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma columnScale_physical (Z r:ℝ)(hZ:1<Z)(k:SourceIndex)(l:ℕ)(negative:Bool):
    columnScale Z r k l negative=physicalScales (Z^r) k l (if negative then 7 else 8):=by
  rw [physicalScales_rpow Z r hZ k l]
  cases negative <;> rfl

 theorem original_live_step_scalars {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z M r ell V F eta tau theta oldb b window em ed pi:ℝ)
    (hZ:1<Z)(hbin:2≤Z^eta)(hF:0≤F)(hM:0≤M)(hMF:M≤F)
    (hr: -eta≤r)(hrF:r≤F)(hell:0≤ell)(hellF:ell≤F)(hV:0≤V)(hVF:V≤F)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hold:oldb≤Real.exp window)(hb:b≤Real.exp window)
    (hem:0≤em)(hed:0≤ed)(hpi:0≤pi)(hetapi:6*eta≤pi)
    (hsmall:em*(20*(3*F+16)+30)≤pi/4)(hsmall':ed*(20*(3*F+16)+30)≤pi/4)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤oldb):
    let A:=3*F+16;
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
    ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),∀negative:Bool,
      let X:=columnScale Z r k.1 k.2.1 negative;
      let Y:=firstCellRadius Z M r ell V eta tau k.1 k.2.2;
      1≤Y ∧ 1≤X*Real.exp window ∧ X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
      b*X≤Z^(16*A+20) ∧ exponent Z (k.1 3)+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
      firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))+
        (9/2:ℝ)*eta≤16*A+20 ∧
      em*(ell+exponent Z (k.1 4)/2+exponent Z k.2.1+(16*A+20)+11*eta/2)≤pi ∧
      em*(r-columnA Z k.1 negative-exponent Z (k.1 2)-exponent Z k.2.1)+7*eta/2+
        ed*(3*ell+exponent Z (k.1 2)+exponent Z k.2.1+5*eta)+
        2*em*(2*ell+exponent Z (k.1 2)+exponent Z k.2.1+4*eta)≤pi+eta/2 ∧
      ell+eta≤16*A+20 ∧ exponent Z (k.1 4)+eta≤16*A+20 ∧
      exponent Z (k.1 2)+eta≤16*A+20 ∧ exponent Z k.2.1+eta≤16*A+20:=by
  intro A cutoff W S k hk negative X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hA:0≤A:=by dsimp [A];linarith
  have hFA:F≤A:=by dsimp [A];linarith
  obtain ⟨hcoords,ht,hj⟩:=original_live_exponent_caps p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell F eta tau theta oldb
    hZ hbin hF hrF hellF heta htau (hold.trans hwindow) hQ hlabels hs k hk
  have hecap:3*F+15*eta+tau≤A:=by dsimp [A];linarith
  have hkcap:∀i,0≤exponent Z (k.1 i) ∧ exponent Z (k.1 i)≤A:=fun i=>⟨(hcoords i).1,(hcoords i).2.trans hecap⟩
  have hacap:0≤columnA Z k.1 negative ∧ columnA Z k.1 negative≤A:=hkcap (if negative then 0 else 1)
  have htcap:exponent Z k.2.1≤A:=ht.2.trans hecap
  have hjcap:exponent Z k.2.2≤A:=hj.2.trans hecap
  have hscl:=first_step_scalar_caps Z A M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative)
    (exponent Z (k.1 2)) (exponent Z (k.1 4)) (exponent Z k.2.1) (exponent Z k.2.2) eta tau window b
    hZ hA hM (hMF.trans hFA) (by linarith) (hrF.trans hFA) hell (hellF.trans hFA) hV (hVF.trans hFA)
    (hkcap 3).1 (hkcap 3).2 hacap.1 hacap.2 (hkcap 2).1 (hkcap 2).2 (hkcap 4).1 (hkcap 4).2
    ht.1 htcap hj.1 hjcap heta heta1 htau htau1 hwindow (hb.trans hwindow)
  have hloss:=first_step_scalar_losses A r ell (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))
    (exponent Z k.2.1) eta pi em ed hA (hrF.trans hFA) (hellF.trans hFA) hacap.1 (hkcap 2).1 (hkcap 2).2
    (hkcap 4).2 ht.1 htcap heta heta1 hem hed hpi hetapi hsmall hsmall'
  have hYone:=first_live_cell_radius_one p hp hcop hg pool Q labels _ Z M r ell V eta tau β Ψ m mark W Φ K hlabels k hk
  have hW:∀y,W y≠0→y≤oldb*Z^r:=by
    intro y hy
    have hnon:om (y/Z^r)≠0:=by intro h;exact hy (by simp [W,normTwistedSource,h])
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
  have hcol:=original_live_column_scale p hp hcop hg pool Q labels _ β cutoff Ψ m mark W Φ K (Z^r) oldb
    (Real.rpow_pos_of_pos hz _) hW k hk
  have hXone:1≤X*Real.exp window:=by
    have hpos:0≤X:=Real.rpow_nonneg hz.le _
    apply le_trans _ (mul_le_mul_of_nonneg_left hold hpos)
    dsimp [X]
    rw [columnScale_physical Z r hZ]
    cases negative
    · exact hcol.2
    · exact hcol.1
  refine ⟨hYone,hXone,hscl.1,hscl.2.1,hscl.2.2.1,hscl.2.2.2.1,hscl.2.2.2.2.1,
    hscl.2.2.2.2.2.1,hloss.1,hloss.2,?_,?_,?_,?_⟩ <;> linarith [(hkcap 4).2,(hkcap 2).2]

end SevenEighths.InverseMoment

end

end OAI

end Source2747

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveActualStep.lean; sha256: e18473b8d737bf1882051daca5ed807d18a5cdd13faf4ac47c65c42fa52858f1 -/
section Source2748
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_label_step
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∃C Cbin Cz Ct:ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Cz ∧ 0≤Ct ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta t Kphysical:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree →
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) t (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      Cz*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ct*Z^(-saving):=by
  let cap:=3*F+16
  have hcap:0≤cap:=by dsimp [cap];linarith
  have hbig:0≤16*cap+20:=by positivity
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_label_cell_step om lo hi hlo hs negative
    window (16*cap+20) (16*cap+20) tau saving (hhib.trans hwindow) hbig hbig htau b hb ed hed (fun _=>0) (by intro i;norm_num) K em hem
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  refine ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta t Kphysical hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA cutoff W mark S k hk hchild
  have hZ1:1<Z:=by linarith
  have hz:0<Z:=by linarith
  obtain ⟨hY1,hX1,hcol,hYcap,hYi,hgeom,hphysical,hPcap,hbudget,hcost,hellcap,hactivecap,hcommoncap,hquotcap⟩:=
    original_live_step_scalars p hp hcop hg pool Q labels β Ψ m mark old Φ Kphysical Z M r ell V F eta tau theta oldb b window em ed pi
      hZ1 hbin hF hM hMF hr hrF hell hellF hV hVF heta heta1 htau.le htau1 hwin hold hwindow hem.le hed.le hpi hetapi
      hsmall hsmall' hQ hn hsold k hk negative
  apply hstep p hp hcop hg hpr hinj hc pool Q k.1 k.2.1 k.2.2 Ψ m slots lists weights
    Z M r ell V eta pi b (cap+1) (4*cap+2) epschild A t (fun _=>0)
    hZ heta hbin (by linarith) hQ hslots hcard hw hΨ (by intro i;simp) hhib le_rfl hb
  · exact (hwindow.trans hwin).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hA
  · exact hcol
  · exact hYi
  · exact hgeom
  · exact hphysical
  · exact hbudget
  · exact hcost
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYi.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hcol.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hPcap
  · exact hellcap
  · exact hactivecap
  · exact hcommoncap
  · exact hquotcap
  · exact hchild

end SevenEighths.InverseMoment

end

end OAI

end Source2748

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstSecondHeightCost.lean; sha256: f7ccb2312c0c6a201f678d239c91bc427c5e2ac542d68fe993046b7ddb527d1d -/
section Source2749
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstSecondHeightCost
open InverseMoment InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile

def firstDegree (degree : ℕ) : ℕ := 2*InverseClippingProfiles.momentOrder (2*degree)

def firstHeight (negative : Bool) (z : Frequency×(Fin 9→ℝ)) : ℝ :=
  profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)

lemma first_height_cost (degree : ℕ) (negative : Bool) (z : Frequency×(Fin 9→ℝ)) :
    (1+‖firstHeight negative z‖)^(firstDegree degree)≤
      tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := by
  cases negative
  · exact first_right_height_budget _ z
  · exact first_left_height_budget _ z

lemma first_weight_one_le (J : ℕ) (z : Frequency×(Fin 9→ℝ)) :
    1≤tripleHeight J z.1*coordinateHeight J z.2 := by
  simpa only [ambientWeight,tripleHeight,coordinateHeight] using ambientWeight_one_le J z

def stepBudget (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ) : ℝ :=
  Czero*Z^(F+17*eta+tau+pi)+
    C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)

lemma stepBudget_nonneg (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hA : 0≤A) (hZ : 0≤Z) :
    0≤stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving := by
  unfold stepBudget
  positivity

theorem second_step_first_height (degree : ℕ) (negative : Bool)
    (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hA : 0≤A) (hZ : 0≤Z)
    (z : Frequency×(Fin 9→ℝ)) :
    Czero*Z^(F+17*eta+tau+pi)+
      C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
        Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  have hw := first_weight_one_le (firstDegree degree) z
  have hh := first_height_cost degree negative z
  have hzero : Czero*Z^(F+17*eta+tau+pi)≤
      (Czero*Z^(F+17*eta+tau+pi))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have htail : Ctail*Z^(-saving)≤
      (Ctail*Z^(-saving))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have hmiddle := mul_le_mul_of_nonneg_left hh
    (show 0≤C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild) by positivity)
  have hs := add_le_add (add_le_add hzero hmiddle) htail
  convert hs using 1 <;> dsimp [stepBudget] <;> ring

lemma log_fourth_small_power (Cbin ε : ℝ) (hε : 0<ε) :
    ∃ Clog : ℝ,0<Clog ∧ ∀ Z : ℝ,2≤Z→
      (1+Cbin*Real.log Z)^4≤Clog*Z^ε := by
  obtain ⟨C,hC,he⟩ := log_eighth_small_power ε hε
  let b := 1+|Cbin|
  have hb : 0<b := by dsimp [b];positivity
  refine ⟨b^4*C,mul_pos (pow_pos hb _) hC,?_⟩
  intro Z hZ
  have hZ1 : 1≤Z := by linarith
  have hl : 0≤Real.log Z := Real.log_nonneg hZ1
  have hn : |1+Cbin*Real.log Z|≤b*(1+Real.log Z) := by
    calc
      _≤1+|Cbin| *Real.log Z := by simpa [abs_mul,abs_of_nonneg hl] using abs_add_le (1:ℝ) (Cbin*Real.log Z)
      _≤_ := by dsimp [b];nlinarith [abs_nonneg Cbin]
  calc
    _ = |1+Cbin*Real.log Z|^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    _ ≤ (b*(1+Real.log Z))^4 := pow_le_pow_left₀ (abs_nonneg _) hn 4
    _≤b^4*(1+Real.log Z)^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤1+Real.log Z) (by norm_num : 4≤8)) (by positivity)
    _≤b^4*(C*Z^ε) := mul_le_mul_of_nonneg_left (he Z hZ1) (by positivity)
    _=_ := by ring

theorem stepBudget_small_power (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving≤
        Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε) := by
  obtain ⟨Clog,hlog,hlogs⟩ := log_fourth_small_power Cbin ε hε
  refine ⟨1+Czero+C*Clog+Ctail,by positivity,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta hepschild hsaving
  have hZ1 : 1≤Z := by linarith
  have hZ0 : 0<Z := by linarith
  have h0 : Z^(F+17*eta+tau+pi)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have h1 : C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)≤
      C*A*Clog*Z^(F+48*eta+tau+pi+epschild+ε) := by
    calc
      _≤C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild) := by gcongr;exact hlogs Z hZ
      _=_ := by rw [show C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild)=
          C*A*Clog*(Z^ε*Z^(F+48*eta+tau+pi+epschild)) by ring,←Real.rpow_add hZ0];congr 1;congr 1;ring
  have h2 : Z^(-saving)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hsaving
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hz) h1)
    (mul_le_mul_of_nonneg_left h2 ht)
  unfold stepBudget
  apply hsum.trans
  have hpow : 0≤Z^(F+48*eta+tau+pi+epschild+ε) := Real.rpow_nonneg hZ0.le _
  have hcoef : Czero+C*A*Clog+Ctail≤(1+Czero+C*Clog+Ctail)*(1+A) := by
    have hza : 0≤Czero*A := mul_nonneg hz hA
    have hta : 0≤Ctail*A := mul_nonneg ht hA
    have hc : 0≤C*Clog := mul_nonneg hC hlog.le
    nlinarith
  convert mul_le_mul_of_nonneg_right hcoef hpow using 1 ; ring

theorem first_source_budget (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := stepBudget_small_power C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z
  exact (second_step_first_height degree negative C Cbin Czero Ctail A Z F eta tau pi epschild saving
    hC hz ht hA (by linarith) z).trans
    (mul_le_mul_of_nonneg_right (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving)
      (le_trans zero_le_one (first_weight_one_le _ z)))

theorem first_source_requested_loss (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving loss : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      48*eta+tau+pi+epschild+ε≤loss→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+loss))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := first_source_budget degree C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving loss hA hZ heta heps hsaving hloss negative z
  apply (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z).trans
  apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (first_weight_one_le _ z))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end SevenEighths.InverseMomentFirstSecondHeightCost
end

end OAI

end Source2749

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstLiveHeightStep.lean; sha256: 7263adc71acd4cfef17564601a073539272ead8bd9bf1348db560273a28f7dff -/
section Source2750
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_first_height
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∀eps:ℝ,0<eps → ∃C:ℝ,0<C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta Kphysical loss:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A → 0≤epschild → -saving≤r+3*ell+V+48*eta+tau+pi+epschild+eps →
      48*eta+tau+pi+epschild+eps≤loss →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree → ∀z:Frequency×(Fin 9 → ℝ),
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) (InverseMomentFirstSecondHeightCost.firstHeight negative z) (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      (C*(1+A)*Z^(r+3*ell+V+loss))*
        (tripleHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.1*
          coordinateHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.2) :=by
  obtain ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_live_label_step
    old oldb hsold om lo hi hlo hs negative F tau saving window b em ed hF htau hb hhib hwindow hold hem hed K
  refine ⟨w₁,w₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree eps heps
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  obtain ⟨Ctotal,hCtotal,hbudget⟩:=InverseMomentFirstSecondHeightCost.first_source_requested_loss degree C Cbin Cz Ct eps hC hCz hCt heps
  refine ⟨Ctotal,hCtotal,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta Kphysical loss hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA hechild hsave hloss cutoff W mark S k hk hchild z
  have he':=hstep p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta (InverseMomentFirstSecondHeightCost.firstHeight negative z) Kphysical
    hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1 hwin hpi hetapi hsmall hsmall'
    hQ hn hΨ hslots hcard hw hA k hk hchild
  exact he'.trans (hbudget A Z (r+3*ell+V) eta tau pi epschild saving loss hA hZ heta hechild hsave hloss negative z)

end SevenEighths.InverseMoment

end

end OAI

end Source2750

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstTwoPassEnergy.lean; sha256: 775695302b363da198a8b250943020cde01256412672654c337c8bb94f3c9901 -/
section Source2751
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_two_pass_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃C Czero Ctail:ℝ,0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
        C*Γ^2*(1+A)*Z^(r+3*ell+V+loss)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨om₁,om₂,lo,hi,hlo,hlh,hom₁,hom₂,hs₁,hs₂,hfull⟩:=original_dyadic_full_energy om a b ha hs Lcap Lcap eta tau saving hcap hcap hb heta heta1 htau htau1
  let bw:=max 1 (max hi b)
  have hbw:1≤bw:=le_max_left _ _
  have hbwb: b≤bw:=(le_max_right hi b).trans (le_max_right 1 _)
  have hbwh:hi≤bw:=(le_max_left hi b).trans (le_max_right 1 _)
  have hbwp:0<bw:=by linarith
  let window:=Real.log bw
  have hew:Real.exp window=bw:=Real.exp_log hbwp
  have hsold:∀y,om y≠0→y≤b:=fun y hy=>(hs hy).2
  obtain ⟨w₁₁,w₁₂,af₁,bf₁,haf₁,hab₁,hw₁₁,hw₁₂,hs₁₁,hs₁₂,hleft⟩:=actual_live_first_height
    om b hsold om₁ lo hi hlo (subset_closure.trans hs₁) true
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  obtain ⟨w₂₁,w₂₂,af₂,bf₂,haf₂,hab₂,hw₂₁,hw₂₂,hs₂₁,hs₂₂,hright⟩:=actual_live_first_height
    om b hsold om₂ lo hi hlo (subset_closure.trans hs₂) false
    Lcap tau saving window bw em ed hcap htau hbw hbwh hew.ge (hbwb.trans hew.ge) hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew.symm,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cf,Cz,Ct,hCf,hCz,hCt,hfull⟩:=hfull epsFirst hepsF (firstDegree degree)
  obtain ⟨Cl,hCl,hleft⟩:=hleft degree epsSecond hepsS
  obtain ⟨Cr,hCr,hright⟩:=hright degree epsSecond hepsS
  refine ⟨Cf*(Cl+Cr),Cz,Ct,mul_nonneg hCf (by positivity),hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hΨ hΓ hA hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hl hr'
  let Be:ℝ:=(Cl+Cr)*(1+A)*Z^(r+3*ell+V+loss)
  have hz:0<Z:=by linarith
  have hBe:0≤Be:=by dsimp[Be];positivity
  have left : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights om₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hleft p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hl k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    apply he.trans
    change (Cl*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have right : ∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights om₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Be*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
    intro k hk z
    have he:=hright p hp hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights rowMajorant
      Z M r ell V eta pi epschild A theta (Z^M) loss hZ hbin hM hMcap hr hrcap hell hellcap hV hVcap
      heta heta1 htau1 hwin hpi hpieta hemcost hedcost hQ hn hΨ hslots hcard hweights hA hechild hsave hloss k hk (hr' k hk) z
    rw [columnScale_physical Z r (by linarith)] at he
    apply he.trans
    change (Cr*(1+A)*Z^(r+3*ell+V+loss))*_ ≤ Be*_
    have hwgt:0≤tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := le_trans zero_le_one (first_weight_one_le _ z)
    dsimp[Be]
    gcongr
    linarith
  have hall:=hfull p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Be
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hBe hsf hn hβ hlabels hslots hweights left right
  convert hall using 1 ; dsimp[Be] ; ring

end SevenEighths.InverseMoment

end

end OAI

end Source2751

/- Original source: OAI/NumberTheory/DirichletL/Descent/TwoPassScalar.lean; sha256: fe0e9308d31f6461cfc34a6bfbf9aa834de64d0cabbc2a2959c9e1a5b6373e07 -/
section Source2752
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment

theorem two_pass_scalar (C Cz Ct Γ A Z F M r ell eta tau _pi epsFirst loss Lcap saving lossFinal H:ℝ)
    (hC:0≤C)(hCz:0≤Cz)(hCt:0≤Ct)(hA:0≤A)(hZ:1≤Z)(hH:1≤H)
    (hM:M-ell≤F)
    (hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
    (hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
    (htail: -saving≤F+lossFinal):
    Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
      C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ct*Γ^2*Z^(-saving)≤
    (C+Cz+Ct)*Γ^2*(1+A)*H*Z^(F+lossFinal) :=by
  have hz:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  have hP:=Real.rpow_le_rpow_of_exponent_le hZ (show M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta)≤F+lossFinal by linarith)
  have hT:=Real.rpow_le_rpow_of_exponent_le hZ htail
  have hR:=Real.rpow_le_rpow_of_exponent_le hZ (show F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤F+lossFinal by linarith)
  have hlarge:1≤(1+A)*H:=one_le_mul_of_one_le_of_one_le (by linarith) hH
  have hp:Cz*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))≤Cz*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hP (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Cz*Γ^2 by positivity)
  have ht:Ct*Γ^2*Z^(-saving)≤Ct*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    apply (mul_le_mul_of_nonneg_left hT (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using mul_le_mul_of_nonneg_left hlarge (show 0≤Ct*Γ^2 by positivity)
  have hr:C*Γ^2*(1+A)*Z^(F+loss)*H*Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)≤
      C*Γ^2*((1+A)*H)*Z^(F+lossFinal):=by
    calc
      _=C*Γ^2*((1+A)*H)*Z^(F+loss+((2*Lcap+15*eta+tau)*epsFirst+epsFirst)):=by simp only [Real.rpow_add hz];ring
      _≤_:=mul_le_mul_of_nonneg_left hR (by positivity)
  nlinarith [add_le_add (add_le_add hp hr) ht]

end SevenEighths.InverseMoment

end

end OAI

end Source2752

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstTwoPassParentEnergy.lean; sha256: f0d585072db5d67f559b34d4dce4405a9414ab9c177d0307b6a49bb09b683cb0 -/
section Source2753
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_two_pass_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃C:ℝ,0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hparent:M-ell≤r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
      (_htail: -saving≤r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*Γ^2*(1+A)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) :=by
  obtain ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,he⟩:=
    original_two_pass_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨C,Cz,Ct,hC,hCz,hCt,he⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨C+Cz+Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hΓ hA hsf hn hβ hlabels hslots hweights mark Y cutoff W source keys hl hr'
  have hall:=he p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hΨ hΓ hA hsf hn hβ hlabels hslots hweights hl hr'
  exact hall.trans (two_pass_scalar C Cz Ct Γ A Z (r+3*ell+V) M r ell eta tau pi epsFirst loss Lcap saving lossFinal
    ((1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))) hC hCz hCt hA (by linarith)
    (one_le_pow₀ (by linarith [norm_nonneg theta])) hparent hprincipal hretained htail)

end SevenEighths.InverseMoment

end

end OAI

end Source2753

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongParent.lean; sha256: ff61d37040b306591f11c0f04db2a5f2f83006b35129ef88edcf27024977b504 -/
section Source2754
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_long_parent_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ pi epschild A loss lossFinal:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hbinExp:Real.exp 1≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖eisEmbedding (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*Z^ell)
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hparent:M-ell≤r+3*ell+V)
      (_hprincipal:3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal)
      (_hretained:loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal)
      (_htail: -saving≤r+3*ell+V+lossFinal)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    original_two_pass_parent_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform epsFirst hepsF
  obtain ⟨C,hC,hfull⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ pi epschild A loss lossFinal hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤Ccoef*(Real.exp 1*Z^ell)^epsFirst := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^epsFirst) ξ pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ (by positivity) hA hsf hn hβ hlabels hslots hweights hleft hright

end SevenEighths.InverseMoment

end

end OAI

end Source2754

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongKeys.lean; sha256: 1feb0598d438cd92630ba23fb09de6d1ff2da39189967778a50c57063bd040fd -/
section Source2755
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks
open InverseMomentFirstOriginalProfile CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Ψ:O→*ℂ)(m mCoef:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=>primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=>normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels)
    (fun x=>x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hcop hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))

end SevenEighths.InverseMoment

end

end OAI

end Source2755

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongUniformTestBin.lean; sha256: 479a3c21e48491e5eafa1d1ad5ec07729fadf8cdddfaceee070f8cb7aec6428e -/
section Source2756
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_uniform_test
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀(test:ℝ → ℂ)(hs₀:Function.support test⊆Set.Icc a₀ b₀)(hTest:ContDiff ℝ ∞ test),
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          test (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^(InverseClippingProfiles.momentOrder (firstDegree degree)))^2 := by
  let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox
  have hs:Function.support om⊆Set.Icc (Real.exp (-Alog)) (Real.exp Alog):=
    fun x hx=>radialFromLog_support Vlog (Vlog.smooth ⊤) Alog hbox x hx
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_long_parent_energy om (Real.exp (-Alog)) (Real.exp Alog) (Real.exp_pos _) hs
      Lcap eta tau saving em ed hcap (Real.exp_pos _).le heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hparent⟩:=he epsFirst epsSecond hepsF hepsS degree
  let d:=InverseClippingProfiles.momentOrder (firstDegree degree)
  refine ⟨Ccoef,C,hCcoef,hC,?_⟩
  intro test hs₀ hTest
  let moment:ℝ:=∫ξ:ℝ,‖reopeningCoefficient test a₀ b₀ ha₀ hs₀ hTest ξ‖*(1+|ξ|)^d
  intro σ _ S D hbad hSp
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0<Z:=by linarith
  have hg' : ∀i:primePool F,goodLambda∉Ideal.span {poolPrimary F i}:=poolPrimary_good F hF
  have hinj:Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j hij
    exact Subtype.ext (by simpa only [poolPrimary_span F hF] using hij)
  have hpr (i:primePool F):goodLambda^2∣poolPrimary F i-1:=
    (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  let Gamma:=Ccoef*(Real.exp 1*Z^ell)^epsFirst
  let E:=C*Gamma^2*(1+A)*Z^(r+3*ell+V+lossFinal)
  have hE:0≤E:=by dsimp [E];positivity
  refine (actual_long_bin_normalized_energy S D hbad hSp Q labels Ψ m test a₀ b₀ ha₀ hb₀ hs₀ hTest
    Vlog hone Z r ell V H₀ (Z^M) E d hz hD (Real.rpow_pos_of_pos hz _) hE hQlo hQhi slots lists weights ?_).trans_eq ?_
  · intro ξ
    have hbnd:=hparent (poolPrimary F) (poolPrimary_ne_zero F hF) hg' hinj
      (poolPrimary_coprime F hF) (poolPrimary_odd F hF) hpr Finset.univ Q labels Ψ m (m*excludedGenerator S)
      slots lists weights Z M r ell V H₀ ξ pi epschild A loss lossFinal
      hZ hbin hbinExp hM hFcap hMcap hell hV hr hbZ (fun _ _=>Finset.subset_univ _)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQlo v hv)
      (by intro v hv;rw [cubeIdeal_primeProduct_norm F hF];exact hQhi v hv)
      hrcap hellcap hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
      hΨ hA hsf hn hlabels hslots hweights (hleft ξ) (hright ξ)
    have hc (I:Ideal O) := funext (actualLongCoefficient_complete S D hbad Ψ m H₀ (Z^ell) ξ I)
    have hrow: (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist Vlog ξ (columnLog (poolPrimary F) (Z^r) T)) z)=
      (fun I z=>varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q
        (separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v))
          (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) (Z^ell) ξ) Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ (primeProductNorm (poolPrimary F) T/Z^r)) z) := by
      funext I z
      exact long_marked_source_eq (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        hg' Finset.univ Q _ Ψ m (idealGenerator I) z slots lists weights Vlog Alog hbox Z r ξ hz
    rw [hrow]
    convert hbnd using 1
    · apply congrArg (fun f => Z^(-r-2*ell-V)*rowFamilyEnergy labels f (Z^M))
      funext I z
      exact congrArg (fun coeff => varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) hg' Finset.univ Q coeff Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (v.support∪T)*normTwistedSource om ξ
          (primeProductNorm (poolPrimary F) T/Z^r)) z) (hc I).symm
    · dsimp [E,Gamma,d]
      try simp only [Real.norm_eq_abs]
      ring
  · dsimp [E,Gamma,moment]

end SevenEighths.InverseMoment

end

end OAI

end Source2756

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalReopeningHeight.lean; sha256: 1de7cd1f92e4b6f35b7fe6cefe0d25d94dc4caf0b9e4fa4958296584ef9a2d23 -/
section Source2757
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseMoment
open MeasureTheory CanonicalCubeSeparation FourierBridge JointLogSeparation CompletedHeight

theorem reopening_coefficient_twist (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(theta:ℝ)
    (hT:ContDiff ℝ ∞ (normTwistedSource W theta)):
    reopeningCoefficient (normTwistedSource W theta) a b ha
      ((normTwistedSource_support W theta).trans hs) hT=
      𝓕 (frequencyTwist (sourceLogProfile W a b ha hs hW) theta) :=by
  unfold reopeningCoefficient
  congr 1
  ext x
  simp only [sourceLogProfile_apply,frequencyTwist_apply,normTwistedSource,Real.log_exp]

theorem reopening_twisted_moment (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)≤
      C*(1+‖theta‖)^(J+(volume:Measure ℝ).integrablePower) :=by
  obtain ⟨C,hC,he⟩:=frequencyTwist_fourier_moment J (sourceLogProfile W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro theta hT
  rw [reopening_coefficient_twist W a b ha hs hW theta hT]
  simpa only [Real.norm_eq_abs,mul_comm] using he theta

theorem reopening_twisted_moment_squared (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)^2≤
      C*(1+‖theta‖)^(2*(J+(volume:Measure ℝ).integrablePower)) :=by
  obtain ⟨C,hC,he⟩:=reopening_twisted_moment W a b ha hs hW J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro theta hT
  have hh:=pow_le_pow_left₀ (integral_nonneg (fun ξ=>by positivity)) (he theta hT) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm] using hh

end SevenEighths.InverseMoment

end

end OAI

end Source2757

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLongHeightBin.lean; sha256: 4505799fe12caa98d75d55145c77218381b8e911952828ba1716e7c9443cbe35 -/
section Source2758
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_height
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (W:ℝ→ℂ)(hsW:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀theta:ℝ,
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          (normTwistedSource W theta) (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,he⟩:=
    actual_marked_bin_uniform_test a₀ b₀ ha₀ hb₀ Vlog Alog hbox hone
      Lcap eta tau saving em ed hcap heta heta1 htau htau1 hem hed K
  refine ⟨ω₁₁,ω₁₂,ω₂₁,ω₂₂,af₁,bf₁,af₂,bf₂,window,bw,
    haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hbwexp,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Ccoef,C,hCcoef,hC,hbin⟩:=he epsFirst epsSecond hepsF hepsS degree
  obtain ⟨Cm,hCm,hmoment⟩:=reopening_twisted_moment_squared W a₀ b₀ ha₀ hsW hW
    (InverseClippingProfiles.momentOrder (firstDegree degree))
  refine ⟨Ccoef,C*Cm,hCcoef,mul_nonneg hC hCm,?_⟩
  intro theta σ _ S D hbad hSp
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  intro Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hT:=CanonicalRowCompletion.normTwistedSource_contDiff W a₀ b₀ ha₀ hsW hW theta
  have hsT:Function.support (normTwistedSource W theta)⊆Set.Icc a₀ b₀:=
    (normTwistedSource_support W theta).trans hsW
  have hbnd:=hbin (normTwistedSource W theta) hsT hT S D hbad hSp
    Q labels Ψ m slots lists weights Z M r ell V H₀ pi epschild A loss lossFinal
    hZ hbins hbinExp hM hFcap hMcap hell hV hr hbZ hQlo hQhi hrcap hellcap hVcap hwin
    hpi hpieta hemcost hedcost hechild hsave hloss hcard hpar hprincipal hretained htail
    hΨ hA hsf hn hlabels hslots hweights hD hleft hright
  have hz:0<Z:=by linarith
  apply hbnd.trans
  calc
    _ ≤ C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
        (Cm*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+
          (volume:Measure ℝ).integrablePower))) :=
      mul_le_mul_of_nonneg_left (hmoment theta hT) (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMoment

end

end OAI

end Source2758

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteChildren.lean; sha256: 0d88225620a5602a345e3acad3f64721b57cb22eb8f8f4936217fd7bcbb83722 -/
section Source2759
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_state_from_children
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤cstar/100000)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(heps:0<eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0<Cs ∧ 0≤Cb ∧ 1<Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤Z → 2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 1≤eta*Real.log Z →
      0≤N → 0≤V → 0≤M → N+V≤L → M≤N+V → z₀≤L →
      hi≤Z^eta → Real.exp Alog≤Z^eta → Real.exp window≤Z^eta →
      0≤cutoff → cutoff≤L → cutoff≤cstar/200 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      0≤pi → 6*eta≤pi → em*(20*(3*L+16)+30)≤pi/4 → ed*(20*(3*L+16)+30)≤pi/4 →
      0≤epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤loss →
      3*eta+epsFirst*(2*L+7*eta)≤lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤lossFinal →
      0≤A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤K →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(Ψ:O→*ℂ),(∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists a ω₁₁ ω₁₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      (∀j∈cubeLogRange hi (Z^N),
        let ell:=actualCubeLength Z j;
        let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j);
        Q.Nonempty → ∀ξ:ℝ,∀k∈actualLongSourceKeys (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists a om Z M (N-3*ell) ell V (Z^(cutoff-V)) ξ L eta tau,
          ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists a ω₂₁ ω₂₂
            Z M (N-3*ell) ell V eta tau window bw epschild A K degree) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  have hL0:0≤L:=by linarith
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hbin⟩:=
    actual_marked_bin_height lo hi hlo hhi W hsW hW Vlog Alog hbox hone L eta tau saving em ed
      hL0 heta.le heta1 htau htau1 hem hed K
  obtain ⟨ds,hstate⟩:=actual_complete_state_from_live_bins lo hi hlo hhi W hsW hW L cstar eta eps
    hL0 hcstar heta heta1 hetac heps K K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Ccoef,C,hcoef,hC,hbin⟩:=hbin epsFirst epsSecond heF heS degree
  obtain ⟨Cs,Z₀,hCs,hZ₀,hstate⟩:=hstate q hq
  let Cb:=C*Ccoef^2*Real.exp (2*epsFirst)
  refine ⟨Cs,Cs*Cb,Z₀,hCs,by dsimp [Cb];positivity,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hmN hmargin hreserve
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod a ha
  dsimp only
  intro hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1≤Z:=by linarith
  let d:=2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)
  let E:=Cb*(1+A)*Z^(N+V+lossFinal+2*L*epsFirst)*(1+‖theta‖)^d
  have hE:0≤E:=by dsimp [E,Cb];positivity
  have hbins:∀j∈cubeLogRange hi (Z^N),
      (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
        (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j)).Nonempty →
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin (reflectionExcludedPrimes q) D
        (progressingCubes (reflectionExcludedPrimes q) D (Z^(cutoff-V))
          (activeCubeLogBin (reflectionExcludedPrimes q) D hi (Z^N) j))
        Ψ m (idealGenerator I) z (normTwistedSource W theta) (Z^N) (Z^(cutoff-V)) slots lists a) (Z^M)≤E := by
    intro j hj hne
    let ell:=actualCubeLength Z j
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    have hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D hi (Z^N) j)
    obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D (reflectionExcludedPrimes_bad q)
      hi Z N V cutoff eta L j (by linarith) hL heta1 hV hFcap hbZ hlog hne
    have hsN:(N-3*ell)+3*ell=N:=by ring
    have hpr:3*eta+epsFirst*(5*ell+2*(N-3*ell)+7*eta)≤lossFinal:=by
      have hNL:N≤L:=by linarith
      nlinarith
    have hh:=hbin theta S D (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
      Q labels Ψ m slots lists a Z M (N-3*ell) ell V (Z^(cutoff-V)) pi epschild A loss lossFinal
      hZ2 h2 hExp hM hFL (by linarith) hel hV hr hAZ
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).1)
      (by intro v hv;rw [←cubeIdeal_primeProduct_norm F hF];exact (hqn v hv).2)
      hrL helL (by linarith) hwin hpi hpieta hemc hedc hechild (by linarith) hloss hcard
      (by linarith) hpr hretained (by linarith) hΨ hA
      (fun I hI=>(hlabels I hI).2.1) (fun I hI=>(hlabels I hI).1.1)
      (fun I hI=>((hlabels I hI).2.2).trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)))
      hdis ha (by simpa only [hsN] using hD) (hleft j hj hne) (hright j hj hne)
    rw [hsN] at hh
    apply hh.trans
    have hc:=mul_le_mul_of_nonneg_right
      (actual_long_uniform_parent_cost Z ell N V L epsFirst Ccoef C A lossFinal hZ1 helL heF.le hC hA)
      (show 0≤(1+‖theta‖)^d by positivity)
    simpa only [hsN] using hc
  have hs:=hstate m hm Z N V M z₀ margin cutoff hZ hN (by linarith) hV (by linarith) hM (by linarith)
    hzcap hcut hcutL hcutc hmN hmargin hreserve labels hlabels D hD slots hcard lists H
    hdis hH1 hH hprod Ψ hΨ hperiod theta a ha E hE hbins
  apply hs.trans_eq
  dsimp [E,d]
  rw [Real.rpow_add hz (N+V+lossFinal+2*L*epsFirst) eps]
  ring

end SevenEighths.InverseMoment

end

end OAI

end Source2759
