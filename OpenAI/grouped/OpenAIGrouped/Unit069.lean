import OpenAIGrouped.Unit066
import OpenAIGrouped.Unit068
import OpenAIGrouped.Unit065
import OpenAIGrouped.Unit058
import OpenAIGrouped.Unit067
import OpenAIGrouped.Unit063
import OpenAIGrouped.Unit007
import OpenAIGrouped.Unit060
import OpenAIGrouped.Unit059
import OpenAIGrouped.Unit015

set_option autoImplicit false
set_option maxHeartbeats 3000000

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankMonotone.lean; sha256: a489c2809a516cf7f089d35b3d5c0d8e52e7135782577e5289e5d350d220ce1b -/
section Source2760
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s

omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤A)(hAB:A≤B)(hJ:degree≤J)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity

end SevenEighths.InverseMoment

end

end OAI

end Source2760

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankCapChildren.lean; sha256: 53b6facef29b0726ef44cbc07e9bae682009f5f55f5e1f970580cf826c3a59ea -/
section Source2761
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_rank_cap_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A Mnext Fnext cnext:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hMc:M-3*cutoff/2≤Mnext)(hFc:r+3*ell+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  exact canonical_rank_moments_children p hp hcop hg hc hpr pool Q k l j negative base Ψ hΨ m hm
    slots lists a ω₁ ω₂ Z M r ell V eta tau window b cutoff Qwidth z c eps A K degree
    hZ heta hbin hell hV hb hbt hwindow hd hterminal hsmall hparent hpuncture hQ
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₁ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₁)
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₂ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₂)

theorem canonical_depth_ceilings (n:ℕ)(cutoff Fbase cbase eta:ℝ)(M F c:ℝ)
    (hM:M≤3*(n:ℝ)*cutoff/2)(hF:F≤Fbase-15*(n:ℝ)*eta)
    (hc:cbase+7*((n:ℝ)+1)*eta≤c):
    M-3*cutoff/2≤3*((n:ℝ)-1)*cutoff/2 ∧
    F+15*eta≤Fbase-15*((n:ℝ)-1)*eta ∧
    cbase+7*(n:ℝ)*eta≤c-7*eta :=by
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI

end Source2761

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLiveBinRank.lean; sha256: 9cb8ae76f7730676eb36f89757f698d9560dd0facc3b06ec8a29f088d3ac1ba3 -/
section Source2762
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_bin_rank_children
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:0≤eta)(heta1:eta≤1)
    (hcut:0<cutoff)(hsmall:eta≤cutoff/32)(hV:0≤V)(hparentcap:N+V≤L)
    (hbW:bW≤Z^eta)(hlog:1≤eta*Real.log Z)(hexp:Real.exp 1≤Z^eta)
    (hbin:2≤Z^eta)(hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤Mnext)(hFc:N+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree :=by
  dsimp only
  intro h₁ h₂ k l jj negative
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D hbad bW Z N V cutoff eta L j
    hZ hL heta1 hV hparentcap hbW hlog hne
  have hs:(N-3*actualCubeLength Z j)+3*actualCubeLength Z j+V=N+V:=by ring
  apply canonical_rank_cap_children (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun i=>(primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2)
    Finset.univ _ k l jj negative base Ψ hΨ m hm slots lists a ω₁ ω₂
    Z M _ _ V eta tau window b (cutoff/2) Qwidth z c eps A Mnext Fnext cnext K degree
    hZ heta hbin hel hV hb hbt hwindow (by linarith) (by linarith) (by linarith)
    (by simpa only [hs] using hparent) hpuncture ?_ hMc (by simpa only [hs] using hFc) hcc h₁ h₂
  intro v hv
  apply (hqn v hv).2.trans
  calc
    _≤Z^eta*Z^(actualCubeLength Z j):=mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (by linarith) _)
    _=Z^(actualCubeLength Z j+eta):=by rw [Real.rpow_add (by linarith : 0<Z)];ring

end SevenEighths.InverseMoment

end

end OAI

end Source2762

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteRank.lean; sha256: 0e6b857c3026740defe71aeedb098831b8b276acb49faece3c0e9bc79e7c914d -/
section Source2763
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_state_from_rank_moments
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
      0<cutoff → cutoff≤L → cutoff≤cstar/200 → eta≤cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) →
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
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_state_from_children lo hi hlo hhi W hsW hW Vlog Alog hbox hone
      L cstar eta tau saving em ed eps hL hcstar heta heta1 hetac htau htau1 hem hed heps K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,hstep⟩:=hstep epsFirst epsSecond heF heS degree q hq
  refine ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha
  dsimp only
  intro h11 h12 h21 h22
  apply hstep m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut.le hcutL hcutc hmN hmargin hreserve
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod Ψ hΨ hperiod a ha
  · intro j hj
    dsimp only
    intro hne ξ k hk
    exact actual_live_bin_rank_children (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
      Z N V M cutoff eta L bw window hi (normWidth Z (Ideal.span {m})) z₀ margin epschild A
      (M-3*(cutoff/2)/2) (N+V+15*eta) (margin-7*eta) tau
      j (by linarith) hL heta.le heta1 hcut hsmall hV hFcap hbZ hlog hExp h2 hbw
      (by rw [hbexp]; exact hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))
      (hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))) hne
      base Ψ hbase m hm hmargin hpuncture le_rfl le_rfl le_rfl slots lists a w11 w12 K degree h11 h12 k.1 k.2.1 k.2.2 true

  · intro j hj
    dsimp only
    intro hne ξ k hk
    exact actual_live_bin_rank_children (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
      Z N V M cutoff eta L bw window hi (normWidth Z (Ideal.span {m})) z₀ margin epschild A
      (M-3*(cutoff/2)/2) (N+V+15*eta) (margin-7*eta) tau
      j (by linarith) hL heta.le heta1 hcut hsmall hV hFcap hbZ hlog hExp h2 hbw
      (by rw [hbexp]; exact hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))
      (hwin.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))) hne
      base Ψ hbase m hm hmargin hpuncture le_rfl le_rfl le_rfl slots lists a w21 w22 K degree h21 h22 k.1 k.2.1 k.2.2 false

end SevenEighths.InverseMoment

end

end OAI

end Source2763

/- Original source: OAI/NumberTheory/DirichletL/Descent/ActualChildStatePuncture.lean; sha256: 251dfa71388ea2acaf2e8baf9c2b7dcd73a9e181a62014c99a9d8e6ab33f6c73 -/
section Source2764
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseSecondFibers CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma actual_inherited_puncture_dvd (m : O) (γ : OuterTriple) :
    m∣actualSecondInheritedPuncture m γ := by
  refine ⟨ConcretePrimeRowBridge.idealGenerator γ.quotient*primaryGenerator γ.q0*
    primaryGenerator γ.residual,?_⟩
  unfold actualSecondInheritedPuncture actualSecondPuncture
  ring

lemma actual_inherited_radical_puncture_span (m : O) (γ : OuterTriple) :
    Ideal.span {actualSecondInheritedRadicalPuncture m γ}=
      (Ideal.span {actualSecondInheritedPuncture m γ}:Ideal O).radical :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma actual_inherited_radical_preserves_support (m : O) (γ : OuterTriple) :
    (Ideal.span {m}:Ideal O).radical∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.dvd_iff_le]
  apply Ideal.radical_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact actual_inherited_puncture_dvd m γ

lemma actual_inherited_radical_preserves_fixed (m : O) (γ : OuterTriple) (Q : Ideal O)
    (hQ : Q.radical=Q) (hparent : Q∣Ideal.span {m}) :
    Q∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  apply dvd_trans _ (actual_inherited_radical_preserves_support m γ)
  rw [Ideal.dvd_iff_le,←hQ]
  exact Ideal.radical_mono (Ideal.dvd_iff_le.mp hparent)

lemma actual_inherited_radical_is_radical (m : O) (γ : OuterTriple) :
    (Ideal.span {actualSecondInheritedRadicalPuncture m γ}:Ideal O).radical=
      Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.radical_idem]

end SevenEighths.InverseMoment
end

end OAI

end Source2764

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalPunctureMask.lean; sha256: a4b8a01c507243d5b479f78673f4f88c280f0a618625eac8184d96fd51d1194a -/
section Source2765
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve
open InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section General
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
theorem rowCoprimeMask_redundant_mul (S : Finset ι) (m c : Eis)
    (hc : ∀ i∈S,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (m*c)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) S m := by
  have he : (∃i∈S,m*c∈Ideal.span {p i}) ↔ ∃i∈S,m∈Ideal.span {p i} := by
    constructor
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,((inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hm).elim id (hc i hi)⟩
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,Ideal.mul_mem_right _ _ hm⟩
  simp only [rowCoprimeMask,he]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c f k : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ (m*c) f k slots lists a W X=
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  have hm := rowCoprimeMask_redundant_mul p S m c
    (fun i hi=>hc i (Finset.mem_powerset.mp hS hi))
  simp only [secondChildColumn,hm]

omit [DecidableEq σ] in
theorem normalizedColumnEnergy_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z F : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    normalizedColumnEnergy p hp hcop hg pool Ψ (m*c) slots lists a labels rows D W X Z F=
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F := by
  simp only [normalizedColumnEnergy,finiteCanonicalMarkedRow_redundant_puncture
    p hp hcop hg pool Ψ m c _ _ slots lists a W X hc]

omit [DecidableEq ι] in
theorem puncture_mem_of_radical_dvd (m c : Eis)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣(Ideal.span {m}:Ideal Eis).radical)
    (i : ι) (hi : c∈Ideal.span {p i}) : m∈Ideal.span {p i} := by
  rw [←Ideal.span_singleton_le_iff_mem]
  apply Ideal.le_radical.trans
  apply (Ideal.dvd_iff_le.mp hc).trans
  exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.mpr
    (by rwa [Ideal.span_singleton_le_iff_mem])

omit [DecidableEq ι] in
theorem inherited_puncture_redundant_mem (m c : Eis)
    (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (i : ι) (hi : c∈Ideal.span {p i}) :
    actualSecondInheritedRadicalPuncture m γ∈Ideal.span {p i} := by
  have hd := actual_inherited_radical_preserves_fixed m γ (Ideal.span {c}).radical
    (Ideal.radical_idem _) hc
  apply puncture_mem_of_radical_dvd p _ c _ i hi
  rw [actual_inherited_radical_is_radical]
  exact hd

end General

theorem outside_pool_redundant_puncture {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) f k slots lists a W X=
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ m f k slots lists a W X := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply finiteCanonicalMarkedRow_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

end SevenEighths.InverseMoment
end

end OAI

end Source2765

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalPunctureMaskEnergy.lean; sha256: 7a7c8c090d9e3aec46cded9e2f1618d5c876fc1cb63cbfe0de311d1e61161cc8 -/
section Source2766
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

theorem outside_pool_redundant_energy {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply normalizedColumnEnergy_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span F hF i] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

theorem reflection_pool_mask_energy {σ : Type*} [DecidableEq σ]
    (q D : ℕ)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (ActualFiber.maskElement q m) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp :=
  outside_pool_redundant_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
    pool Ψ m slots lists a labels rows weight W X Z Fexp

theorem inherited_radical_mask_energy {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ : Eis→*ℂ) (m c : Eis) (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ*c) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ) slots lists a labels rows weight W X Z Fexp :=
  normalizedColumnEnergy_redundant_puncture p hp hcop hg pool Ψ _ c
    slots lists a labels rows weight W X Z Fexp
    (fun i _=>inherited_puncture_redundant_mem p m c γ hc i)

end SevenEighths.InverseMoment
end

end OAI

end Source2766

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteNormalized.lean; sha256: 938a23be99533e549dfbb01dfb5a00e01b31541e2fee3ac0c03746cbc53e6ae1 -/
section Source2767
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem normalizedColumnEnergy_eq_generator_sum {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z F R:ℝ)(hZ:0<Z) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z F=
    Z^(-F)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2) := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  ring

theorem outside_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) k slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  exact (normalizedColumnEnergy_eq_generator_sum (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (hlabels I hI)) weight W X Z Fexp R hZ).symm

theorem reflection_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (q D:ℕ)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) k
        slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ
      (ActualFiber.maskElement q m) slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  have h:=outside_complete_normalized_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) Ψ m slots lists a labels hlabels weight W X Z Fexp R hZ
  exact h.trans (reflection_pool_mask_energy q D Finset.univ Ψ m slots lists a labels
    (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp).symm

end SevenEighths.InverseMoment

end

end OAI

end Source2767

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteRankNormalized.lean; sha256: 32bfc9336cc9d9fbdd216deed44ef328d945fa61f0aea540b993bafa91d7909d -/
section Source2768
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open InverseInitialClippedColumns FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_normalized_rank_step
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
      0<cutoff → cutoff≤L → cutoff≤cstar/200 → eta≤cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) →
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
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (normTwistedSource W theta)
        (Z^N) Z (N+V)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_state_from_rank_moments lo hi hlo hhi W hsW hW Vlog Alog hbox hone
      L cstar eta tau saving em ed eps hL hcstar heta heta1 hetac htau htau1 hem hed heps K
  refine ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,?_⟩
  intro epsFirst epsSecond heF heS degree q hq
  obtain ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,hstep⟩:=hstep epsFirst epsSecond heF heS degree q hq
  refine ⟨Cs,Cb,Z₀,hCs,hCb,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha
  dsimp only
  intro h11 h12 h21 h22
  have hh:=hstep m hm Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta hZ hZ2 h2 hExp hlog
    hN hV hM hFcap hMF hzcap hbZ hAZ hwin hcut hcutL hcutc hsmall hmN hmargin hreserve hpuncture
    hpi hpieta hemc hedc hechild hsave hloss hprincipal hretained htail hA
    labels hlabels D hD slots hcard lists H hdis hH1 hH hprod base Ψ hbase hΨ hperiod a ha h11 h12 h21 h22
  rw [outside_complete_normalized_energy (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
    Ψ m slots lists a labels (fun I hI=>(hlabels I hI).1) (secondLabelWeight K)
    (normTwistedSource W theta) (Z^N) Z (N+V) (Z^M) (by linarith)] at hh
  exact hh

end SevenEighths.InverseMoment

end

end OAI

end Source2768

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalLowerMoments.lean; sha256: 0765eab6c717bd7f07edb71ec69b9fa6861bb749ec7a90e055102a400cdf06e5 -/
section Source2769
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalLowerMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M<Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

include hp in
theorem canonical_lower_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalLowerMoments p hp hcop hg pool base slots lists a ω₁ Z M (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalLowerMoments p hp hcop hg pool base slots lists a ω₂ Z M (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI

end Source2769

/- Original source: OAI/NumberTheory/DirichletL/Descent/FirstTwoPassLowerRank.lean; sha256: d9ea644b7f8ce03b4bab7c94a49d180a199670b53a4b6497b521c219be656392 -/
section Source2770
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

theorem original_two_pass_from_lower_moments
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
      (β:Ideal O→(ι→₀ℕ)→ℂ)(base Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss lossFinal delta Qwidth z c:ℝ)
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
      (_hbase:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(_hm:m≠0)
      (_hd:0<delta)(_hterminal:delta≤ell+V)(_hsmall:eta≤delta/16)
      (_hmargin:CanonicalMargins (r+3*ell+V) M Qwidth z c)
      (_hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let _keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      CanonicalLowerMoments p hp hcop hg pool base slots lists weights ω₁₁ Z M (r+3*ell+V+15*eta) z (c-7*eta) epschild A K degree→
      CanonicalLowerMoments p hp hcop hg pool base slots lists weights ω₁₂ Z M (r+3*ell+V+15*eta) z (c-7*eta) epschild A K degree→
      CanonicalLowerMoments p hp hcop hg pool base slots lists weights ω₂₁ Z M (r+3*ell+V+15*eta) z (c-7*eta) epschild A K degree→
      CanonicalLowerMoments p hp hcop hg pool base slots lists weights ω₂₂ Z M (r+3*ell+V+15*eta) z (c-7*eta) epschild A K degree→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        C*Γ^2*(1+A)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^(r+3*ell+V+lossFinal) :=by
  obtain ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,he⟩:=
    original_two_pass_parent_energy om a b ha hs Lcap eta tau saving em ed hcap hb heta heta1 htau htau1 hem hed K
  refine ⟨w₁₁,w₁₂,w₂₁,w₂₂,af₁,bf₁,af₂,bf₂,window,bw,haf₁,hab₁,haf₂,hab₂,hw₁₁,hw₁₂,hw₂₁,hw₂₂,hs₁₁,hs₁₂,hs₂₁,hs₂₂,hbw,hbwb,hew,?_⟩
  intro epsFirst epsSecond hepsF hepsS degree
  obtain ⟨C,hC,he⟩:=he epsFirst epsSecond hepsF hepsS degree
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β base Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss lossFinal delta Qwidth z c hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hΓ hA hsf hn hβ hlabels hbase hm hd hterminal hsmall hmargin hpuncture hslots hweights
    mark Y cutoff W source keys hl₁ hl₂ hr₁ hr₂
  have hZ1:1<Z:=by linarith
  have hb6:bw≤Z^(6*eta):=hew.le.trans (hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)))
  have hw4:Real.exp window≤Z^(4*eta):=hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  apply he p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights
    Z M r ell V Γ theta pi epschild A loss lossFinal hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap
    hVcap hwin hpi hpieta hemcost hedcost hechild hsave hloss hcard hparent hprincipal hretained htail
    hΨ hΓ hA hsf hn hβ hlabels hslots hweights
  · intro k hk
    exact canonical_lower_moments_children p hp hcop hg hc hpr pool Q k.1 k.2.1 k.2.2 true
      base Ψ hbase m hm slots lists weights w₁₁ w₁₂ Z M r ell V eta tau window bw delta Qwidth z c epschild A K degree
      hZ1 heta hbin hell hV hbw hb6 hw4 hd hterminal hsmall hmargin hpuncture hQ hl₁ hl₂
  · intro k hk
    exact canonical_lower_moments_children p hp hcop hg hc hpr pool Q k.1 k.2.1 k.2.2 false
      base Ψ hbase m hm slots lists weights w₂₁ w₂₂ Z M r ell V eta tau window bw delta Qwidth z c epschild A K degree
      hZ1 heta hbin hell hV hbw hb6 hw4 hd hterminal hsmall hmargin hpuncture hQ hr₁ hr₂

end SevenEighths.InverseMoment

end

end OAI

end Source2770

/- Original source: OAI/NumberTheory/DirichletL/Descent/RecursionParameters.lean; sha256: 31bf0d226c4b360593537fec979748c045a454d6e82363675fb66486fce2fe0b -/
section Source2771
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

def firstPassEpsilon (F eta:ℝ):ℝ:=eta/(10*F+32)
def sourceMassEpsilon (F eta:ℝ):ℝ:=2*eta/(20*(3*F+16)+30)

theorem actual_step_parameters (F eta r ell epsChild:ℝ)
    (hF:0≤F)(heta:0<eta)(heta1:eta≤1)(hr:r≤F)(hell:ell≤F)(heps:0≤epsChild):
    0<firstPassEpsilon F eta ∧ 0<sourceMassEpsilon F eta ∧
    6*eta≤8*eta ∧
    sourceMassEpsilon F eta*(20*(3*F+16)+30)≤(8*eta)/4 ∧
    48*eta+eta+8*eta+epsChild+eta≤epsChild+58*eta ∧
    3*eta+firstPassEpsilon F eta*(5*ell+2*r+7*eta)≤epsChild+60*eta ∧
    (epsChild+58*eta)+(2*F+15*eta+eta)*firstPassEpsilon F eta+firstPassEpsilon F eta≤epsChild+60*eta :=by
  have hd:0<10*F+32:=by positivity
  have hm:0<20*(3*F+16)+30:=by positivity
  have he:0<firstPassEpsilon F eta:=div_pos heta hd
  have heq:firstPassEpsilon F eta*(10*F+32)=eta:=by unfold firstPassEpsilon;field_simp
  have heq':sourceMassEpsilon F eta*(20*(3*F+16)+30)=2*eta:=by unfold sourceMassEpsilon;field_simp
  refine ⟨he,div_pos (by positivity) hm,by linarith,by linarith,by ring_nf;linarith,?_,?_⟩
  · have hcap:5*ell+2*r+7*eta≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith
  · have hcap:2*F+15*eta+eta+1≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith

theorem actual_long_rank_slack (cutoff eta ell V:ℝ)(hd:0<cutoff)(_he:0≤eta)
    (hsmall:eta≤cutoff/32)(hprogress:cutoff-eta≤ell+V):
    0<cutoff/2 ∧ cutoff/2≤ell+V ∧ eta≤(cutoff/2)/16 ∧ 17*eta≤cutoff :=by
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem actual_recursion_parameters (Mcap Fcap c eps:ℝ)(_hM:0≤Mcap)(_hF:0≤Fcap)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤(c/2)/200 ∧ eta≤(c/2)/100000 ∧
      let depth:=actualDepth Mcap (cutoff/2);
      (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*100*eta≤eps/4 :=by
  let cutoff:=c/1000
  have hd:0<cutoff:=by dsimp[cutoff];positivity
  let depth:=actualDepth Mcap (cutoff/2)
  let D:ℝ:=(depth:ℝ)+1
  have hD:0<D:=by dsimp[D];positivity
  let eta:=min 1 (min (cutoff/32) (min (c/200000) (min (c/(28*D)) (min (1/(30*D)) (eps/(800*D))))))
  have he:0<eta:=by dsimp[eta];positivity
  have he1:eta≤1:=min_le_left _ _
  have he2:eta≤cutoff/32:=(min_le_right _ _).trans (min_le_left _ _)
  have he3:eta≤c/200000:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4:eta≤c/(28*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he5:eta≤1/(30*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he6:eta≤eps/(800*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨cutoff,eta,hd,he,he1,he2,by dsimp[cutoff];linarith,by linarith,?_⟩
  have h4:eta*(28*D)≤c:=(le_div_iff₀ (by positivity)).mp he4
  have h5:eta*(30*D)≤1:=(le_div_iff₀ (by positivity)).mp he5
  have h6:eta*(800*D)≤eps:=(le_div_iff₀ (by positivity)).mp he6
  have hn:(depth:ℝ)*eta≤D*eta:=mul_le_mul_of_nonneg_right (by dsimp[D];linarith) he.le
  change (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧ (depth:ℝ)*100*eta≤eps/4
  constructor <;> first | nlinarith | constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI

end Source2771

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteBudget.lean; sha256: 54ec2525e2dfb6fe062771f389a4e7674087dcb2fb6abf005a9f8daad2ce10a7 -/
section Source2772
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_complete_step_cost (L eta epsChild:ℝ)(hL:0≤L)(heta:0<eta)
    (heta1:eta≤1)(heps:0≤epsChild):
    3*eta+firstPassEpsilon L eta*(2*L+7*eta)≤epsChild+60*eta ∧
    2*L*firstPassEpsilon L eta≤eta ∧
    (epsChild+60*eta)+2*L*firstPassEpsilon L eta+eta≤epsChild+62*eta := by
  have hd:0<10*L+32:=by positivity
  have hp:0<firstPassEpsilon L eta:=div_pos heta hd
  have he:firstPassEpsilon L eta*(10*L+32)=eta:=by unfold firstPassEpsilon;field_simp
  have hb:2*L+7*eta≤10*L+32:=by linarith
  have hc:=mul_le_mul_of_nonneg_left hb hp.le
  have hl:=mul_le_mul_of_nonneg_left (show 2*L≤10*L+32 by linarith) hp.le
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem actual_complete_height_merge (dshort dlong:ℕ)(Z F cstar loss Cs Cb A theta:ℝ)
    (hZ:1≤Z)(hcstar:0≤cstar)(hloss:0≤loss)(hCs:0≤Cs)(hCb:0≤Cb)(hA:0≤A):
    Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
    (Cs+Cb)*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss) := by
  have hp:1≤1+‖theta‖:=by linarith [norm_nonneg theta]
  have hshort:(1+‖theta‖)^dshort≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_left _ _)
  have hlong:(1+‖theta‖)^dlong≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_right _ _)
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:Z^(F-cstar/256)≤Z^(F+loss):=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hs':Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)≤
      Cs*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by
    calc
      _≤Cs*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
      _≤_:=by
        have hh:Cs≤Cs*(1+A):=by nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
  have hl':Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
      Cb*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
  have hh:=add_le_add hs' hl'
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI

end Source2772

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankPuncture.lean; sha256: 8bd768de8c67316bde0d7ca3a7cef64a3b01dc708730f5e2385b675d305e42f0 -/
section Source2773
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseTerminalWidths
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_parent_puncture (m:O)(hm:m≠0)(Z:ℝ)(hZ:1<Z):
    (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) :=by
  have hi:(Ideal.span {m}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hm
  have hn:0<(Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ):=actual_ideal_norm_pos _ hi
  have hle:Ideal.absNorm (Ideal.span {m}:Ideal O).radical≤Ideal.absNorm (Ideal.span {m}:Ideal O):=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hi))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  unfold normWidth
  rw [Real.rpow_logb (by linarith:0<Z) (ne_of_gt hZ) hn]
  exact_mod_cast hle

end SevenEighths.InverseMoment

end

end OAI

end Source2773

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistenceData.lean; sha256: 84da1aa426d0e3d661cc7aeb9af0a599b75b9c9251a8c2cc3140e43de269e5d7 -/
section Source2774
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CompletePoolRankMoments (q D:ℕ) {σ:Type}[DecidableEq σ]
    (slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (base:O→*ℂ)(W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
  let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q);
  letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
  CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ base slots lists a W
    Z Mmax Fcap z c eps A K degree

def rankRowCap (n:ℕ)(cutoff:ℝ):ℝ:=3*((n:ℝ)-1)*cutoff/4

def rankTotalCap (n:ℕ)(L eta:ℝ):ℝ:=L-15*(n:ℝ)*eta

def rankMargin (n:ℕ)(cstar eta:ℝ):ℝ:=cstar/2+7*(n:ℝ)*eta

def rankLoss (n:ℕ)(eta:ℝ):ℝ:=62*(n:ℝ)*eta

def RankEnergyExists (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) C K degree

theorem rank_energy_exists_zero (L cstar cutoff eta:ℝ)(hcut:0<cutoff)(K:ℕ)(W:𝓢(ℝ,ℂ)):
    RankEnergyExists 0 L cstar cutoff eta K W :=by
  refine ⟨0,1,le_rfl,?_⟩
  intro q hq
  refine ⟨1,2,by norm_num,by norm_num,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments]
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply canonical_rank_negative
  simp only [rankRowCap,Nat.cast_zero]
  linarith

theorem actual_rank_successor_caps (n:ℕ)(L cstar cutoff eta M F c:ℝ)
    (hM:M≤rankRowCap (n+1) cutoff)(hF:F≤rankTotalCap (n+1) L eta)
    (hc:rankMargin (n+1) cstar eta≤c):
    M-3*cutoff/4≤rankRowCap n cutoff ∧ F+15*eta≤rankTotalCap n L eta ∧
      rankMargin n cstar eta≤c-7*eta :=by
  unfold rankRowCap rankTotalCap rankMargin at *
  push_cast at *
  constructor <;> first | linarith | constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI

end Source2774

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankFamilyGates.lean; sha256: 5a3521c9554bb8274c79f6295a5297c23a088594d1d6a020c44f99eea945545e -/
section Source2775
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalCoefficientClass InverseTerminalWidths
open ConcretePrimeRowBridge CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem actual_rank_family_period (q:ℕ)(base Ψ:O→*ℂ)
    (hbase:FactorsModulo (fixedBaseConductor q) base)
    (hΨ:IsBaseRayTwist base Ψ):
    FactorsModulo (fixedBaseConductor q) Ψ := by
  intro x y hxy
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x y hxy
  · simp only [MonoidHom.mul_apply]
    rw [hbase x y hxy]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

theorem actual_rank_family_gates (q:ℕ)(base:O→*ℂ)
    (hbase:∀x,‖base x‖≤1)(hperiod:FactorsModulo (fixedBaseConductor q) base):
    ∀Ψ:O→*ℂ,IsBaseRayTwist base Ψ→
      (∀x,‖Ψ x‖≤1) ∧ FactorsModulo (fixedBaseConductor q) Ψ := by
  intro Ψ hΨ
  exact ⟨hΨ.norm_le hbase,actual_rank_family_period q base Ψ hperiod hΨ⟩

theorem actual_rank_norm_width (m:O)(Z Q:ℝ)(hZ:1<Z)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    normWidth Z (Ideal.span {m})=Q := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
  rw [normWidth,hn,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]

theorem actual_rank_state_gates (m:O)(hm:m≠0)(Z N V M Q z c L:ℝ)
    (hZ:1<Z)(hN:0≤N)(hV:0≤V)(hM:0≤M)(hQ:0≤Q)(hz:0≤z)(hc:0≤c)
    (hcap:N+V≤L)(hmargin:CanonicalMargins (N+V) M Q z c)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    N≤L ∧ V≤L ∧ M≤N+V ∧ Q≤L ∧ z≤L ∧
      normWidth Z (Ideal.span {m})=Q ∧
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z c ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ)≤Z^L ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q := by
  have hfirst:=hmargin.1
  have hQcap:Q≤L:=by linarith
  have he:=actual_rank_norm_width m Z Q hZ hn
  refine ⟨by linarith,by linarith,by linarith,hQcap,by linarith,he,?_,?_,?_⟩
  · rwa [he]
  · rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
    rw [hn]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hQcap
  · simpa only [he] using actual_rank_parent_puncture m hm Z hZ

theorem canonical_rank_subslots {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A:ℝ)(K degree:ℕ)(hsub:subslots⊆slots)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base subslots lists a W Z M F z c eps A K degree := by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  exact h Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss
    (hss.trans hsub) labels hlabels s

theorem canonical_rank_subslot_product {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i):
    (∏i∈subslots,H i)≤∏i∈slots,H i :=
  Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    (fun i hi=>(zero_le_one: (0:ℝ)≤1).trans (hH i (hsub hi)))
    (fun i hi _=>hH i hi)

theorem canonical_rank_subslot_cap {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(Z z:ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i)(hcap:(∏i∈slots,H i)≤Z^z):
    (∏i∈subslots,H i)≤Z^z :=
  (canonical_rank_subslot_product slots subslots H hsub hH).trans hcap

end SevenEighths.InverseMoment

end

end OAI

end Source2775

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistenceSuccessor.lean; sha256: f35c0a704fe90157aa2e5eba6b2b38cfe8293b09955c1b5a5fa03d841e554d9d -/
section Source2776
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase InverseTerminalWidths
open CanonicalCubeSeparation CompletedHeight InverseMomentFirstSecondHeightCost
local notation "O"=>ActualEisensteinCubic.O

theorem rank_energy_exists_succ_of_reference
    (n:ℕ)(L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32)
    (hIH:∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W)
    (W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0→|x|≤Alog)
    (hone:∀x,|x|≤columnWindowRadius lo hi→Vlog x=1)
    (hlarge:∀window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
      2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
      hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta):
    RankEnergyExists (n+1) L cstar cutoff eta K W :=by
  have hL0:0≤L:=by linarith
  have heF:0<firstPassEpsilon L eta:=by unfold firstPassEpsilon;positivity
  have hem:0<sourceMassEpsilon L eta:=by unfold sourceMassEpsilon;positivity
  obtain ⟨w11,w12,w21,w22,af1,bf1,af2,bf2,window,bw,ds,ha1,hab1,ha2,hab2,
    hw11,hw12,hw21,hw22,hs11,hs12,hs21,hs22,hbw,hbA,hbexp,hstep⟩:=
    actual_complete_normalized_rank_step lo hi hlo hhi W hsW (W.smooth ⊤) Vlog Alog hbox hone
      L cstar eta eta 1 (sourceMassEpsilon L eta) (sourceMassEpsilon L eta) eta
      hL hcstar heta heta1 hetac heta heta1 hem hem heta K
  obtain ⟨J11,B11,hB11,ih11⟩:=hIH w11 af1 bf1 ha1 (by linarith) (subset_closure.trans hs11)
  obtain ⟨J12,B12,hB12,ih12⟩:=hIH w12 af1 bf1 ha1 (by linarith) (subset_closure.trans hs12)
  obtain ⟨J21,B21,hB21,ih21⟩:=hIH w21 af2 bf2 ha2 (by linarith) (subset_closure.trans hs21)
  obtain ⟨J22,B22,hB22,ih22⟩:=hIH w22 af2 bf2 ha2 (by linarith) (subset_closure.trans hs22)
  let J:=J11+J12+J21+J22
  let dl:=2*(InverseClippingProfiles.momentOrder (firstDegree J)+(volume:Measure ℝ).integrablePower)
  let Jout:=max ds dl
  let B:=1+hi+B11+B12+B21+B22
  have hB:1≤B:=by dsimp [B];linarith
  have hb0:0≤B:=by linarith
  have hhiB:hi≤B:=by dsimp [B];linarith
  have hBB11:B11≤B:=by dsimp [B];linarith
  have hBB12:B12≤B:=by dsimp [B];linarith
  have hBB21:B21≤B:=by dsimp [B];linarith
  have hBB22:B22≤B:=by dsimp [B];linarith
  have hj11:J11≤J:=by dsimp [J];omega
  have hj12:J12≤J:=by dsimp [J];omega
  have hj21:J21≤J:=by dsimp [J];omega
  have hj22:J22≤J:=by dsimp [J];omega
  obtain ⟨Zt,hZt,hlarge⟩:=hlarge window
  refine ⟨Jout,B,hB,?_⟩
  intro q hq
  obtain ⟨C11,Z11,hC11,hZ11,ih11⟩:=ih11 q hq
  obtain ⟨C12,Z12,hC12,hZ12,ih12⟩:=ih12 q hq
  obtain ⟨C21,Z21,hC21,hZ21,ih21⟩:=ih21 q hq
  obtain ⟨C22,Z22,hC22,hZ22,ih22⟩:=ih22 q hq
  obtain ⟨Cs,Cb,Zs,hCs,hCb,hZs,hstep⟩:=hstep (firstPassEpsilon L eta) eta heF heta J q hq
  let A:=C11+C12+C21+C22
  have hA:0≤A:=by dsimp [A];linarith
  have hCA11:C11≤A:=by dsimp [A];linarith
  have hCA12:C12≤A:=by dsimp [A];linarith
  have hCA21:C21≤A:=by dsimp [A];linarith
  have hCA22:C22≤A:=by dsimp [A];linarith
  let C:=(Cs+Cb)*(1+A)
  let Z₀:=Zs+Zt+Z11+Z12+Z21+Z22
  have hC:0<C:=by dsimp [C];positivity
  have hZ₀:1<Z₀:=by dsimp [Z₀];linarith
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have hZs':Zs≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZt':Zt≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ11':Z11≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ12':Z12≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ21':Z21≤Z:=by dsimp [Z₀] at hZ;linarith
  have hZ22':Z22≤Z:=by dsimp [Z₀] at hZ;linarith
  obtain ⟨hZ2,h2,hExp,hlog,hhiZ,hAZ,hwin⟩:=hlarge Z hZt'
  have hZ1:1<Z:=by linarith
  have hZ0:0<Z:=by linarith
  have hD11:B11*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB11 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD12:B12*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB12 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD21:B21*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB21 (Real.rpow_nonneg hZ0.le _)).trans hD
  have hD22:B22*Z^L≤D:=(mul_le_mul_of_nonneg_right hBB22 (Real.rpow_nonneg hZ0.le _)).trans hD
  have m11:=ih11 Z hZ11' D hD11 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m12:=ih12 Z hZ12' D hD12 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m21:=ih21 Z hZ21' D hD21 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  have m22:=ih22 Z hZ22' D hD22 slots hslots lists H a hdis hH hP ha z hz hprod base hbase hperiod
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only [CompletePoolRankMoments] at m11 m12 m21 m22 ⊢
  intro Ψ hΨ m hm N V M Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels theta
  have hcap:N+V≤L:=by
    unfold rankTotalCap at hFc
    have hh:0≤15*((n+1:ℕ):ℝ)*eta:=by positivity
    linarith
  have hcm:0≤rankMargin (n+1) cstar eta:=by unfold rankMargin;positivity
  obtain ⟨hNL,hVL,hMF,hQL,hzL,hwidth,hmargin',hmL,hpuncture⟩:=
    actual_rank_state_gates m hm Z N V M Qwidth z (rankMargin (n+1) cstar eta) L
      hZ1 hN hV hM hQ hz hcm hcap hmargin hnorm
  obtain ⟨hΨnorm,hΨperiod⟩:=actual_rank_family_gates q base hbase hperiod Ψ hΨ
  have hDparent:hi*Z^N≤D:=by
    calc
      _≤B*Z^L:=mul_le_mul hhiB (Real.rpow_le_rpow_of_exponent_le hZ1.le hNL)
        (Real.rpow_nonneg hZ0.le _) hb0
      _≤D:=hD
  have hsscard:ss.card≤K:=(Finset.card_le_card hss).trans hslots
  have hssdis:(ss:Set σ).PairwiseDisjoint lists:=by
    intro i hi j hj hij
    exact hdis (hss hi) (hss hj) hij
  have hssH:∀i∈ss,1≤H i:=fun i hi=>hH i (hss hi)
  have hssP:∀i∈ss,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i:=fun i hi=>hP i (hss hi)
  have hssa:∀i∈ss,∀P∈lists i,‖a i P‖≤1:=fun i hi=>ha i (hss hi)
  have hssprod:(∏i∈ss,H i)≤Z^z:=canonical_rank_subslot_cap slots ss H Z z hss hH hprod
  obtain ⟨hsmallM,hsmallF,hsmallc⟩:=actual_rank_successor_caps n L cstar cutoff eta M (N+V)
    (rankMargin (n+1) cstar eta) hMc hFc le_rfl
  have lift (w:𝓢(ℝ,ℂ))(Cw:ℝ)(Jw:ℕ)(hCw:0≤Cw)(hCwA:Cw≤A)(hJw:Jw≤J)
      (mw:CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a w Z (rankRowCap n cutoff)
        (rankTotalCap n L eta) z (rankMargin n cstar eta) (rankLoss n eta) Cw K Jw):
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base ss lists a w Z (M-3*(cutoff/2)/2)
        (N+V+15*eta) z (rankMargin (n+1) cstar eta-7*eta) (rankLoss n eta) A K J:=by
    apply canonical_rank_subslots (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots ss lists a w Z _ _ z _ _ A K J hss
    apply canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z
      (M-3*(cutoff/2)/2) (rankRowCap n cutoff) (N+V+15*eta) (rankTotalCap n L eta)
      z (rankMargin (n+1) cstar eta-7*eta) (rankMargin n cstar eta) (rankLoss n eta) A K J
      (by linarith) hsmallF hsmallc
    exact canonical_rank_height_constant (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a w Z _ _ z _ _ Cw A K Jw J
      hZ0 hCw hCwA hJw mw
  have hechild:0≤rankLoss n eta:=by unfold rankLoss;positivity
  obtain ⟨_,_,hpieta,hmass,hret,hprincipal0,hcost⟩:=actual_step_parameters L eta 0 0 (rankLoss n eta)
    hL0 heta heta1 (by linarith) (by linarith) hechild
  obtain ⟨hprincipal,hFirst,hFinal⟩:=actual_complete_step_cost L eta (rankLoss n eta) hL0 heta heta1 hechild
  have hreserve:cstar/2≤rankMargin (n+1) cstar eta:=by
    unfold rankMargin
    exact le_add_of_nonneg_right (by positivity)
  have hbound:=hstep m hm Z N V M z (rankMargin (n+1) cstar eta) cutoff (8*eta)
    (rankLoss n eta) A (rankLoss n eta+58*eta) (rankLoss n eta+60*eta) theta
    hZs' hZ2 h2 hExp hlog hN hV hM hcap hMF hzL hhiZ hAZ hwin hcut hcutL hcutc hetad hmL hmargin'
    hreserve (by simpa only [hwidth] using hpuncture) (by positivity) hpieta hmass hmass hechild
    (by linarith) hret hprincipal hcost (by linarith) hA
    labels (fun I hI=>⟨⟨(hlabels I hI).1.1,(hlabels I hI).1.2.2⟩,(hlabels I hI).1.2.1,(hlabels I hI).2⟩)
    D hDparent ss hsscard lists H hssdis hssH hssP hssprod base Ψ hΨ hΨnorm hΨperiod a hssa
    (lift w11 C11 J11 hC11.le hCA11 hj11 m11) (lift w12 C12 J12 hC12.le hCA12 hj12 m12)
    (lift w21 C21 J21 hC21.le hCA21 hj21 m21) (lift w22 C22 J22 hC22.le hCA22 hj22 m22)
  have hnextLoss:rankLoss n eta+62*eta=rankLoss (n+1) eta:=by unfold rankLoss;push_cast;ring
  have hlongexp:(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta≤rankLoss (n+1) eta:=by
    simpa only [hnextLoss] using hFinal
  have hloss0:0≤rankLoss (n+1) eta:=by unfold rankLoss;positivity
  have hlong:Cb*(1+A)*(1+‖theta‖)^dl*
      Z^(N+V+(rankLoss n eta+60*eta)+2*L*firstPassEpsilon L eta+eta)≤
      Cb*(1+A)*(1+‖theta‖)^dl*Z^(N+V+rankLoss (n+1) eta):=by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ1.le
    linarith
  have hh:=hbound.trans (add_le_add le_rfl hlong)
  have hmrg:=actual_complete_height_merge ds dl Z (N+V) cstar (rankLoss (n+1) eta) Cs Cb A theta
    hZ1.le hcstar.le hloss0 hCs.le hCb hA
  have hpow:(1+‖theta‖)^Jout≤(1+‖theta‖)^(2*Jout):=
    pow_le_pow_right₀ (by linarith [norm_nonneg theta]) (by omega)
  have hf:childLogTest W theta=normTwistedSource W theta:=by
    funext y
    simp only [childLogTest,normTwistedSource,mul_comm]
  rw [hf]
  apply (hh.trans hmrg).trans
  dsimp only [C,Jout]
  have hx:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (show 0≤(Cs+Cb)*(1+A) by positivity))
    (Real.rpow_nonneg hZ0.le (N+V+rankLoss (n+1) eta))
  convert hx using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI

end Source2776

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankDepthParameters.lean; sha256: e940291425c7535fa521dd5b3f2b1dc4ccdd98096bb76efd0dc50bf63784aa6d -/
section Source2777
namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_rank_depth_covers (Mmax cutoff:ℝ)(hcut:0<cutoff):
    Mmax≤rankRowCap (actualDepth Mmax (cutoff/2)) cutoff := by
  have hceil:=Nat.le_ceil (2*Mmax/(3*(cutoff/2)))
  have hscaled:2*Mmax≤(⌈2*Mmax/(3*(cutoff/2))⌉₊:ℝ)*(3*(cutoff/2)):=
    (div_le_iff₀ (by positivity:0<3*(cutoff/2))).mp hceil
  unfold rankRowCap actualDepth
  push_cast
  nlinarith

theorem actual_rank_depth_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤c/200 ∧ eta≤c/100000 ∧
      let n:=actualDepth Mmax (cutoff/2);
      0<n ∧ Mmax≤rankRowCap n cutoff ∧
      ∀k:ℕ,k≤n→Fmax≤rankTotalCap k (Fmax+1) eta ∧
        c/2≤rankMargin k c eta ∧ rankMargin k c eta≤c ∧
        0≤rankLoss k eta ∧ rankLoss k eta≤eps/4 := by
  let csmall:=min c 1
  have hcs:0<csmall:=lt_min hc (by norm_num)
  have hcc:csmall≤c:=min_le_left _ _
  have hc1:csmall≤1:=min_le_right _ _
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutc,hetac,hbudgets⟩:=
    actual_recursion_parameters Mmax Fmax csmall eps hM hF hcs heps
  dsimp only at hbudgets
  refine ⟨cutoff,eta,hcut,heta,heta1,hetacut,by linarith,by linarith,by linarith,?_⟩
  dsimp only
  refine ⟨actualDepth_pos _ _,actual_rank_depth_covers Mmax cutoff hcut,?_⟩
  intro k hk
  have hk':(k:ℝ)≤(actualDepth Mmax (cutoff/2):ℝ):=by exact_mod_cast hk
  have hmono:=mul_le_mul_of_nonneg_right hk' heta.le
  have hk0:0≤(k:ℝ):=Nat.cast_nonneg _
  have hkE:0≤(k:ℝ)*eta:=mul_nonneg hk0 heta.le
  rcases hbudgets with ⟨hmargin,hsize,hloss⟩
  unfold rankTotalCap rankMargin rankLoss
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem actual_rank_top_parameters (Mmax Fmax c eps:ℝ)
    (hM:0≤Mmax)(hF:0≤Fmax)(hc:0<c)(heps:0<eps):
    ∃(n:ℕ)(cutoff eta:ℝ),n=actualDepth Mmax (cutoff/2) ∧
      0<n ∧ 0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤Fmax+1 ∧ cutoff≤c/200 ∧ eta≤c/100000 ∧
      Mmax≤rankRowCap n cutoff ∧ Fmax≤rankTotalCap n (Fmax+1) eta ∧
      c/2≤rankMargin n c eta ∧ rankMargin n c eta≤c ∧
      0≤rankLoss n eta ∧ rankLoss n eta<eps := by
  obtain ⟨cutoff,eta,hcut,heta,heta1,hetacut,hcutL,hcutc,hetac,hn,hrow,hall⟩:=
    actual_rank_depth_parameters Mmax Fmax c eps hM hF hc heps
  have htop:=hall (actualDepth Mmax (cutoff/2)) le_rfl
  refine ⟨actualDepth Mmax (cutoff/2),cutoff,eta,rfl,hn,hcut,heta,heta1,hetacut,
    hcutL,hcutc,hetac,hrow,htop.1,htop.2.1,htop.2.2.1,htop.2.2.2.1,?_⟩
  linarith [htop.2.2.2.2]

end SevenEighths.InverseMoment

end

end OAI

end Source2777

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankEnergyMonotone.lean; sha256: cb0f970ccf49664b48a8d28081b592fc2d10679c58987beb75bbb2fa71013df5 -/
section Source2778
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA

end SevenEighths.InverseMoment

end

end OAI

end Source2778

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalEnergyExistenceData.lean; sha256: 1a8d03934668493314e431f0094af47e1a6e8f314e5f7d8b85f9ae1abc5f148d -/
section Source2779
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase
local notation "O"=>ActualEisensteinCubic.O

def CanonicalEnergyExists (Mcap Fcap c eps L:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ)):Prop :=
  ∃degree:ℕ,∃B:ℝ,1≤B ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀D:ℕ,B*Z^L≤D→
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H:σ→ℝ)(a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→
      (∀i∈slots,1≤H i)→(∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→
    ∀z:ℝ,0≤z→(∏i∈slots,H i)≤Z^z→
    ∀base:O→*ℂ,(∀u,‖base u‖≤1)→
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) base→
      CompletePoolRankMoments q D slots lists a base W Z Mcap Fcap z c eps C K degree

theorem canonical_energy_of_rank (n:ℕ)(L cstar cutoff eta Mcap Fcap c eps:ℝ)(K:ℕ)(W:𝓢(ℝ,ℂ))
    (hM:Mcap≤rankRowCap n cutoff)(hF:Fcap≤rankTotalCap n L eta)
    (hc:rankMargin n cstar eta≤c)(he:rankLoss n eta≤eps)
    (h:RankEnergyExists n L cstar cutoff eta K W):
    CanonicalEnergyExists Mcap Fcap c eps L K W :=by
  obtain ⟨degree,B,hB,h⟩:=h
  refine ⟨degree,B,hB,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,h⟩:=h q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  have hmom:=h Z hZ D hD slots hslots lists H a hdis hH hP ha z hz hprod base hb hp
  dsimp only [CompletePoolRankMoments] at hmom ⊢
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D (reflectionExcludedPrimes_bad q)
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  apply canonical_rank_loss_le (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap Fcap z c (rankLoss n eta) eps C K degree
    (by linarith) hC.le he
  exact canonical_rank_restrict (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) Finset.univ base slots lists a W Z Mcap (rankRowCap n cutoff)
    Fcap (rankTotalCap n L eta) z c (rankMargin n cstar eta) (rankLoss n eta) C K degree hM hF hc hmom

end SevenEighths.InverseMoment

end

end OAI

end Source2779

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistenceInduction.lean; sha256: 253c41f23b601d0c592a313f50bd95977e96c049982b019e4cca7d03a6622358 -/
section Source2780
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open CanonicalCubeSeparation

def RankReferenceCutoffs:Prop :=
  ∀lo hi:ℝ,0<lo→0≤hi→∃(Vlog:𝓢(ℝ,ℂ))(Alog:ℝ),
    (∀x,Vlog x≠0→|x|≤Alog) ∧
    (∀x,|x|≤columnWindowRadius lo hi→Vlog x=1)

def RankReferenceThresholds:Prop :=
  ∀eta:ℝ,0<eta→∀hi Alog window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
    2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
    hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta

theorem rank_energy_exists_all_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32):
    ∀n:ℕ,∀(W:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo→0≤hi→
      Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi→RankEnergyExists n L cstar cutoff eta K W :=by
  intro n
  induction n with
  | zero =>
      intro W lo hi hlo hhi hsW
      exact rank_energy_exists_zero L cstar cutoff eta hcut K W
  | succ n ih =>
      intro W lo hi hlo hhi hsW
      obtain ⟨Vlog,Alog,hbox,hone⟩:=href lo hi hlo hhi
      exact rank_energy_exists_succ_of_reference n L cstar cutoff eta K hL hcstar hcut hcutL
        hcutc heta heta1 hetac hetad ih W lo hi hlo hhi hsW Vlog Alog hbox hone
        (fun window=>hthreshold eta heta hi Alog window)

theorem canonical_energy_exists_of_references
    (href:RankReferenceCutoffs)(hthreshold:RankReferenceThresholds)
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=by
  obtain ⟨n,cutoff,eta,hn,hpos,hcut,heta,heta1,hetad,hcutL,hcutc,hetac,hrow,hcap,hmargin0,hmargin,hloss0,hloss⟩:=
    actual_rank_top_parameters Mcap Fcap c eps hM hF hc heps
  have he:=rank_energy_exists_all_of_references href hthreshold (Fcap+1) c cutoff eta K
    (by linarith) hc hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW
  exact canonical_energy_of_rank n (Fcap+1) c cutoff eta Mcap Fcap c eps K W
    hrow hcap hmargin hloss.le he

end SevenEighths.InverseMoment

end

end OAI

end Source2780

/- Original source: OAI/NumberTheory/DirichletL/Inversion/CanonicalReferenceThreshold.lean; sha256: 013aa771f4f84decba163ede69d9626e4dc953cef4aa865099b4e6b21bf6dc93 -/
section Source2781
namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap ContDiff

namespace SevenEighths.InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvzero⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (R / eta)) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self Alog, abs_nonneg hi, abs_nonneg window]
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self window, abs_nonneg hi, abs_nonneg Alog]

theorem canonical_reference_pool_coverage (hi B Z N L D : ℝ)
    (hB : 0 ≤ B) (hhi : hi ≤ B) (hZ : 1 ≤ Z) (hNL : N ≤ L)
    (hD : B * Z ^ L ≤ D) : hi * Z ^ N ≤ D := by
  calc
    hi * Z ^ N ≤ B * Z ^ N :=
      mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg (by linarith) _)
    _ ≤ B * Z ^ L :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hNL) hB
    _ ≤ D := hD

theorem exists_canonical_reference_family_gates {ι : Type*} (s : Finset ι)
    (hi Alog window : ι → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 < B ∧ ∃ Z0 : ℝ, 1 < Z0 ∧
      (∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧ Real.exp (window i) ≤ B) ∧
      ∀ Z : ℝ, Z0 ≤ Z →
        2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
        1 ≤ eta * Real.log Z ∧ B ≤ Z ^ eta ∧
        (∀ i ∈ s, hi i ≤ Z ^ eta ∧ Real.exp (Alog i) ≤ Z ^ eta ∧
          Real.exp (window i) ≤ Z ^ eta) ∧
        (∀ i ∈ s, ∀ N L D : ℝ, N ≤ L → B * Z ^ L ≤ D → hi i * Z ^ N ≤ D) := by
  let mass : ι → ℝ := fun i => |hi i| + Real.exp (Alog i) + Real.exp (window i)
  have hm : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  let B : ℝ := 1 + ∑ i ∈ s, mass i
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧
      Real.exp (window i) ≤ B := by
    intro i hiS
    have hsum : mass i ≤ ∑ j ∈ s, mass j := Finset.single_le_sum (fun j _ => hm j) hiS
    dsimp [mass, B] at *
    constructor
    · linarith [le_abs_self (hi i), Real.exp_pos (Alog i), Real.exp_pos (window i)]
    constructor
    · linarith [abs_nonneg (hi i), Real.exp_pos (window i)]
    · linarith [abs_nonneg (hi i), Real.exp_pos (Alog i)]
  obtain ⟨Z0, hZ0, hgate⟩ := eventually_canonical_reference_gates B 0 0 eta heta
  refine ⟨B, hB, Z0, hZ0, hbound, ?_⟩
  intro Z hZ
  obtain ⟨hZtwo, htwo, hexp, hlog, hBpow, _, _⟩ := hgate Z hZ
  refine ⟨hZtwo, htwo, hexp, hlog, hBpow, ?_, ?_⟩
  · intro i hiS
    obtain ⟨hhi, hA, hw⟩ := hbound i hiS
    exact ⟨hhi.trans hBpow, hA.trans hBpow, hw.trans hBpow⟩
  · intro i hiS N L D hNL hD
    exact canonical_reference_pool_coverage (hi i) B Z N L D hB.le
      (hbound i hiS).1 (by linarith) hNL hD

end SevenEighths.InverseMoment

end

end OAI

end Source2781

/- Original source: OAI/NumberTheory/DirichletL/Descent/CanonicalRankExistence.lean; sha256: cc8c92db1ab0ee9ead06f4f2ab7b4229e3a2698b012989f3e335d0d1b6a2ba74 -/
section Source2782
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment

theorem actual_rank_reference_cutoffs : RankReferenceCutoffs :=by
  intro lo hi hlo hhi
  obtain ⟨Vlog,Alog,hA,hAe,hcompact,hsupport,hbox,hone,hzero⟩:=
    exists_canonical_reference_cutoff lo hi
  exact ⟨Vlog,Alog,hbox,hone⟩

theorem actual_rank_reference_thresholds : RankReferenceThresholds :=by
  intro eta heta hi Alog window
  exact eventually_canonical_reference_gates hi Alog window eta heta

theorem canonical_rank_energy_exists
    (L cstar cutoff eta:ℝ)(K:ℕ)
    (hL:1≤L)(hcstar:0<cstar)(hcut:0<cutoff)(hcutL:cutoff≤L)
    (hcutc:cutoff≤cstar/200)(heta:0<eta)(heta1:eta≤1)
    (hetac:eta≤cstar/100000)(hetad:eta≤cutoff/32)
    (n:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    RankEnergyExists n L cstar cutoff eta K W :=
  rank_energy_exists_all_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    L cstar cutoff eta K hL hcstar hcut hcutL hcutc heta heta1 hetac hetad n W lo hi hlo hhi hsW

theorem canonical_marked_energy_exists
    (Mcap Fcap c eps:ℝ)(hM:0≤Mcap)(hF:0≤Fcap)(hc:0<c)(heps:0<eps)
    (K:ℕ)(W:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)
    (hsW:Function.support (W:ℝ→ℂ)⊆Set.Icc lo hi):
    CanonicalEnergyExists Mcap Fcap c eps (Fcap+1) K W :=
  canonical_energy_exists_of_references actual_rank_reference_cutoffs actual_rank_reference_thresholds
    Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW

end SevenEighths.InverseMoment

end

end OAI

end Source2782

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerGeometry.lean; sha256: 4c23123cfb31fc427d7638282a3ac1901202ffce0a05bb8ebdd154c8e564b62d -/
section Source2783
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem outerCoefficient_nonzero_coprime
    (Ψ:Eis→*ℂ)(j:Eis)(x:Point ι)(ρ:SecondRayIndex)
    (hn:outerCoefficient p hp hcop hg Ψ j x ρ≠0) :
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) := by
  apply sourceIdeal_coprime_of_not_mem p
  intro i hi hc
  have hmc : j*(∏k∈x.common,p k)∈Ideal.span {p i} := Ideal.mul_mem_left _ j hc
  have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) x.overlap (j*(∏k∈x.common,p k))=0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃i∈x.overlap,j*(∏k∈x.common,p k)∈Ideal.span {p i}
      from ⟨i,hi,hmc⟩)]
  apply hn
  simp only [outerCoefficient,initialColumn,hz,mul_zero,zero_mul,star_zero]

theorem original_nonzero_child_squarefree
    (Ψ:Eis→*ℂ)(j:Eis)(x:Source (ι:=ι) 0)(ρ:SecondRayIndex)
    (hd:x.divisor⊆x.common)
    (hn:outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ≠0)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ hn
  change IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common) at hc
  have hdv := sourceIdeal_dvd p x.divisor x.common hd
  have hcd : IsCoprime (sourceIdeal p x.divisor) (sourceIdeal p x.overlap) :=
    hc.symm.of_isCoprime_of_dvd_left hdv
  exact squarefree_mul_iff.mpr ⟨hcd.isRelPrime,sourceIdeal_squarefree p hcop x.divisor,
    sourceIdeal_squarefree p hcop x.overlap⟩

omit [DecidableEq ι] in
theorem initial_child_label_norm (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)=
      (sourceIdeal p x.divisor).absNorm*(sourceIdeal p x.overlap).absNorm := by
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)=_
  simp only [map_mul,Nat.cast_mul]

include hp in

theorem initial_child_row_norm (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ) :
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2=
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency))‖^2=_
  have he : primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      ((u^5:Eisˣ):Eis)*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency) := by
    change primaryGenerator (sourceIdeal p x.divisor)*((u:Eis)^5*x.frequency)=
      (u:Eis)^5*(primaryGenerator (sourceIdeal p x.divisor)*x.frequency)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul,map_mul,norm_mul,mul_pow]
  rw [eisEmbedding_norm_sq_eq_absNorm_span,sourceIdeal_gen p hp hpr]
  rfl

include hp in
theorem initial_child_row_ball (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(R:ℝ) :
    (initialChild (toTuple p (sectorSource u x))).2.2∈nonzeroChildFrequencyBall 1 R ↔
    0<((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2 ∧
      ((sourceIdeal p x.divisor).absNorm:ℝ)*‖eisEmbedding x.frequency‖^2≤R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,initial_child_row_norm p hp hpr]

include hp in

theorem initial_child_enclosures
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(u:Eisˣ)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤Z^(θ+v+2*η) ∧
      ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤Z^(θ+H+2*η) := by
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul hd hv (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  · apply (mul_le_mul hd hh (by positivity) (by positivity)).trans_eq
    rw [←Real.rpow_add hZ]
    congr 1
    ring

end SevenEighths.InverseInitialEnergyCallerGeometry

end

end OAI

end Source2783

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerSourceMask.lean; sha256: 07ef319ebf95c4c2a4a743bc39c516146e2496dbf8263bb68c17f95a3e37e49f -/
section Source2784
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSourceMask
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialProfile ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coprimeSource (S:Finset (Source (ι:=ι) 0)) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common))

theorem physicalBlock_coprimeSource
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(H:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j H W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (coprimeSource p S)) (w∘erasePoint)
      Ψ j H W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,coprimeSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hc:IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.common)
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hxpoint : sourcePoint x N M∈pointSource pool S := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x,hx,?_⟩
      apply Finset.mem_image.mpr
      exact ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
    have hv := pointSource_valid pool S hdiv hf _ hxpoint
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j H W₁ W₂ Φ Z D m _ hv ρ]
    have hz : outerCoefficient p hp hcop hg Ψ j (sourcePoint x N M) ρ=0 := by
      by_contra hn
      exact hc (outerCoefficient_nonzero_coprime p hp hcop hg Ψ j (sourcePoint x N M) ρ hn)
    simp only [hz,zero_mul,mul_zero]

include hcop in
theorem retained_child_squarefree
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Squarefree (initialChild (toTuple p (sectorSource u x))).2.1 := by
  obtain ⟨hxs,hcoprime⟩ := Finset.mem_filter.mp hx
  change Squarefree (sourceIdeal p x.divisor*sourceIdeal p x.overlap)
  have hc := hcoprime.symm.of_isCoprime_of_dvd_left (sourceIdeal_dvd p _ _ (hdiv x hxs))
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,sourceIdeal_squarefree p hcop _,
    sourceIdeal_squarefree p hcop _⟩

def childLabels (S:Finset (Source (ι:=ι) 0)) : Finset (Ideal Eis) :=
  (coprimeSource p S).image (fun x=>sourceIdeal p x.divisor*sourceIdeal p x.overlap)

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem childLabels_ne_zero (S:Finset (Source (ι:=ι) 0)) :
    ∀f∈childLabels p S,f≠0 := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)

include hcop in
theorem childLabels_squarefree (S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common) : ∀f∈childLabels p S,Squarefree f := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  exact retained_child_squarefree p hcop S hdiv hx 1

omit [DecidableEq ι] in
theorem child_label_mem (S:Finset (Source (ι:=ι) 0))
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    (initialChild (toTuple p (sectorSource u x))).2.1∈childLabels p S :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem nonzero_child_ball_neg (R:ℝ)(k:Eis)(hk:k∈nonzeroChildFrequencyBall 1 R) :
    -k∈nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul] at hk ⊢
  simpa only [map_neg,norm_neg] using hk

end SevenEighths.InverseInitialEnergyCallerSourceMask

end

end OAI

end Source2784

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerRanges.lean; sha256: bcde9255ea582eebba996b817777ca8fe3a57f4891b024b0bd71b248f7d50c9d -/
section Source2785
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerRanges
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile ConcreteTraceCRT CanonicalQuadraticSieve
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp hcop hg

omit [DecidableEq ι] in
theorem sourceIdeal_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset ι) : Admissible (sourceIdeal p S) := by
  refine ⟨sourceIdeal_ne_zero p hp S,sourceIdeal_squarefree p hcop S,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (sourceIdeal_ne_zero p hp S)).mp hP
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod] at hdiv
  obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i=>Ideal.span {p i})).mp hdiv
  have he := (prime_dvd_prime_iff_eq hprime (sourcePrime p i).property).mp hPi
  rw [he]
  exact ⟨hg i,hc i⟩

theorem retained_label_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Admissible (initialChild (toTuple p (sectorSource u x))).2.1 := by
  have hs := (supported_mul_iff (sourceIdeal p x.divisor) (sourceIdeal p x.overlap)).mpr
    ⟨admissible_supported (sourceIdeal_admissible p hp hcop hg hc _),
      admissible_supported (sourceIdeal_admissible p hp hcop hg hc _)⟩
  exact ⟨hs.1,retained_child_squarefree p hcop S hdiv hx u,hs.2⟩

theorem childLabels_subset_range
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (Z θ v η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η)) :
    childLabels p S⊆idealRange (Z^(θ+v+2*η)) := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  apply mem_idealRange.mpr
  refine ⟨retained_label_admissible p hp hcop hg hc S hdiv hx 1,?_⟩
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)≤_
  rw [map_mul,Nat.cast_mul]
  apply (mul_le_mul (hd x hx) (hv x hx) (by positivity) (by positivity)).trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem canonical_child_domains
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (hf:∀x∈S,x.frequency≠0)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:∀x∈coprimeSource p S,‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ∀x∈coprimeSource p S,∀u:Eisˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  intro x hx u
  refine ⟨childLabels_subset_range p hp hcop hg hc hpr S hdiv Z θ v η hZ hd hv
    (child_label_mem p S hx u),?_⟩
  rw [initial_child_row_ball p hp hpr]
  refine ⟨mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (hf x (Finset.mem_filter.mp hx).1)))),?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (fun h=>sourceIdeal_ne_zero p hp x.divisor
      (Ideal.absNorm_eq_zero_iff.mp h))
  · have he := (initial_child_enclosures p hp hpr x u Z θ v H η hZ
      (hd x hx) (hv x hx) (hh x hx)).2
    rwa [initial_child_row_norm p hp hpr] at he

end SevenEighths.InverseInitialEnergyCallerRanges

end

end OAI

end Source2785

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerWindows.lean; sha256: f6c0e802a7cf795224a3668cc8bfde4605ab526a3c3240cb9d44473a6e39b329 -/
section Source2786
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2
  change outerCutoff ψ (sourceRelative p s Z D B v θ H)≠0 at ho
  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left ho]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem actual_window_block_support
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)
    (a b A₀ B₀ A₂ B₂:ℝ)(hA₀:0<A₀)(hA₂:0<A₂)
    (hψ₀:∀y,ψ 0 y≠0→y∈Set.Icc A₀ B₀)
    (hψ₂:∀y,ψ 2 y≠0→y∈Set.Icc A₂ B₂)
    (hω₁:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₁ y=1)
    (hω₂:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₂ y=1)
    (hV:∀i y,0<y→ retainedCutoffs ψ ω₁ ω₂ i y≠0→V i (Real.log y)=1)
    (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hW₁:Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Icc a b)
    (hW₂:Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Icc a b) :
    BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
      W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0<relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  refine ⟨?_,?_,?_⟩
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₁ c₁ θ₁) ω₁ a b A₀ B₀ A₂ B₂
      _ _ _ hW₁ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 4).le hω₁ hlive
    rw [relative_column_left] at he
    rw [he,star_one]
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₂ c₂ θ₂) ω₂ a b A₀ B₀ A₂ B₂
      _ _ _ hW₂ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 5).le hω₂ hlive
    rwa [relative_column_right] at he
  · intro x hx h₁ h₂ i
    apply hV i _ (hpos x hx i)
    apply retainedCutoffs_nonzero ψ ω₁ ω₂ _ ?_ ?_ ?_ i
    · unfold outerCutoff
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0)
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 1))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 3)
    · rw [relative_column_left]
      exact star_ne_zero.mp h₁
    · rwa [relative_column_right]

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI

end Source2786

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerWindowGeometry.lean; sha256: de4a4d6dcc327765bed1c16656fe634a670c6b67b99fa583c43aa432964142b4 -/
section Source2787
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindowGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerGeometry
open InverseInitialProfile InverseInitialKernelBridge ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖eisEmbedding x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(∅,∅),by simp,rfl⟩
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖eisEmbedding x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h0.2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h2.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem retained_child_boxes
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hhi:∀i,0≤hi i)
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤
      (hi 1*hi 2)*Z^(θ+v) ∧
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤
      (hi 1*hi 3)*Z^(θ+H) := by
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul h1 h2 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring
  · apply (mul_le_mul h1 h3 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_source_quotients
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hlo:0<lo 1)(hhi:0≤hi 0)
    (Z D B v θ H:ℝ)(hZ:0<Z) :
    ∀t∈InverseInitialQuotientGeometry.quotientSet p (windowSource p S ψ Z D B v θ H),
      (t.absNorm:ℝ)≤(hi 0/lo 1)*Z^(B-θ) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [InverseInitialQuotientGeometry.quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  apply (div_le_div₀ (by positivity) h0 (mul_pos hlo (Real.rpow_pos_of_pos hZ _)) h1lo).trans_eq
  rw [Real.rpow_sub hZ]
  ring

end SevenEighths.InverseInitialEnergyCallerWindowGeometry

end

end OAI

end Source2787

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerState.lean; sha256: e20a084a1f55bdd4fb7f7dec9b436ca4c4df71dcaa2ee83e98f66ded817999b6 -/
section Source2788
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

theorem initial_F_exact (r z G B θ v:ℝ) :
    max 0 (r+z-2*G-B-v)+(θ+v)=
      initialF r z G (B-θ) (max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v)) := by
  unfold initialF
  ring

variable (hp:∀i,p i≠0)
include hp

theorem actual_window_initial_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r δ τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂) :
    c₁+δ-9*η-τ ≤
      initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      punctureLength Z t (assignedElement assigned q) - assignedCenter (all\assigned) z ∧
    c₂+4*δ-22*η-3*τ ≤
      4*initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ -
      3*initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ -
      6*assignedCenter (all\assigned) z := by
  exact retained_initial_margins p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold (window_quotient_subset_retained p S ψ Z D B v θ H ht)
    m r δ τ c₁ c₂ h₁ h₂

theorem actual_window_canonical_margins (S : Finset (Source (ι:=ι) 0))
    (ψ : Fin 4 → ℝ → ℂ) (D v H : ℝ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support (ψ 0) ⊆ Set.Icc aC bC)
    (hd : Function.support (ψ 1) ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) (hpr : ∀ i, λ₀^2 ∣ p i-1)
    {σ : Type*} [DecidableEq σ] (all assigned : Finset σ) (ha : assigned ⊆ all)
    (q : σ → Eis) (z a b : σ → ℝ) (W : σ → ℝ → ℂ)
    (hz : ∀ i ∈ all, 0 ≤ z i) (hq : ∀ i ∈ assigned, q i ≠ 0)
    (hW : ∀ i ∈ assigned, Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hret : ∀ i ∈ assigned, W i ((Ideal.absNorm (Ideal.span {q i}) : ℝ)/Z^(z i)) ≠ 0)
    (hthreshold : (∏ i ∈ assigned, b i) ≤ Z^η)
    {t : Ideal Eis} (ht : t ∈ quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂ : ℝ)
    (h₁ : r+2*assignedCenter all z ≤ m-c₁)
    (h₂ : 2*r+8*assignedCenter all z ≤ 3*m-c₂)
    (hc:0≤min c₁ c₂)(hη:η≤min c₁ c₂/100)(hτ:τ≤min c₁ c₂/100) :
    CanonicalMargins
      (max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)+(θ+v))
      (initialM m r (assignedCenter all z) (assignedCenter assigned z) (B-θ) η τ)
      (punctureLength Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z) (3*min c₁ c₂/4) := by
  let δ:=max 0 (r+assignedCenter all z-2*assignedCenter assigned z-B-v)-
    (r+assignedCenter all z-2*assignedCenter assigned z-B-v)
  have hδ:0≤δ:=sub_nonneg.mpr (le_max_right _ _)
  obtain ⟨h1,h2⟩ := actual_window_initial_margins p hp S ψ D v H
    aC bC ad bd Z B θ η hZ hC hd hCup hdlo hdiv hpr all assigned ha q z a b W
    hz hq hW hret hthreshold ht m r δ τ c₁ c₂ h₁ h₂
  rw [initial_F_exact]
  change CanonicalMargins (initialF r (assignedCenter all z) (assignedCenter assigned z) (B-θ) δ)
    _ _ _ _
  have hc1:=min_le_left c₁ c₂
  have hc2:=min_le_right c₁ c₂
  constructor <;> linarith

end SevenEighths.InverseInitialEnergyCallerState

end

end OAI

end Source2788

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalState.lean; sha256: 97a977a6b16e446aefe0d751225efce2bd14925df0b98b2fb7ad39eca164b1d0 -/
section Source2789
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

def fullPunctureWidth (Z:ℝ)(t:Ideal O)(j:O):ℝ :=
  Real.logb Z (Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)

theorem full_puncture_width_exact (Z:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0):
    0≤fullPunctureWidth Z t j ∧
      ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) := by
  have hn:(1:ℝ)≤Ideal.absNorm (Ideal.span {j*primaryGenerator t}) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  constructor
  · unfold fullPunctureWidth Real.logb
    exact div_nonneg (Real.log_nonneg hn) (Real.log_pos hZ).le
  · rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (zero_lt_one.trans_le hn)).symm

theorem full_product_width_bound (Z P G η:ℝ)(hZ:1<Z)(t:Ideal O)(j:O)
    (hm:j*primaryGenerator t≠0)
    (hspan:Ideal.span {j*primaryGenerator t}=t*Ideal.span {j})
    (ht:(t.absNorm:ℝ)≤Z^(P+2*η))
    (hj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η)):
    fullPunctureWidth Z t j≤P+G+3*η := by
  have hz:=zero_lt_one.trans hZ
  have hpos:0<(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ):=by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hm))
  have hb:(Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)≤Z^(P+G+3*η):=by
    rw [hspan,map_mul,Nat.cast_mul]
    apply (mul_le_mul ht hj (by positivity) (Real.rpow_nonneg hz.le _)).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  unfold fullPunctureWidth Real.logb
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  simpa only [Real.log_rpow hz] using Real.log_le_log hpos hb

theorem physical_row_width_le (m r z G B θ H η τ:ℝ)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    θ+H+2*η≤ initialM m r z G (B-θ) η τ := by
  unfold radialCenter at hcut
  unfold initialM
  linarith

theorem enlarged_initial_margins (m r z G B θ v H η τ Q c₁ c₂:ℝ)
    (h₁:r+2*z≤m-c₁)(h₂:2*r+8*z≤3*m-c₂)
    (hG:0≤G)(hP:-2*η≤B-θ)(hQ:Q≤B-θ+G+3*η)
    (hc:0≤min c₁ c₂)(hη:0≤η)(hηsmall:η≤min c₁ c₂/100)
    (hτ:τ≤min c₁ c₂/100)
    (hcut:radialCenter m H θ (r+z-2*G) B≤4*η+τ):
    CanonicalMargins
      (max 0 (r+z-2*G-B-v)+(θ+v+2*η)) (θ+H+2*η) Q (z-G)
      (3*min c₁ c₂/4) := by
  have hd:0≤max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v):=
    sub_nonneg.mpr (le_max_right _ _)
  have hh:=initial_margins (delta:=max 0 (r+z-2*G-B-v)-(r+z-2*G-B-v))
    h₁ h₂ hG hP hQ hc hd hηsmall hτ
  have hr:=physical_row_width_le m r z G B θ H η τ hcut
  unfold CanonicalMargins at hh ⊢
  unfold initialF at hh
  constructor <;> linarith [hh.1,hh.2]

theorem enlarged_label_exact (N V η:ℝ)(hV:0≤V+2*η):
    max 0 (V+2*η)=V+2*η ∧
      N+max 0 (V+2*η)-(N+V)=2*η := by
  rw [max_eq_right hV]
  exact ⟨rfl,by ring⟩

theorem assigned_label_weight_le {σ:Type*}[DecidableEq σ]
    (slots J₁ J₂:Finset σ)(K:ℕ)(hK:slots.card≤K)
    (h₁:J₁⊆slots)(h₂:J₂⊆slots)(f:Ideal O)(hf:f≠0):
    ((IdealMobiusDivisorSum.idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)≤secondLabelWeight K f := by
  have hmem:(1:Ideal O)∈IdealMobiusDivisorSum.idealDivisors f:=
    (IdealMobiusDivisorSum.mem_idealDivisors hf).mpr (one_dvd _)
  have hn:(1:ℝ)≤(IdealMobiusDivisorSum.idealDivisors f).card:=by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,hmem⟩
  have hcard1:=Finset.card_le_card h₁
  have hcard2:=Finset.card_le_card h₂
  exact pow_le_pow_right₀ hn (by omega)

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end Source2789

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRetainedPhysical.lean; sha256: 77dca5b2e857f621909847e72cbfa3d867c73b96f9e2f3b14c338f97c42a781b -/
section Source2790
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedPhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseReflectedPhase InverseMoment InverseInitialClippedColumns
open CanonicalCoefficientClass ConcreteTraceCRT SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerModes
open InverseInitialQuotientGeometry InverseInitialEnergyCallerGeometry InverseInitialCanonicalState
local notation "O"=>ActualEisensteinCubic.O

theorem retained_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(Vlog:Fin 6→ℝ→ℂ)(Mlog:Fin 6→ℝ)
    (hVlog:∀i,ContDiff ℝ ∞ (Vlog i))(hSlog:∀i,HasCompactSupport (Vlog i))
    (hMlog:∀i,0≤Mlog i)(hbox:∀i y,Vlog i y≠0→|y|≤Mlog i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂)
    (cap margin eps U π:ℝ)(hcap:0≤cap)(hmargin:0<margin)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](slots:Finset σ),slots.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(a:σ→primePool F→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,1≤Hslot i)→
      (∀i∈slots,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1)→∀z:ℝ,0≤z→(∏i∈slots,Hslot i)≤Z^z→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(j:O)(D B v θ H R m η:ℝ),R≤U→0≤η→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),0<c₁→0<c₂→
      BlockSupport p (pointSource Finset.univ S) W₁ W₂ ω₁ ω₂ Vlog Z D B v θ H c₁ c₂ θ₁ θ₂→
      (∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
    ∀(labels:Finset (Ideal O))(rows:Finset O),
      (∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(θ+v+2*η))→
      rows⊆nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η))→(∀k∈rows,-k∈rows)→
      (∀x∈S,(initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource
        (unitSector p hp (InverseInitialRayAttachment.poolPrimary_primary F hF) (sourcePoint x ∅ ∅)) x))).2.2∈rows)→
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η→R=B-θ+2*η→
      (∀t∈quotientSet p S,
        j*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
        0≤fullPunctureWidth Z t j ∧
        ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
        θ+H+2*η≤cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤cap ∧
        CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η))
          (θ+H+2*η) (fullPunctureWidth Z t j) z margin)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh₁,fresh₂,hsf₁,hsf₂,hphysical⟩:=
    InverseInitialEnergyCallerReference.actual_physical_reference_bound
      W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ Vlog Mlog hVlog hSlog hMlog hbox
      ω₁ ω₂ lo b hlo hb hω₁ hω₂ hd₁ hd₂
  obtain ⟨af₁,bf₁,haf₁,hab₁,_,hs₁f⟩:=hsf₁
  obtain ⟨af₂,bf₂,haf₂,hab₂,_,hs₂f⟩:=hsf₂
  obtain ⟨J₁,B₁,hB₁,hm₁⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₁ af₁ bf₁ haf₁ (haf₁.le.trans hab₁) (subset_trans (subset_closure) hs₁f)
  obtain ⟨J₂,B₂,hB₂,hm₂⟩:=canonical_marked_energy_exists cap cap margin eps hcap hcap hmargin heps
    K fresh₂ af₂ bf₂ haf₂ (haf₂.le.trans hab₂) (subset_trans (subset_closure) hs₂f)
  let J:=J₁+J₂
  obtain ⟨Cp,hCp,hphysical⟩:=hphysical J K U π hU hπ
  refine ⟨J,B₁+B₂,by linarith,?_⟩
  intro q hq
  obtain ⟨C₁,Z₁,hC₁,hZ₁,hm₁⟩:=hm₁ q hq
  obtain ⟨C₂,Z₂,hC₂,hZ₂,hm₂⟩:=hm₂ q hq
  refine ⟨Cp*(C₁+C₂),max Z₁ Z₂,mul_pos hCp (add_pos hC₁ hC₂),lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
    S hdiv hf j D B v θ H R m η hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows hlabels hrows hneg hchild hclip hReq hstate
  have hZp:1<Z:=hZ₁.trans_le ((le_max_left _ _).trans hZ)
  have hD₁:B₁*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₁≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hD₂:B₂*Z^(cap+1)≤Dpool:=
    (mul_le_mul_of_nonneg_right (by linarith : B₂≤B₁+B₂) (Real.rpow_nonneg (by linarith) _)).trans hD
  have hmoment₁:=hm₁ Z ((le_max_left _ _).trans hZ) Dpool hD₁ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hmoment₂:=hm₂ Z ((le_max_right _ _).trans hZ) Dpool hD₂ slots hslots lists Hslot a hdis hHslot hP ha z hz hprod Ψ hΨ hperiod
  have hbound:=hphysical p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) (poolPrimary_odd F hFa)
    S hdiv hf Finset.univ Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZp hR (mul_nonneg hη (Real.log_pos hZp).le)
    c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn w hw labels rows
    (fun f hf=>(hlabels f hf).1.1) hneg hchild
    (max 0 (columnCenter D B v)+(θ+v)) (C₁+C₂) (eps+4*η) (by positivity) hclip
    (by unfold columnCenter;ring) hReq ?_
  · convert hbound using 1
    rw [show m+11*η+π+(eps+4*η)=m+15*η+π+eps by ring]
    ring
  · intro s ρ A₁ hA₁ A₂ hA₂ t ht
    obtain ⟨hm,hV,hM,hQ,hnorm,hMc,hFc,hmargin⟩:=hstate t ht
    have hweight:∀f∈labels,((idealDivisors f).card:ℝ)^(A₁.card+A₂.card+1)≤secondLabelWeight K f:=by
      intro f hf
      exact assigned_label_weight_le slots A₁ A₂ K hslots (Finset.mem_powerset.mp hA₁)
        (Finset.mem_powerset.mp hA₂) f (hlabels f hf).1.1
    have hleft:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayMinus Ψ ρ) slots (slots\A₁) lists a fresh₁ Z cap cap z margin eps C₁
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₁
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondMinus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₁
    have hright:=InverseInitialCanonicalEnergy.initial_child_from_rank p hp hcop hg Finset.univ Ψ
      (secondRayPlus Ψ ρ) slots (slots\A₂) lists a fresh₂ Z cap cap z margin eps C₂
      (max 0 (columnCenter D B v)) (θ+v) (θ+H+2*η) (fullPunctureWidth Z t j) η K J₂
      (j*primaryGenerator t) hZp ((show IsBaseRayTwist Ψ Ψ from Or.inl rfl).secondPlus ρ) hm
      (le_max_left _ _) hV hM hQ hMc hFc hmargin hnorm Finset.sdiff_subset labels hlabels rows hrows
      _ (by intros;positivity) hweight s hmoment₂
    constructor
    · apply hleft.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega
    · apply hright.trans
      have hexp:max 0 (columnCenter D B v)+(θ+v)+eps+4*η=
        max 0 (columnCenter D B v)+(θ+v)+(eps+4*η):=by ring
      rw [hexp]
      gcongr
      · linarith
      · linarith [norm_nonneg s]
      · dsimp [J]; omega

end SevenEighths.InverseInitialRetainedPhysical

end

end OAI

end Source2790

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalDomains.lean; sha256: ded14514bbd0d95a3c4d4506757ca9c02f3f39ba19dd73e6d0dcd7ebac77efb4 -/
section Source2791
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalDomains
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerWindowGeometry
open InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerRanges
open InverseInitialEnergyCallerSource CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem window_power_bounds
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H):
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η) ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η) ∧
    ‖eisEmbedding x.frequency‖^2≤Z^(H+η) := by
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  have hpow (i:Fin 4)(r:ℝ):hi i*Z^r≤Z^(r+η):=by
    rw [Real.rpow_add hZ]
    exact (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hZ.le _)).trans_eq (mul_comm _ _)
  exact ⟨hd.trans (hpow 1 θ),hv.trans (hpow 2 v),hh.trans (hpow 3 H)⟩

include hp hcop hg in
theorem actual_window_domains
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η):
    ∀x∈coprimeSource p (windowSource p S ψ Z D B v θ H),∀u:Oˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  apply canonical_child_domains p hp hcop hg hc hpr (windowSource p S ψ Z D B v θ H)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1) Z θ v H η hZ
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_subset
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ):
    quotientSet p (coprimeSource p (windowSource p S ψ Z D B v θ H))⊆
      quotientSet p (windowSource p S ψ Z D B v θ H) :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end SevenEighths.InverseInitialCanonicalDomains

end

end OAI

end Source2791

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalStateSource.lean; sha256: d15408f6585f046597bbf4a3708a36e3d48c368416ce6302017433f977f94584 -/
section Source2792
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem live_widths_nonnegative
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H)
    (hf:x.frequency≠0):
    0≤θ+v+2*η ∧ 0≤θ+H+2*η := by
  have hz:=zero_lt_one.trans hZ
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hz hx
  have bound (a c:ℝ)(i:Fin 4)(ha:a≤hi i*Z^c):a≤Z^(c+η):=by
    apply (ha.trans (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hz.le c))).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  obtain ⟨hlabel,hrow⟩:=initial_child_enclosures p hp hpr x 1 Z θ v H η hz
    (bound _ _ 1 hd) (bound _ _ 2 hv) (bound _ _ 3 hh)
  have hI:(1:ℝ)≤Ideal.absNorm (initialChild (toTuple p (sectorSource 1 x))).2.1:=by
    have hne:(initialChild (toTuple p (sectorSource 1 x))).2.1≠0:=
      mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  have hdiv:(1:ℝ)≤(sourceIdeal p x.divisor).absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _))
  have hfreq:(1:ℝ)≤‖eisEmbedding x.frequency‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hf))
  have hr:(1:ℝ)≤‖eisEmbedding (initialChild (toTuple p (sectorSource 1 x))).2.2‖^2:=by
    rw [initial_child_row_norm p hp hpr]
    exact one_le_mul_of_one_le_of_one_le hdiv hfreq
  constructor
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hI.trans hlabel)
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hr.trans hrow)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_full_puncture
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(D v H aC bC ad bd Z B θ η G:ℝ)(hZ:1<Z)
    (hC:Function.support (ψ 0)⊆Set.Icc aC bC)
    (hd:Function.support (ψ 1)⊆Set.Icc ad bd)
    (hCup:bC≤Z^η)(hdlo:Z^(-η)≤ad)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (j:O)(hj:j≠0)(hnj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η))
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H)):
    j*primaryGenerator t≠0 ∧ 0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    fullPunctureWidth Z t j≤B-θ+G+3*η := by
  have hspan:=span_source_puncture p hp (windowSource p S ψ Z D B v θ H) hpr j ht
  have ht0:=quotientSet_nonzero p hp (windowSource p S ψ Z D B v θ H) t ht
  have hm:j*primaryGenerator t≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [hspan]
    exact mul_ne_zero ht0 (Ideal.span_singleton_eq_bot.not.mpr hj)
  have hret:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hnt:=retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv t hret
  obtain ⟨hn,he⟩:=full_puncture_width_exact Z hZ t j hm
  exact ⟨hm,hn,he,full_product_width_bound Z (B-θ) G η hZ t j hm hspan hnt hnj⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end Source2792

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalStateWindow.lean; sha256: c612508352057856ddb3b66e711b0701169fb499bba9101732ea17788aac9b49 -/
section Source2793
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_window_state
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (h₁:r+2*assignedCenter all z≤m-c₁)
    (h₂:2*r+8*assignedCenter all z≤3*m-c₂)
    (hc:0≤min c₁ c₂)(hηsmall:η≤min c₁ c₂/100)(hτ:τ≤min c₁ c₂/100)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryGenerator t≠0 ∧ 0≤N ∧ 0≤V ∧ 0≤M ∧
    0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    CanonicalMargins (N+V) M (fullPunctureWidth Z t j)
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2) ∧
    N+V≤r+assignedCenter all z+7*η ∧
    M≤r+assignedCenter all z+7*η ∧
    N+V-(N+(θ+v))=2*η := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hmg:=enlarged_initial_margins m r (assignedCenter all z) (assignedCenter assigned z)
    B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q)) c₁ c₂
    h₁ h₂ hreg.1 hP hQ hc hη hηsmall hτ (by simpa only [hD] using hcut)
  rw [←hD,hreg.2.2] at hmg
  have hactual:CanonicalMargins (max 0 (D-B-v)+(θ+v+2*η)) (θ+H+2*η)
      (fullPunctureWidth Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2):=by
    unfold CanonicalMargins at hmg ⊢
    constructor <;> linarith [hmg.1,hmg.2]
  have hF:max 0 (D-B-v)+(θ+v+2*η)≤r+assignedCenter all z+7*η:=by
    rw [hD] at hclip ⊢
    linarith [hreg.1]
  have hMF:θ+H+2*η≤max 0 (D-B-v)+(θ+v+2*η):=by
    have hh:=hactual.1
    linarith [hreg.2.1]
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hactual,hF,hMF.trans hF,by ring⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI

end Source2793

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerFixedWindows.lean; sha256: 8a4f7197d64519ec0b0bf06628e83d2372776b57809eb2c539a09c5de0c7b14e -/
section Source2794
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerFixedWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseSecondChildWindows InverseSecondProfileUniform
local notation "Eis"=>ActualEisensteinCubic.O

theorem log_source_support (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W) :
    Function.support (CubicReflectionKernel.logSchwartz W a b ha hs hW)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hh := hs hx
  change a≤Real.exp x ∧ Real.exp x≤b at hh
  have hl := Real.log_le_log ha hh.1
  have hu := Real.log_le_log (Real.exp_pos x) hh.2
  rw [Real.log_exp] at hl hu
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem exists_actual_initial_windows
    (W₁ W₂:ℝ→ℂ)(a b bcap:ℝ)(ha:0<a)(hcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a b)(hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i) :
    ∃(wFresh:𝓢(ℝ,ℂ))(V:Fin 6→𝓢(ℝ,ℂ))(M:Fin 6→ℝ)(af bf:ℝ),
      0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (V i:ℝ→ℂ)) ∧
      (∀i,Function.support (V i)⊆Set.Icc (-M i) (M i)) ∧
      ∀{ι:Type*}[DecidableEq ι](p:ι→Eis)(_hp:∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
      (_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (ψ:Fin 4→ℝ→ℂ)(_hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
      (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ),0<Z→1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
      BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
        W₁ W₂ wFresh wFresh (fun i=>V i) Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  let m:=|Real.log a|+|Real.log b|
  obtain ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,hw,hcut⟩ :=
    fixed_windows m bcap lo hi (fun _=>0) (by dsimp [m];positivity) hcap hlo hhi (by simp)
  refine ⟨wFresh,V,M,af,bf,haf,hab,hwc,hws,hM,hVc,hVs,?_⟩
  intro ι _ p hp _ pool S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂ hZ hc₁ hb₁ hc₂ hb₂
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  have hg₁ : Function.support g₁⊆Set.Icc (-m) m := log_source_support W₁ a b ha hs₁ hW₁
  have hg₂ : Function.support g₂⊆Set.Icc (-m) m := log_source_support W₂ a b ha hs₂ hW₂
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0<relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  have hblock (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i:Fin 4,relativeNorm (coordinates p x) Z D B v θ H (outerIndex i)∈Set.Icc (lo i) (hi i) :=
    fun i=>hψ i (windowSource_four_nonzero p pool S ψ Z D B v θ H hx i)
  refine ⟨?_,?_,?_⟩
  · intro x hx hn
    have he := hw g₁ hg₁ c₁ θ₁ _ _ _ hc₁ hb₁ (hblock x hx 0) (hblock x hx 2) (hpos x hx 4) ?_
    · rw [relative_column_left] at he
      rw [he,star_one]
    · change positiveSource g₁ c₁ θ₁
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 4)≠0
      dsimp only [g₁]
      rw [positiveSource_logSchwartz W₁ a b ha hs₁ hW₁ (zero_lt_one.trans_le hc₁)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 4))]
      exact hn
  · intro x hx hn
    have he := hw g₂ hg₂ c₂ θ₂ _ _ _ hc₂ hb₂ (hblock x hx 0) (hblock x hx 2) (hpos x hx 5) ?_
    · rwa [relative_column_right] at he
    · change positiveSource g₂ c₂ θ₂
        (relativeNorm (coordinates p x) Z D B v θ H 0 *
          relativeNorm (coordinates p x) Z D B v θ H 2 *
          relativeNorm (coordinates p x) Z D B v θ H 5)≠0
      dsimp only [g₂]
      rw [positiveSource_logSchwartz W₂ a b ha hs₂ hW₂ (zero_lt_one.trans_le hc₂)
        (mul_pos (mul_pos (hpos x hx 0) (hpos x hx 2)) (hpos x hx 5))]
      exact hn
  · intro x hx hl hr i
    have hl' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 4)≠0 := by
      rw [relative_column_left]
      exact star_ne_zero.mp hl
    have hr' : wFresh (relativeNorm (coordinates p x) Z D B v θ H 5)≠0 := by
      rwa [relative_column_right]
    have he := hcut (relativeNorm (coordinates p x) Z D B v θ H) (fun _=>0)
      (by simp) (hblock x hx) hl' hr' i
    simpa only [add_zero,relativeLog] using he

end SevenEighths.InverseInitialEnergyCallerFixedWindows

end

end OAI

end Source2794

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerEmpty.lean; sha256: 01878a53a25bba0eafb48cc5a09d78b6b8a2b3460f67cb90b5944c9eb567fb8c -/
section Source2795
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerEmpty
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_zero_of_fresh_empty
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (he:freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅) :
    physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  have hv:=pointSource_valid pool S hdiv hf x hx
  have hleft:x.left⊆pool := by
    obtain ⟨s,hs,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  have hω:ω₁ (columnRatio p x.left Z D B v)=0 := by
    by_contra hn
    rw [columnRatio_actual] at hn
    have hm:= (mem_freshColumns p pool ω₁ (Z^(columnCenter D B v)) x.left).mpr ⟨hleft,hn⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hW:clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 *
        relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)=0 := by
    by_contra hn
    have hh:=hs.1 x hx hn
    simp only [hω,star_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j marks _ _ Φ Z D m x hv ρ,
    physicalKernel_nominal _ _ Φ hZ D B v m θ H _ (coordinates_pos p hp x hv)]
  change w x*(_*(_*secondNormProfile _ _ _ _ _
    (relativeNorm (coordinates p x) Z D B v θ H)))=0
  simp only [secondNormProfile,hW,mul_zero,zero_mul,zero_div]

include hp hcop hg in

theorem physical_nonzero_clipping
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂ a b η:ℝ)(hZ:1<Z)(hb:1≤b)
    (hω:Function.support ω₁⊆Set.Icc a b)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (ht:Real.log b≤3*η*Real.log Z)
    (hn:physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m≠0) :
    0≤max 0 (columnCenter D B v)-columnCenter D B v ∧
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η := by
  apply freshColumns_initial_clipping_shift p hp pool ω₁ a b Z (columnCenter D B v) η hZ hb hω _ ht
  by_contra he
  have he':freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅:=Finset.not_nonempty_iff_eq_empty.mp he
  exact hn (physicalBlock_zero_of_fresh_empty p hp hcop hg hpr pool S hdiv hf w Ψ j marks
    W₁ W₂ ω₁ ω₂ V Φ Z D B v θ H m c₁ c₂ θ₁ θ₂ (zero_lt_one.trans hZ) hs he')

end SevenEighths.InverseInitialEnergyCallerEmpty

end

end OAI

end Source2795

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialRetainedWindow.lean; sha256: f0a00fec29a9881ac8531b98cbe5cae3eae639d5e0b839affccedb9064e53d81 -/
section Source2796
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedWindow
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState InverseInitialEnergyCallerState FirstPassCubeLabels
local notation "O"=>ActualEisensteinCubic.O

theorem retained_window_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (cap gap eps U π:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree Tclip:ℝ,1≤Btree ∧ 0≤Tclip ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
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
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(ψ:Fin 4→ℝ→ℂ),(∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))→
    ∀(D B v θ H m r η τ:ℝ),0≤η→η≤gap/50→τ≤gap/50→
      (∀i,hi i≤Z^η)→Z^(-η)≤lo 1→Tclip≤3*η*Real.log Z→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→B-θ+2*η≤U→
      radialCenter m H θ D B≤4*η+τ→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ (windowSource p S ψ Z D B v θ H))
        (w∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨fresh,Vlog,Mlog,af,bf,haf,hab,hfc,hfs,hM,hVc,hVs,hwindow⟩:=
    InverseInitialEnergyCallerFixedWindows.exists_actual_initial_windows
      W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ lo hi hlo hhi
  have hfs':Function.support (fresh:ℝ→ℂ)⊆Set.Icc af (max 1 bf):=by
    intro x hx
    have h:=hfs (subset_closure hx)
    exact ⟨h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨J,Btree,hBtree,hbound⟩:=InverseInitialRetainedPhysical.retained_physical_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ (fun i=>Vlog i) Mlog
    (fun i=>(Vlog i).smooth ⊤) hVc hM (fun i y hy=>abs_le.mpr (hVs i hy))
    fresh fresh af (max 1 bf) haf (le_max_left _ _) hfs' hfs' (fresh.smooth ⊤) (fresh.smooth ⊤)
    cap gap eps U π hcap hgap heps hU hπ K
  refine ⟨J,Btree,Real.log (max 1 bf),hBtree,Real.log_nonneg (le_max_left _ _),?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf ψ hψ
    D B v θ H m r η τ hη hηsmall hτ hhiZ hloZ hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent hR hrad
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hprimary:=InverseInitialRayAttachment.poolPrimary_primary F hFa
  let Sw:=windowSource p S ψ Z D B v θ H
  let Sc:=coprimeSource p Sw
  have hdivw:∀x∈Sw,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfw:∀x∈Sw,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdivw x (Finset.mem_filter.mp hx).1
  have hfc':∀x∈Sc,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
  have hswhole:=hwindow p hp Finset.univ S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
    (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
  have hpoint:pointSource Finset.univ Sc⊆pointSource Finset.univ Sw:=by
    intro x hx
    obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
  have hsupport:BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
    ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
      fun x hx=>hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Sc) (w∘erasePoint) Ψ
      (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
    Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt:quotientSet p Sc⊆quotientSet p Sw:=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hn:∀t∈quotientSet p Sc,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
    intro t ht
    exact retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
      (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
      (hψ 0) (hψ 1) (hhiZ 0) hloZ hdiv t
      (window_quotient_subset_retained p S ψ Z D B v θ H (hqt ht))
  have hstates:∀t∈quotientSet p Sc,
      assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
      0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
      ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
        Z^(fullPunctureWidth Z t (assignedElement assigned qelem)) ∧
      θ+H+2*η≤cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤cap ∧
      CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η)) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (assignedCenter (all\assigned) z+η) gap:=by
    intro t ht
    have hs:=actual_window_state p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
      hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
      m r τ (2*gap) (2*gap) hDeq hmargin₁ hmargin₂ (by simp;positivity)
      (by simp only [min_self];linarith) (by simp only [min_self];linarith) hrad hclip
    simp only [min_self] at hs
    obtain ⟨hm,hN,hV,hM,hQ,he,hmargin,hF,hMr,hshift⟩:=hs
    refine ⟨hm,hV,hM,hQ,he,hMr.trans hparent,hF.trans hparent,?_⟩
    convert hmargin using 1 <;> simp [columnCenter]
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
    (assignedCenter (all\assigned) z+η) (by apply add_nonneg _ hη;exact Finset.sum_nonneg (fun i hi=>hz i (Finset.mem_sdiff.mp hi).1))
    hprod Ψ hΨ hperiod Sc hdivc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
    hR hη c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx=>hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
    (fun f hf=>mem_idealRange.mp hf) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates
  · intro k hk
    exact (child_ball_neg _ k).mpr hk
  · intro x hx
    exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
      hprimary S hdiv hf ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

end SevenEighths.InverseInitialRetainedWindow

end

end OAI

end Source2796

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssembly.lean; sha256: b3e3bf3a42e77127aa1bd8deaf4679dd40ab8ad3909fc16bfe01cbe1f2ebd0a0 -/
section Source2797
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

abbrev Windows (a b : Fin 4→ℝ) := ∀ i:Fin 4,↥(indices (a i) (b i))

def exponent (Z:ℝ) (k:ℤ) : ℝ := Real.logb Z (dyadicScale k)

def cutoff : Fin 4→ℝ→ℂ := fun _ y=>(annulus y:ℂ)

def weight (k:Fin 4→ℤ) (q:Fin 4→ℝ) : ℂ :=
  ∏i:Fin 4,(dyadicWeight (k i) (q i):ℂ)

theorem exponent_scale (Z:ℝ) (hZ:1<Z) (k:ℤ) :
    Z^(exponent Z k)=dyadicScale k :=
  Real.rpow_logb (by positivity) (ne_of_gt hZ) (dyadicScale_pos k)

theorem weight_partition (a b q:Fin 4→ℝ) (ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    (∑k:Windows a b,weight (fun i=>(k i).val) q)=1 := by
  unfold weight
  rw [←Fintype.prod_sum (fun (i:Fin 4) (k:↥(indices (a i) (b i)))=>(dyadicWeight k.val (q i):ℂ))]
  have he (i:Fin 4) : (∑k:↥(indices (a i) (b i)),(dyadicWeight k.val (q i):ℂ))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun k=>(dyadicWeight k (q i):ℂ))]
    exact_mod_cast dyadic_partition_on_interval (a i) (b i) (q i) (ha i) (hq i)
  simp only [he,Finset.prod_const_one]

theorem weight_eq_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ) (q:Fin 6→ℝ) :
    weight k (fun i=>q (outerIndex i)) =
      outerCutoff cutoff (relativeNorm q Z D (exponent Z (k 0))
        (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))) := by
  simp [weight,Fin.prod_univ_succ,dyadicWeight,outerIndex,outerCutoff,cutoff,
    relativeNorm,secondRelativeNorm,exponent_scale Z hZ,mul_assoc]

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceNorms (x:Source (ι:=ι) 0) : Fin 4→ℝ :=
  fun i=>coordinates p (sourcePoint x ∅ ∅) (outerIndex i)

omit [DecidableEq ι] in
theorem source_weight_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ)
    (x:Source (ι:=ι) 0) :
    weight k (sourceNorms p x)=outerCutoff cutoff
      (sourceRelative p x Z D (exponent Z (k 0)) (exponent Z (k 2))
        (exponent Z (k 1)) (exponent Z (k 3))) :=
  weight_eq_cutoff Z D hZ k _

omit [DecidableEq ι] in
theorem sourceNorms_one_le (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal] (x:Source (ι:=ι) 0)
    (hf:x.frequency≠0) : ∀i,1≤sourceNorms p x i := by
  have hi (I:Ideal Eis) (hI:I≠0) : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · change 1≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hi _ (by change Ideal.span {x.frequency}≠⊥; exact Ideal.span_singleton_eq_bot.not.mpr hf)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*weight (fun i=>(k i).val) (sourceNorms p x))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨s,hsS,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply,erase_sourcePoint]
  rw [←Finset.sum_mul,←Finset.mul_sum,weight_partition a b _ ha (hs s hsS),mul_one]

theorem physicalBlock_window_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg
      (pointSource pool (windowSource p S cutoff Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))
      ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  rw [physicalBlock_partition p hp hcop hg pool S a b ha hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [source_weight_cutoff p Z D hZ]
  exact physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m w Ψ j marks W₁ W₂ Φ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2797

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyBounds.lean; sha256: d8af4e51be07dd86eabdb3a99e3434fbe4d362549c3bb861153792cc0d863cea -/
section Source2798
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windows_card_log (a b:Fin 4→ℝ)(ha:∀i,0<a i)(hab:∀i,a i≤b i) :
    (Fintype.card (Windows a b):ℝ)≤∏i:Fin 4,(3+Real.logb 2 (b i/a i)) :=
  four_indices_card_bound a b ha hab

theorem windows_card_subpower (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀a b:Fin 4→ℝ,(∀i,0<a i)→(∀i,a i≤b i)→(∀i,b i/a i≤C*Z^R)→
        (Fintype.card (Windows a b):ℝ)≤A*Z^ε :=
  four_indices_subpower C R ε hC hR hε

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def windowBlock (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(k:Fin 4→ℤ) : ℂ :=
  physicalBlock p hp hcop hg
    (pointSource pool (windowSource p S cutoff Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))
    ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))∘erasePoint)
    Ψ j marks W₁ W₂ Φ Z D m

theorem physicalBlock_norm_le_windows
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (E:ℝ)(hblock:∀k:Windows a b,
      ‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
        (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_window_partition p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k:Windows a b,E := Finset.sum_le_sum (fun k hk=>hblock k)
    _ = _ := by simp

omit p hp hcop hg [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem physicalBlock_uniform_subpower
    (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀{κ:Type*}[DecidableEq κ](p:κ→Eis)(hp:∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (pool:Finset κ)(S:Finset (Source (ι:=κ) 0))
        (a b:Fin 4→ℝ),(∀i,0<a i)→(∀i,a i≤b i)→
        (∀i,b i/a i≤C*Z^R)→
        (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))→
      ∀(w:Source (ι:=κ) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset κ→ℂ)
        (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(D m E:ℝ),0≤E→
        (∀k:Windows a b,‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
          (fun i=>(k i).val)‖≤E)→
        ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
          Ψ j marks W₁ W₂ Φ Z D m‖≤A*Z^ε*E := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower C R ε hC hR hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hcount,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro κ _ p hp _ hcop hg pool S a b ha hab hr hs w Ψ j marks W₁ W₂ Φ D m E hE hb
  exact (physicalBlock_norm_le_windows p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ E hb).trans
    (mul_le_mul_of_nonneg_right (hc a b ha hab hr) hE)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2798

/- Original source: OAI/NumberTheory/DirichletL/Inversion/InitialDyadicAssemblyLive.lean; sha256: 8d00cce7eb6ae80b74eaedde73fa199881fc442a828114745a064082b887ccc4 -/
section Source2799
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

theorem physicalBlock_live_norm
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (E:ℝ)(he:∀k:Windows a b,‖windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_norm_le_windows p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ E he

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end Source2799
