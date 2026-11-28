// Finite-band experiment. Numerical fits are not actual Chen estimates.
import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const dir=path.join(process.cwd(),'research/chen-grh'),sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const studyBytes=fs.readFileSync(path.join(dir,'SPECIALIZED_FINITE_SCALE_STUDY.json')),study=JSON.parse(studyBytes);
const audit=JSON.parse(fs.readFileSync(path.join(dir,'FINAL_GRHSub12_CHEN_AUDIT.json')));
if(study.baseline.manifest!==audit.sourceObjectManifestHash)throw Error('Study has a different checked baseline');
const endpoints=[22026];while(endpoints.at(-1)<159500)endpoints.push(Math.min(159500,Math.ceil(endpoints.at(-1)*101/100)));
const ceil=(x,n=1e6)=>Math.ceil(x*n)/n;
const eta=L=>(255/L+2400/L**2)*Math.exp(-L/160); // new, slightly looser proved bridge
function profile(g,error){let ik=0,ih=0;const w=7/1920;for(let i=0;i<64;i++){
 const a=.1+w*i,s=5-10*(a+w)-g,u=s-2,P=1+u+u*u/2+u**3/6+u**4/24+u**5/120+u**6/720;
 if(s<=0)return null;ik+=w/(a*s*s);ih+=w/a*(s<=2?1:(s<=3?1:3/s)/P);
 }return{ik:ceil(ik+64*error),ih:ceil(ih+64*error)};}
const packages=[
 {id:'published_envelopes_diagnostic',z:4000000,half:true,Ct:336,pt:6,Cd:3.2e17,pd:7,kappa:.001,tau:1e-12,Pan:true,interval:'inverse_log'},
 {id:'prime_mass_cleanup_half_moment',z:4000000,half:true,Ct:102,pt:4,Cd:3.2e17,pd:7,kappa:.001,tau:1e-4,Pan:true,interval:'retained_power'},
 {id:'prime_mass_cleanup_variable_rankin',z:4000000,Ct:102,pt:4,Cd:3.2e17,pd:7,kappa:.001,tau:1e-4,Pan:true,interval:'retained_power'},
 {id:'H10_keep_existing_endpoint',z:4000000,Ct:16,pt:1,Cd:10,pd:4,kappa:0,tau:1e-4,Pan:false,interval:'retained_power'},
 {id:'H10_smaller_product_endpoint',z:300000,Ct:16,pt:2,Cd:10,pd:4,kappa:0,tau:1e-4,Pan:false,interval:'retained_power'},
];
function fit(A,B,p,m){
 const s=m.sigma,M=m.proposedLogCap,theta=ceil((M+Math.log(p.Ct)+p.pt*Math.log(A)+Math.log(1/p.tau)+s*Math.log(2))/(s*A),1e5);
 const delta=ceil(Math.max(p.kappa+(Math.log(p.Cd)+p.pd*Math.log(A)+Math.log(1/p.tau))/A,p.Pan?39*Math.log(A)/A:0),1e5);
 const g=ceil(10*(theta+delta)+10*Math.log(2)/A,1000);
 if(g>.1)return null;const e=p.interval==='retained_power'?eta(A):1/A**2,caps=profile(g,e);
 const den=1/8-delta/4-1.5/A;if(!caps||den<=0)return null;
 const K=ceil(1/den,1e4),nm=Math.max(1,Math.min(1e7,Math.ceil(Math.sqrt(196/(192*e))))),np=Math.max(1,Math.min(1e7,Math.ceil(Math.sqrt(759/(30*e)))));
 const medMesh=196/nm+192*nm*e,pairMesh=759/np+30*np*e+5*np*np*e*e;
 const pair=ceil(.49254+pairMesh+45/A),b=ceil(.41*g+12.5*.055/28+.001+10*p.tau);
 const med=ceil(.06+12.52*medMesh+40*g*1.02*caps.ik+.6886*caps.ih+.002+10*p.tau);
 const lower=2.6408-b-med/2-.00005,triple=K*pair+6e7/A**3+38/A,margin=lower-triple/2;
 const tailLog=Math.log(p.Ct)+p.pt*Math.log(A)+M+s*Math.log(2)-s*theta*A,apLog=Math.log(p.Cd)+p.pd*Math.log(A)-(delta-p.kappa)*A;
 const monotonic={tail:s*theta>=p.pt/A,distribution:delta-p.kappa>=p.pd/A,
  denominatorLinearSingular:1/A-(1/16-delta/4)<=0};
 if(tailLog>Math.log(p.tau)+1e-9||apLog>Math.log(p.tau)+1e-9||Object.values(monotonic).some(x=>!x))return null;
 return{lowerLog:A,upperLog:B,sigma:s,momentLogCap:M,theta,delta,g,K,pair,baseLoss:b,mediumLoss:med,lower,triple,margin,
  mediumGrid:nm,pairGrid:np,intervalError:e,tailLog,distributionLog:apLog,monotonic,
  linearSingularDenominatorLogError:Math.log(20)+1096+Math.log(10*A)+Math.log(2)/2-(1/16-delta/4)*A,
  fittedOnWholeBand:true,actualCountEstimatesProved:false};
}
const bands=endpoints.slice(0,-1).map((A,i)=>({index:i,lowerLog:A,upperLog:endpoints[i+1],
 candidates:packages.map(p=>{
  const moments=p.half?[{sigma:.5,proposedLogCap:350}]:study.moments.filter(m=>m.z===p.z);
  const fits=moments.map(m=>fit(A,endpoints[i+1],p,m)).filter(Boolean).sort((x,y)=>y.margin-x.margin);
  return{package:p.id,best:fits[0]??null,positiveModel:!!fits[0]&&fits[0].margin>0,certifiedChenBand:false};
 })}));
const summary=packages.map(p=>{
 const rows=bands.map(b=>({index:b.index,...b.candidates.find(c=>c.package===p.id)}));
 const positive=rows.filter(x=>x.positiveModel);
 return{package:p.id,positiveModelBands:positive.length,totalBands:bands.length,
  firstPositiveLog:positive[0]?.best.lowerLog??null,firstPositiveApproxH:positive[0]?Math.log(positive[0].best.lowerLog):null,
  minimumModelMargin:positive.length?Math.min(...positive.map(r=>r.best.margin)):null,
  provedInteriorBands:0};
});
const recommended=bands[0].candidates.find(c=>c.package==='H10_keep_existing_endpoint').best;
if(!recommended||recommended.margin<=0)throw Error('No positive H10 endpoint model');
if(summary.find(r=>r.package==='H10_keep_existing_endpoint').positiveModelBands!==bands.length)throw Error('Uncovered numerical band');
const report={classification:'H10_FINITE_BAND_EXPERIMENT_NOT_A_CHEN_PROOF',baselineManifest:audit.sourceObjectManifestHash,
 studyHash:sha(studyBytes),generatorHash:sha(fs.readFileSync(new URL(import.meta.url))),
 lowerH:10,lowerLog:22026,upperLog:159500,existingCutoff:'3^145000',bandCount:bands.length,
 endpoints,packages,summary,recommendedFirstBand:recommended,bands,
 boundaries:{convention:'[lowerLog,upperLog)',existingCutoffComparison:'log(3^145000) <= 159500',
  mathematicalCoverage:'All log N >= 22026 are in an interior band or N >= 3^145000. Lean cover theorem checks this independently of numerical fits.'},
 limitations:[
  'No interior Chen band is proved. Every package still needs analytic estimates for actual counts.',
  'The proposed sharp weighted distribution must include the convolution/QD remainder. Pointwise prime-AP estimates alone do not suffice.',
  'Moment log caps from the study remain uncertified proposals; variable Rankin identities do not certify their values.',
  'The 16 L and 16 L^2 aggregate tail prefactors remain unproved.',
  'Existing source-mass, singular-series and interface thresholds still require replacements.',
  'Here fitted envelopes are monotone beyond each left endpoint; finite banding organizes parameter choices but does not itself repair any analytic inequality.'
 ]};
fs.writeFileSync(path.join(dir,'H10_FINITE_BAND_EXPERIMENT.json'),JSON.stringify(report,null,2)+'\n');
const cover=`import GRHH10PrimeIntervals

/-! Exact finite-band coverage and conditional pasting with the saved cutoff.
No representation estimate inside a band is asserted. -/
noncomputable section
namespace ChenEffective.H10Band
open Real
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def bandEndpoints : Array ℕ := #[${endpoints.join(',')}]
def bandCount : ℕ := ${bands.length}
def bandEndpoint (i : ℕ) : ℝ := (bandEndpoints[i]?.getD 159500 : ℕ)

theorem endpoints_checked : bandEndpoints.size=bandCount+1 ∧
    bandEndpoints[0]?.getD 0=22026 ∧
    bandEndpoints[bandCount]?.getD 0=159500 ∧
    ∀ i : Fin bandCount, bandEndpoints[i.val]?.getD 0 < bandEndpoints[i.val+1]?.getD 0 := by
  decide +kernel

theorem first_endpoint : bandEndpoint 0=22026 := by norm_num [bandEndpoint,bandEndpoints]
theorem last_endpoint : bandEndpoint bandCount=159500 := by norm_num [bandEndpoint,bandEndpoints,bandCount]

theorem adjacent_cover {n : ℕ} (hn : 0<n) (e : ℕ→ℝ) {x : ℝ}
    (hx : e 0≤x) (ht : x<e n) : ∃ i : ℕ, i<n ∧ e i≤x ∧ x<e (i+1) := by
  let P := fun i : ℕ => i<n ∧ x<e (i+1)
  have hex : ∃ i, P i := by
    refine ⟨n-1,?_,?_⟩
    · omega
    · simpa only [Nat.sub_add_cancel (by omega : 1≤n)] using ht
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have hlow : e j≤x := by
    by_cases hz : j=0
    · simpa only [hz] using hx
    · by_contra h
      have hprev : P (j-1) := by
        constructor
        · have := hj.1; omega
        · simpa only [Nat.sub_add_cancel (by omega : 1≤j)] using (lt_of_not_ge h)
      have hm := Nat.find_min' hex hprev
      change j≤j-1 at hm
      omega
  exact ⟨j,hj.1,hlow,hj.2⟩

theorem log_band_cover {L : ℝ} (hL : 22026≤L) (hU : L<159500) :
    ∃ i : ℕ, i<bandCount ∧ bandEndpoint i≤L ∧ L<bandEndpoint (i+1) := by
  apply adjacent_cover (by norm_num [bandCount]) bandEndpoint
  · simpa only [first_endpoint] using hL
  · simpa only [last_endpoint] using hU

/-- A bridge proof for each band can be pasted with the existing cutoff.
Both the interior proofs and the saved theorem are explicit arguments. -/
theorem paste_saved_cutoff (P : ℕ→Prop)
    (hhigh : ∀ N : ℕ, 3^145000≤N → P N)
    (hbands : ∀ i : ℕ, i<bandCount → ∀ N : ℕ,
      bandEndpoint i≤log (N:ℝ) → log (N:ℝ)<bandEndpoint (i+1) → P N)
    {N : ℕ} (hN : exp (exp (10:ℝ))≤N) : P N := by
  by_cases hlarge : 3^145000≤N
  · exact hhigh N hlarge
  · have hn : (0:ℝ)<N := lt_of_lt_of_le (exp_pos _) hN
    have hlt : (N:ℝ)<((3^145000:ℕ):ℝ) := by exact_mod_cast (lt_of_not_ge hlarge)
    have hlog := (log_lt_log hn hlt).trans_le old_cutoff_log_cap
    obtain ⟨i,hi,hlo,hhi⟩ := log_band_cover (log_lower_of_double_exp_ten hN) hlog
    exact hbands i hi N hlo hhi

#print axioms endpoints_checked
#print axioms log_band_cover
#print axioms paste_saved_cutoff
end ChenEffective.H10Band
end
`;
fs.writeFileSync(path.join(dir,'GRHH10BandCover.lean'),cover);
const picks=bands.map(b=>b.candidates.find(c=>c.package==='H10_keep_existing_endpoint').best);
const ints=key=>picks.map(p=>Math.round(p[key]*1e6)).join(',');
const budget=`import GRHH10BandCover
import GRHFiniteScaleBudget

/-! Kernel-checked coefficient coupons for 199 conditional band estimates.
The coefficients are proposed analytic bounds, not proved actual counts. -/
noncomputable section
namespace ChenEffective.H10Band
open Real Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
def baseNumerators : Array ℕ := #[${ints('baseLoss')}]
def mediumNumerators : Array ℕ := #[${ints('mediumLoss')}]
def radiusNumerators : Array ℕ := #[${ints('K')}]
def pairNumerators : Array ℕ := #[${ints('pair')}]

theorem band_coefficients_checked :
    baseNumerators.size=bandCount ∧ mediumNumerators.size=bandCount ∧
    radiusNumerators.size=bandCount ∧ pairNumerators.size=bandCount ∧
    ∀ i : Fin bandCount,
      baseNumerators[i.val]?.getD 0≤68000 ∧
      mediumNumerators[i.val]?.getD 0≤1120000 ∧
      radiusNumerators[i.val]?.getD 0≤8060000 ∧
      pairNumerators[i.val]?.getD 0≤495000 := by
  decide +kernel

def baseCap (i : ℕ) : ℝ := (baseNumerators[i]?.getD 0 : ℕ)/1000000
def mediumCap (i : ℕ) : ℝ := (mediumNumerators[i]?.getD 0 : ℕ)/1000000
def radiusCap (i : ℕ) : ℝ := (radiusNumerators[i]?.getD 0 : ℕ)/1000000
def pairCap (i : ℕ) : ℝ := (pairNumerators[i]?.getD 0 : ℕ)/1000000

theorem band_caps {i : ℕ} (hi : i<bandCount) :
    baseCap i≤17/250 ∧ mediumCap i≤28/25 ∧ radiusCap i≤403/50 ∧ pairCap i≤99/200 := by
  have hc := band_coefficients_checked.2.2.2.2 ⟨i,hi⟩
  have hb : ((baseNumerators[i]?.getD 0 : ℕ):ℝ)≤68000 := by exact_mod_cast hc.1
  have hm : ((mediumNumerators[i]?.getD 0 : ℕ):ℝ)≤1120000 := by exact_mod_cast hc.2.1
  have hk : ((radiusNumerators[i]?.getD 0 : ℕ):ℝ)≤8060000 := by exact_mod_cast hc.2.2.1
  have hp : ((pairNumerators[i]?.getD 0 : ℕ):ℝ)≤495000 := by exact_mod_cast hc.2.2.2
  unfold baseCap mediumCap radiusCap pairCap
  constructor
  · linarith only [hb]
  constructor
  · linarith only [hm]
  constructor
  · linarith only [hk]
  · linarith only [hp]

theorem band_lower_coefficient {i : ℕ} (hi : i<bandCount) :
    (8051/4000:ℝ)≤3301/1250-baseCap i-mediumCap i/2-1/20000 := by
  obtain ⟨hb,hm,hk,hp⟩ := band_caps hi
  linarith only [hb,hm]

theorem band_triple_coefficient {i : ℕ} (hi : i<bandCount) {L : ℝ} (hL : 22026≤L) :
    radiusCap i*pairCap i+60000000/L^3+38/L≤3992/1000 := by
  obtain ⟨hb,hm,hk,hp⟩ := band_caps hi
  have hpp : 0≤pairCap i := by unfold pairCap; positivity
  have hprod := mul_le_mul hk hp hpp (by norm_num : (0:ℝ)≤403/50)
  have hc := FiniteScaleStudy.cost_H10 hL
  unfold FiniteScaleStudy.completeTripleCost at hc
  linarith only [hprod,hc]

/-- Uniform positivity if the proposed estimates are established for actual counts. -/
theorem positive_of_band_counts {i : ℕ} (hi : i<bandCount) {L M W T R : ℝ}
    (hL : 22026≤L) (hM : 0<M)
    (hW : (3301/1250-baseCap i-mediumCap i/2-1/20000)*M≤W)
    (hT : T≤(radiusCap i*pairCap i+60000000/L^3+38/L)*M)
    (hR : W-T/2≤R) : (67/4000:ℝ)*M≤R ∧ 0<R := by
  have hw := mul_le_mul_of_nonneg_right (band_lower_coefficient hi) hM.le
  have ht := mul_le_mul_of_nonneg_right (band_triple_coefficient hi hL) hM.le
  have hpaid : (67/4000:ℝ)*M≤R := by nlinarith only [hw,ht,hW,hT,hR]
  exact ⟨hpaid,(mul_pos (by norm_num : (0:ℝ)<67/4000) hM).trans_le hpaid⟩

#print axioms band_coefficients_checked
#print axioms positive_of_band_counts
end ChenEffective.H10Band
end
`;
fs.writeFileSync(path.join(dir,'GRHH10BandBudget.lean'),budget);
console.log(JSON.stringify({classification:report.classification,bandCount:report.bandCount,summary,recommendedFirstBand:recommended},null,2));
