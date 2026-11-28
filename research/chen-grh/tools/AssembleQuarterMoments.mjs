import fs from 'node:fs';
import path from 'node:path';
const root=path.resolve(process.argv[2]||process.cwd());
const data=JSON.parse(fs.readFileSync(path.join(root,'research/chen-grh/GRHQuarterMomentData.json'),'utf8'));
const out=path.resolve(process.argv[3]||path.join(root,'research/chen-grh'));fs.mkdirSync(out,{recursive:true});
const header=`\nnoncomputable section\nnamespace ChenEffective.H10Band\nopen Real Finset QuarterCert\nset_option maxHeartbeats 6000000\nset_option maxRecDepth 100000\nset_option backward.isDefEq.respectTransparency false\n`;
const groups=[];
for(let i=0;i<data.rows.length;i+=32){
 const rows=data.rows.slice(i,i+32),name='GRHQuarterGroup'+String(i/32).padStart(2,'0');
 const total=rows.reduce((a,r)=>a+BigInt(r.numerator),0n);
 let s='import GRHQuarterMomentSoundness\n'+rows.map(r=>'import '+r.module).join('\n')+header;
 s+=`\ntheorem ${name}_bound (F : Finset ℕ) (hF : ∀ p∈F,p.Prime) :\n envelopePrefix F ${rows.at(-1).upper} ≤ envelopePrefix F ${rows[0].lo-1}+(${total}:ℝ)/denominator := by\n`;
 for(let j=0;j<rows.length;j++){
  const r=rows[j],n=r.module.replace('GRHQuarterCertificates.','');
  s+=`  have h${j} : envelopePrefix F ${r.upper} ≤ envelopePrefix F ${r.lo-1}+(${r.numerator}:ℝ)/denominator :=\n    certified_envelope_prefix F hF (lo:=${r.lo}) (w:=${r.w}) (degree:=${r.degree}) (B:=${r.B})\n      (by norm_num) (by norm_num) (by norm_num [PsiFinite.baseCover])\n      ${n}.data ${n}.counts_checked ${n}.bounds_checked ${n}.weighted_checked\n`;
 }
 let round=rows.map((r,j)=>({h:'h'+j,a:r.lo-1,b:r.upper,n:BigInt(r.numerator)})),k=0;
 while(round.length>1){const next=[];for(let j=0;j<round.length;j+=2){if(j+1===round.length){next.push(round[j]);continue;}const a=round[j],b=round[j+1];if(a.b!==b.a)throw Error('gap');const h='m'+k++,n=a.n+b.n;s+=`  have ${h} : envelopePrefix F ${b.b} ≤ envelopePrefix F ${a.a}+(${n}:ℝ)/denominator := by\n    dsimp only [denominator] at ${a.h} ${b.h} ⊢\n    linarith only [${a.h},${b.h}]\n`;next.push({h,a:a.a,b:b.b,n});}round=next;}
 s+=`  exact ${round[0].h}\n\n#print axioms ${name}_bound\nend ChenEffective.H10Band\nend\n`;
 fs.writeFileSync(path.join(out,name+'.lean'),s);groups.push({name,a:rows[0].lo-1,b:rows.at(-1).upper,n:total});
}
let s=groups.map(g=>'import '+g.name).join('\n')+header;
s+=`\n/-- Kernel-certified real logarithmic Euler envelope, through four million. -/\ntheorem quarter_prime_envelope_cap (F : Finset ℕ)\n (hF : ∀ p∈F,p.Prime ∧ 2<p ∧ p≤4000000) :\n (∑ p∈F,primeEnvelope p) ≤ (1799/100:ℝ) := by\n  classical\n  have hp : ∀ p∈F,p.Prime := fun p h => (hF p h).1\n`;
for(let i=0;i<groups.length;i++)s+=`  have h${i} := ${groups[i].name}_bound F hp\n`;
s+=`  have hstart : envelopePrefix F 2=0 := by\n    unfold envelopePrefix\n    apply sum_eq_zero\n    intro p hp\n    have hf := mem_filter.mp hp\n    have := (hF p hf.1).2.1\n    omega\n  have hend : envelopePrefix F ${groups.at(-1).b}=∑ p∈F,primeEnvelope p := by\n    unfold envelopePrefix\n    congr 1\n    apply filter_eq_self.mpr\n    intro p hp\n    have := (hF p hp).2.2\n    omega\n  dsimp only [denominator] at *\n  rw [hstart] at h0\n  rw [hend] at h${groups.length-1}\n  linarith only [${groups.map((_,i)=>'h'+i).join(',')}]\n\n#print axioms quarter_prime_envelope_cap\nend ChenEffective.H10Band\nend\n`;
fs.writeFileSync(path.join(out,'GRHQuarterPrimeEnvelope.lean'),s);
console.log(JSON.stringify({groups:groups.length,leaves:data.rows.length,total:data.numerator,output:out}));
