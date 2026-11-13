// The generated arithmetic is untrusted input; Lean checks every equality and inequality.
import fs from 'node:fs';
import {fileURLToPath} from 'node:url';
const target=process.argv[2]||fileURLToPath(new URL('./BJSSmallPrefixCertificate.lean',import.meta.url));
let source=fs.readFileSync(target,'utf8').replaceAll('\r\n','\n');
const data=source.slice(source.indexOf('def bjsSmallLogRows'),source.indexOf('def bjsSmallPrefixQ'));
const rows=[...data.matchAll(/\((\d+),\s*(\d+)(?:\/(\d+))?,\s*(\d+),\s*(\d+)(?:\/(\d+))?\)/g)].map(m=>({k:Number(m[1]),u:[BigInt(m[2]),BigInt(m[3]||1)],l:Number(m[4]),v:[BigInt(m[5]),BigInt(m[6]||1)]}));
if(rows.length!==287)throw Error('Expected 287 unchanged source rows');
const gcd=(a,b)=>{a=a<0n?-a:a;while(b){[a,b]=[b,a%b];}return a;};
const q=(n,d=1n)=>{if(d===0n)throw Error('Zero denominator');if(d<0n){n=-n;d=-d;}const g=gcd(n,d);return [n/g,d/g];};
const add=([a,b],[c,d])=>q(a*d+c*b,b*d), neg=([a,b])=>[-a,b];
const sub=(a,b)=>add(a,neg(b)),mul=([a,b],[c,d])=>q(a*c,b*d),div=([a,b],[c,d])=>q(a*d,b*c);
const pow=([a,b],n)=>q(a**BigInt(n),b**BigInt(n)),le=([a,b],[c,d])=>a*d<=c*b;
const num=n=>q(BigInt(n)),two=num(2),one=num(1);
function logUpper(r,k){const p=pow(two,k),z=div(sub(div(r,p),one),add(div(r,p),one));let s=num(0);for(let i=0;i<8;i++)s=add(s,div(pow(z,2*i+1),num(2*i+1)));return add(mul(num(k),q(6931471808n,10000000000n)),mul(two,add(s,div(pow(z,17),sub(one,pow(z,2))))));}
const prime=n=>{if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true;};
const values=[];let total=num(0);
for(let n=0;n<287;n++){
 if(prime(n))total=add(total,q(1n,BigInt(n)));values.push(total);
 if(n<2)continue;const {k,u,l,v}=rows[n];
 const tests=[le(pow(two,k),num(n+1)),le(logUpper(num(n+1),k),u),le(pow(two,l),u),le(logUpper(u,l),v),le(one,u),le(sub(add(v,q(27n,100n)),div(one,mul(two,pow(u,2)))),total)];
 if(tests.some(x=>!x))throw Error('Existing row fails exact rational check: '+n+' '+tests);
}
const rat=([n,d])=>`((${n} : ℚ)/${d})`;
const name=n=>String(n).padStart(3,'0');
let out=`set_option Elab.async false\n\nprivate theorem bjsSmallPrefixQ_step (n : ℕ) :\n    bjsSmallPrefixQ (n+1) = bjsSmallPrefixQ n +\n      (if (n+1).Prime then 1/((n+1 : ℕ) : ℚ) else 0) := by\n  unfold bjsSmallPrefixQ\n  rw [Finset.sum_range_succ]\n\n`;
for(let n=0;n<287;n++){
 out+=`private theorem bjsSmallPrefixQ_value${name(n)} : bjsSmallPrefixQ ${n} = ${rat(values[n])} := by\n`;
 out+=n===0?'  norm_num [bjsSmallPrefixQ]\n\n':`  rw [bjsSmallPrefixQ_step ${n-1}, bjsSmallPrefixQ_value${name(n-1)}]\n  norm_num\n\n`;
}
for(let n=2;n<287;n++){
 const {k,u,l,v}=rows[n],U=rat(u),V=rat(v);
 out+=`private theorem bjsSmallPrefixRow${name(n)} : bjsSmallPrefixCertificate ${n} := by\n  change (2 : ℚ)^${k} ≤ (${n} : ℚ)+1 ∧\n    bjsLogUpper ((${n} : ℚ)+1) ${k} ≤ ${U} ∧\n    (2 : ℚ)^${l} ≤ ${U} ∧ bjsLogUpper ${U} ${l} ≤ ${V} ∧\n    1 ≤ ${U} ∧ ${V}+27/100-1/(2*${U}^2) ≤ bjsSmallPrefixQ ${n}\n  rw [bjsSmallPrefixQ_value${name(n)}]\n  norm_num [bjsLogUpper, Finset.sum_range_succ]\n\n`;
}
out+='theorem bjsSmallPrefixCertificates :\n    ∀ n : Fin 287, 2 ≤ n.val → bjsSmallPrefixCertificate n.val := by\n  intro n hn\n  fin_cases n\n  · norm_num at hn\n  · norm_num at hn\n';
for(let n=2;n<287;n++)out+=`  · exact bjsSmallPrefixRow${name(n)}\n`;
out+='\nend ChenEffective\n';
const start=source.includes('set_option Elab.async false')?source.indexOf('set_option Elab.async false'):source.indexOf('theorem bjsSmallPrefixCertificates');
if(start<0)throw Error('Missing source proof boundary');
source=source.slice(0,start)+out;
if(!source.includes('import Mathlib.Tactic.NormNum.Prime'))source='import Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.FinCases\n'+source;
fs.writeFileSync(target,source);
console.log(JSON.stringify({rows:rows.length,exactRationalChecks:285,prefixValues:287,generatedBytes:source.length,requiresLeanKernelCheck:true}));
