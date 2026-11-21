import fs from 'node:fs';
const gcd=(a,b)=>{while(b){[a,b]=[b,a%b];}return a<0n?-a:a;};
const f=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}const g=gcd(n,d);return[n/g,d/g];};
const add=(a,b)=>f(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const neg=a=>[-a[0],a[1]];
const mul=(a,b)=>f(a[0]*b[0],a[1]*b[1]);
const div=(a,b)=>f(a[0]*b[1],a[1]*b[0]);
const le=(a,b)=>a[0]*b[1]<=b[0]*a[1];
const scale=f(100000000);const h=f(7,1920);const kernel=[],hat=[];
const ceilScaled=a=>{const b=mul(a,scale);return(b[0]+b[1]-1n)/b[1];};
for(let i=0;i<64;i++){
 const a=add(f(1,10),mul(h,f(i))),b=add(a,h),s=add(add(f(5),neg(mul(f(10),b))),neg(f(71,1000)));
 kernel.push(ceilScaled(div(h,mul(a,mul(s,s)))));
 let H=f(1);
 if(!le(s,f(2))){let u=add(s,neg(f(2))),term=f(1),poly=f(1);for(let k=1;k<=6;k++){term=div(mul(term,u),f(k));poly=add(poly,term);}H=div(le(s,f(3))?f(1):div(f(3),s),poly);}
 hat.push(ceilScaled(div(mul(h,H),a)));
}
const code=`import GRH14LowerFactor

noncomputable section
namespace ChenEffective.GRH14
open Real Finset
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def mediumCellStart (i : Fin 64) : ℝ := 1/10+(7/1920:ℝ)*i.val
def mediumCellRatio (i : Fin 64) : ℝ := 5-10*(mediumCellStart i+7/1920)-(71/1000:ℝ)
def mediumKernelCell (i : Fin 64) : ℝ := (7/1920:ℝ)/(mediumCellStart i*(mediumCellRatio i)^2)
def mediumExpPolynomial (u : ℝ) : ℝ := 1+u+u^2/2+u^3/6+u^4/24+u^5/120+u^6/720
def mediumHatEnvelope (s : ℝ) : ℝ :=
  if s≤2 then 1 else if s≤3 then 1/mediumExpPolynomial (s-2) else (3/s)/mediumExpPolynomial (s-2)
def mediumHatCell (i : Fin 64) : ℝ := (7/1920:ℝ)*mediumHatEnvelope (mediumCellRatio i)/mediumCellStart i
def mediumKernelCaps : Fin 64 → ℕ := ![${kernel.join(',')}]
def mediumHatCaps : Fin 64 → ℕ := ![${hat.join(',')}]

theorem medium_kernel_cell_certificate (i : Fin 64) :
    mediumKernelCell i ≤ (mediumKernelCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumKernelCell,mediumCellStart,mediumCellRatio,mediumKernelCaps]

theorem medium_hat_cell_certificate (i : Fin 64) :
    mediumHatCell i ≤ (mediumHatCaps i:ℝ)/100000000 := by
  fin_cases i <;> norm_num [mediumHatCell,mediumCellStart,mediumCellRatio,
    mediumHatEnvelope,mediumExpPolynomial,mediumHatCaps]

theorem medium_kernel_grid_certificate : (∑ i : Fin 64, mediumKernelCell i) ≤ (1661/10000:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_kernel_cell_certificate i)
  apply hh.trans
  norm_num [mediumKernelCaps,Fin.sum_univ_succ]

theorem medium_hat_grid_certificate : (∑ i : Fin 64, mediumHatCell i) ≤ (53/100:ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 64))) => medium_hat_cell_certificate i)
  apply hh.trans
  norm_num [mediumHatCaps,Fin.sum_univ_succ]

#print axioms medium_kernel_grid_certificate
#print axioms medium_hat_grid_certificate
end ChenEffective.GRH14
`;
fs.writeFileSync(new URL('../GRH14MediumKernelCertificates.lean',import.meta.url),code);
console.log(JSON.stringify({kernelCapsSum:kernel.reduce((a,b)=>a+b,0n).toString(),hatCapsSum:hat.reduce((a,b)=>a+b,0n).toString(),scale:'100000000',cells:64}));
