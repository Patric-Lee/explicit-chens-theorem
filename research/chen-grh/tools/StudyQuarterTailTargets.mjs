// Conditional diagnostics only: no analytic inequality is asserted.
import fs from 'node:fs';import path from 'node:path';
const root=path.resolve(process.argv[2]||process.cwd()),L=22026;
const ceil=(x,n=1e6)=>Math.ceil(x*n)/n;
const rows=[];
for(const Ct of [.02,.04,.05,.08,.12,.2])for(const tau of [.0001,.0002,.0005,.001,.002,.005])for(const cells of [64,128,256]){
 const sigma=.25,M=17.99;
 const theta=ceil((M+Math.log(Ct)+2*Math.log(L)+Math.log(1/tau)+sigma*Math.log(2))/(sigma*L),1e5);
 const delta=ceil((Math.log(10)+4*Math.log(L)+Math.log(1/tau))/L,1e5);
 const g=ceil(10*(theta+delta)+10*Math.log(2)/L,1000);
 if(g>.1)continue;
 let ik=0,ih=0;const w=(7/30)/cells;
 for(let i=0;i<cells;i++){
  const a=.1+w*i,s=5-10*(a+w)-g,u=s-2;
  const P=1+u+u*u/2+u**3/6+u**4/24+u**5/120+u**6/720;
  ik+=w/(a*s*s);ih+=w/a*(s<=2?1:(s<=3?1:3/s)/P);
 }
 const K=ceil(1/(1/8-delta/4-1.5/L),1e4),pair=ceil(.49254+759/1e7+45/L);
 const base=ceil(.41*g+12.5*.055/28+.001+10*tau);
 const medium=ceil(.06+12.52*196/1e7+40*g*1.02*ceil(ik)+.6886*ceil(ih)+.002+10*tau);
 const lower=2.6408-base-medium/2-.00005,triple=K*pair+6e7/L**3+38/L;
 rows.push({Ct,tailPower:2,tau,cells,sigma,M,theta,delta,g,K,pair,base,medium,lower,triple,margin:lower-triple/2});
}
rows.sort((a,b)=>b.margin-a.margin);
const report={classification:'CONDITIONAL_QUADRATIC_TAIL_TARGETS_NOT_A_CHEN_PROOF',L,H:10,
 commonUnprovedDistribution:'10 L^4 exp(-delta L)',
 unprovedTail:'Ct L^2 exp(17.99) C^(-1/4)',
 caveats:['The displayed tail prefactors are targets, not established estimates.','The weighted convolution/QD distribution estimate remains unproved.','The higher-cell kernel budget and actual count propagation still require Lean proofs.'],rows};
fs.writeFileSync(path.join(root,'research/chen-grh/H10_QUADRATIC_TAIL_TARGETS.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({classification:report.classification,positive:rows.filter(r=>r.margin>0).length,best:rows.slice(0,8)},null,2));
