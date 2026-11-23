// Numerical planning only. All theorem inputs must be independently proved
// in Lean. No optimizer output is accepted as an axiom or proof certificate.
import fs from 'node:fs';
const rootMoment=465,densityExponent=476;
const ceil=(x,s)=>Math.ceil(x*s)/s;
function mediumCaps(g){
  const h=7/1920,poly=x=>1+x+x*x/2+x**3/6+x**4/24+x**5/120+x**6/720;
  let kernel=0,hat=0;
  for(let i=0;i<64;i++){
    const a=.1+h*i,s=5-10*(a+h)-g;
    kernel+=h/(a*s*s);
    hat+=h/a*(s<=2?1:s<=3?1/poly(s-2):3/s/poly(s-2));
  }
  return {kernel:ceil(kernel+.000002,1000),hat:ceil(hat+.000002,100)};
}
function evaluate(L,theta,delta){
  const g=ceil(10*(theta+delta)+10*Math.log(2)/L,1000);
  const caps=mediumCaps(g),K=ceil(1/(1/8-delta/4-1.5/L),10000);
  const baseLoss=ceil(.41*g+12.5*.055/28+.00002,1000);
  const mediumLoss=ceil(.015*3+12.515*.0065+40*g*1.015*caps.kernel+.688325*caps.hat+.002,1000);
  const lower=2.6408-baseLoss-mediumLoss/2-.00005;
  const triple=K*.498+.001+38/L;
  const tests={
    presieve:Math.log(336)+6*Math.log(L)+densityExponent+Math.log(2)/2-theta*L/2<=Math.log(1e-12),
    weightedAP:Math.log(3.2e17)+7*Math.log(L)-(delta-.001)*L<=Math.log(1e-12),
    convolutionLevel:39*Math.log(L)<=delta*L,
    sourceMass:L>=10*(Math.floor(Math.sqrt(6*20000000))+3)*Math.log(3),
    upperSourceMass:L>=(40*4400+1)*Math.log(3),
    logarithmicBox:Math.log(L)<=L/16000,
    denominator:1918.5-(1/64-delta/4)*L<=-20,
    square:3e7/L**3<=.001/2,
    lowerWindow:g<=.1,
    pairMain:.49644+45/L<=.498,
    mediumMesh:196/65000+192*65000/L**2<=.0065,
    positive:lower-triple/2>0,
  };
  return {L,H:Math.log(L),theta,delta,g,K,...caps,baseLoss,mediumLoss,lower,triple,margin:lower-triple/2,tests,feasible:Object.values(tests).every(Boolean)};
}
const rows=[];
for(let L=140000;L<=210000;L+=1000)for(let t=50;t<=75;t++)for(let d=24;d<=34;d++){
  const r=evaluate(L,t/10000,d/10000);if(r.feasible)rows.push(r);
}
rows.sort((a,b)=>a.L-b.L||b.margin-a.margin);
const report={classification:'NUMERICAL_PARAMETER_STUDY_NOT_A_LEAN_PROOF',rootMoment,densityExponent,
  scope:'Existing finite certificates; compensated medium factor 40; varying truncation and distribution gap. Does not certify omitted Lean interface gates.',
  selected:evaluate(197000,31/5000,1/400),bestExploratory:rows.slice(0,10),feasibleRows:rows.length,
  selectedTheoremBudget:{cutoff:'3^180000',H:Math.log(180000*Math.log(3)),lower:2.01875,triple:4.006,margin:.01575},
};
if(process.argv[2])fs.writeFileSync(process.argv[2],JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
