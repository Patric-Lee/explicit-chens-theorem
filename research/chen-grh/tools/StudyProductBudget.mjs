// Floating-point exploration only. This script produces no Lean theorem
// and is not imported by any proof or certificate checker.
const endpoint=Number(process.argv[2]||1000000);
if(!Number.isSafeInteger(endpoint)||endpoint<10000||endpoint>10000000)throw Error('Use an integer endpoint in [10000,10000000].');
const composite=new Uint8Array(endpoint+1);
for(let p=2;p*p<=endpoint;p++)if(!composite[p])for(let n=p*p;n<=endpoint;n+=p)composite[n]=1;
const rows=[];
for(const U of [1500,3000,5000,10000]){
 let logProduct=0,min=Infinity,minAt=0,best={logRatio:0};
 for(let p=U;p<=endpoint;p++)if(!composite[p]){
  const before=logProduct-Math.log(Math.log(p));
  if(before<min){min=before;minAt=p;}
  logProduct+=Math.log1p(1/(p-2));
  const after=logProduct-Math.log(Math.log(p));
  if(after-min>best.logRatio)best={logRatio:after-min,u:minAt,zJustAbove:p};
 }
 rows.push({U,endpoint,...best,observedAllowance:Math.expm1(best.logRatio)});
}
console.log(JSON.stringify({classification:'FLOATING_POINT_STUDY_NOT_A_PROOF',
 explanation:'Observed lower bounds on the allowance needed for all ordered prime intervals; the infinite tail is not covered.',
 targetCutoff:'3^1000000',targetH:Math.log(1000000*Math.log(3)),
 rows},null,2));
