import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2]||process.cwd(),dir=path.join(repo,'research/chen-grh'),out=path.join(dir,'GRHQuarterCertificates');fs.mkdirSync(out,{recursive:true});
const Z=4000000,c=new Uint8Array(Z+64);for(let p=2;p*p<c.length;p++)if(!c[p])for(let j=p*p;j<c.length;j+=p)c[j]=1;
const S=100000n,D=1000000000000n,rows=[];let total=0n;
function block(lo,w,degree){
 let count=0;for(let j=0;j<2**w;j++)if(!c[lo+2*j])count++;
 let u=BigInt(Math.floor(lo**.25*Number(S)));while((u+1n)**4n<=BigInt(lo)*S**4n)u++;while(u**4n>BigInt(lo)*S**4n)u--;
 const num=(lo<=100?126n:101n)*S**3n+(lo===3?100n*S*u*u:0n),den=100n*u**3n;
 const fac=degree===3?6n:5040n;
 const poly=t=>degree===3?6n*t*D*D+3n*t*t*D+t**3n:
 5040n*t*D**6n+2520n*t*t*D**5n+840n*t**3n*D**4n+210n*t**4n*D**3n+42n*t**5n*D*D+7n*t**6n*D+t**7n;
 const good=t=>poly(t)*den>=fac*D**BigInt(degree)*num;
 let lower=0n,upper=BigInt(Math.ceil(Math.log1p(Number(num)/Number(den))*Number(D)))+1n;
 while(!good(upper))upper*=2n;
 while(upper-lower>1n){const mid=(upper+lower)/2n;if(good(mid))upper=mid;else lower=mid;}
 return{count,u,weight:upper};
}
function shard(lo,w,degree,B){
 let packed=0n,weighted=0n;const roots=[],weights=[];
 for(let k=0;k<B;k++){const r=block(lo+2*(2**w*k),w,degree);packed|=BigInt(r.count)<<(BigInt(2**w)*BigInt(k));weighted+=BigInt(r.count)*r.weight;roots.push(r.u.toString());weights.push(r.weight.toString());}
 const id=String(rows.length).padStart(3,'0'),module='GRHQuarterCertificates.C'+id;
 const source=`import GRHQuarterMomentKernel
namespace ChenEffective.H10Band.QuarterCert.C${id}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def packed : Nat := ${packed}
def data : List (Nat×Nat) := [${roots.map((r,i)=>'('+r+','+weights[i]+')').join(',')}]
theorem counts_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts ${lo} ${w} ${B}) packed=true := by
  decide +kernel
theorem bounds_checked : QuarterCert.boundsCheck ${lo} ${w} ${degree} ${B} data=true := by
  decide +kernel
theorem weighted_checked : Nat.beq (QuarterCert.weightedSum ${w} packed data) ${weighted}=true := by
  decide +kernel
end ChenEffective.H10Band.QuarterCert.C${id}
`;
 fs.writeFileSync(path.join(out,'C'+id+'.lean'),source);
 rows.push({module,lo,w,degree,B,upper:lo+2*2**w*B-1,numerator:weighted.toString(),sourceHash:crypto.createHash('sha256').update(source).digest('hex')});total+=weighted;
}
for(let k=0;k<4999;k+=256)shard(3+2*k,0,7,Math.min(256,4999-k));
const highB=Math.ceil((Z-10001+1)/32);
for(let k=0;k<highB;k+=256)shard(10001+32*k,4,3,Math.min(256,highB-k));
if(100n*total>1799n*D)throw Error('Proposed cap does not fit');
const data={classification:'GENERATED_QUARTER_MOMENT_PROPOSALS_NOT_KERNEL_CHECKED',endpoint:Z,denominator:D.toString(),numerator:total.toString(),logCap:'1799/100',rows};
fs.writeFileSync(path.join(dir,'GRHQuarterMomentData.json'),JSON.stringify(data,null,2)+'\n');
fs.writeFileSync(path.join(dir,'GRHQuarterCounts.lean'),rows.map(r=>'import '+r.module).join('\n')+'\n');
fs.writeFileSync(path.join(out,'.gitattributes'),'*.lean text eol=lf\n');
console.log(JSON.stringify({shards:rows.length,weightedNumerator:total.toString(),denominator:D.toString(),proposedLogCap:Number(total)/Number(D),small:rows[0].module,firstHigh:rows.find(r=>r.w===4).module}));
