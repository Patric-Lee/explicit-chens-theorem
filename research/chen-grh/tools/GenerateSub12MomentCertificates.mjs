import fs from 'node:fs';import path from 'node:path';import crypto from 'node:crypto';
const repo=process.argv[2]||process.cwd(),dir=path.join(repo,'research/chen-grh'),certdir=path.join(dir,'GRHMomentCertificates');
fs.mkdirSync(certdir,{recursive:true});if(!fs.existsSync(path.join(dir,'GRHMomentCountKernel.lean')))throw Error('Missing local certificate kernel');
const top=4000100,composite=new Uint8Array(top+1);for(let p=2;p*p<=top;p++)if(!composite[p])for(let n=p*p;n<=top;n+=p)composite[n]=1;
const roots=[10];while(roots.at(-1)<2000)roots.push(Math.min(2000,Math.ceil(roots.at(-1)*1.03)));
const gcd=(a,b)=>b?gcd(b,a%b):a,frac=(a,b)=>{let g=gcd(a,b);return[a/g,b/g]};
let bound=[20n,1n],rows=[];
for(let i=0;i<roots.length-1;i++){
 const r=roots[i],a=r*r,b=roots[i+1]**2,lo=(a+1)|1,B=Math.ceil((Math.floor((b-lo)/2)+1)/16);
 let packed=0n,count=0;for(let k=0;k<B;k++){let c=0;for(let j=0;j<16;j++)if(!composite[lo+32*k+2*j])c++;count+=c;packed|=BigInt(c)<<(16n*BigInt(k));}
 const module='GRHMomentCertificates.B'+String(i).padStart(3,'0');
 const source='import GRHMomentCountKernel\nnamespace ChenEffective.GRHSub12.MomentCertificates.B'+String(i).padStart(3,'0')+'\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\ndef packed : Nat := '+packed+'\n\ntheorem count_checked : Nat.beq (ChenEffective.PlattWindow.segmentCounts '+lo+' 4 '+B+') packed = true := by\n  decide +kernel\n\ntheorem sum_checked : Nat.beq (ChenEffective.GRHSub12.sumFields 4 packed '+B+') '+count+' = true := by\n  decide +kernel\nend ChenEffective.GRHSub12.MomentCertificates.B'+String(i).padStart(3,'0')+'\n';
 fs.writeFileSync(path.join(certdir,'B'+String(i).padStart(3,'0')+'.lean'),source);
 bound=frac(bound[0]*BigInt(r)+BigInt(count)*bound[1],bound[1]*BigInt(r));
 // Directed rounding controls generated proof arithmetic size.
 bound=frac((bound[0]*10000n+bound[1]-1n)/bound[1],10000n);
 rows.push({module,r,a,b,lo,w:4,B,count,endpoint:lo+32*B-1,bound:bound.map(String),sourceHash:crypto.createHash('sha256').update(source).digest('hex')});
}

fs.writeFileSync(path.join(dir,'GRHMomentCertificateData.json'),JSON.stringify({classification:'GENERATED_NOT_CHECKED',endpoint:4000000,rootCap:340,densityExponent:350,rows},null,2)+'\n');
let lake=fs.readFileSync(path.join(repo,'lakefile.toml'),'utf8');if(!lake.includes('"GRHMomentCountKernel"'))lake=lake.replace('globs = ["AuditGRH122Chen"','globs = ["GRHMomentCountKernel",'+rows.map(x=>JSON.stringify(x.module)).join(',')+',"AuditGRH122Chen"');fs.writeFileSync(path.join(repo,'lakefile.toml'),lake);
console.log(JSON.stringify({blocks:rows.length,rootBound:bound.map(String),first:rows[0].module,last:rows.at(-1).module,maxB:Math.max(...rows.map(x=>x.B)),totalSourceBytes:rows.reduce((s,x)=>s+fs.statSync(path.join(certdir,x.module.split('.').at(-1)+'.lean')).size,0)}));
