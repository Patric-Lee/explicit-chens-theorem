import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt');
const out=path.join(root,'PlattAssemblyPilot');fs.mkdirSync(out,{recursive:true});
const data=JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(root,'block-relative-1e10.grid.json.gz'))));
const counts=zlib.gunzipSync(fs.readFileSync(path.join(root,'block-relative-1e10.counts.bin.gz')));
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
if(sha(counts)!==data.countSha256)throw Error('Count hash mismatch');
const S=1n<<48n;
let a=data.U,offset=0,g=0,lower=0n,upper=0n,point=0;
const prefix=[];
function record(){
 if(data.grid[point]?.x===a){prefix.push({x:a,lower,upper});point++;}
}
record();
for(;offset<counts.length/2;offset++){
 while(data.groups[g+1]?.offset===offset)g++;
 const h=2*2**data.groups[g].w,c=BigInt(counts.readUInt16LE(2*offset));
 lower+=S*c/BigInt(a+h);upper+=S*c/BigInt(a)+1n;a+=h;record();
}
if(point!==data.grid.length||a!==data.R)throw Error('Grid/block alignment failed');
const logs=[];
for(let i=0;i<Math.ceil(data.grid.length/256);i++){
 const name='C'+String(i).padStart(6,'0');
 const source=fs.readFileSync(path.join(root,'PlattCertificates/Log256',name+'.lean'),'utf8');
 for(const m of source.matchAll(/⟨(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+)⟩/g))
  logs.push({x:Number(m[1]),lower:BigInt(m[7]),upper:BigInt(m[8])});
}
if(logs.length!==prefix.length||logs.some((r,i)=>r.x!==prefix[i].x))throw Error('Log grid mismatch');
const ref=prefix.at(-1),rlog=logs.at(-1);
let minimum=0n,maximum=0n;
for(let i=0;i+1<prefix.length;i++){
 const lo=prefix[i].lower-ref.upper-logs[i+1].upper+rlog.lower;
 const hi=prefix[i+1].upper-ref.lower-logs[i].lower+rlog.upper;
 if(lo<minimum)minimum=lo;if(hi>maximum)maximum=hi;
 if(lo*20000n< -S||hi*20000n>S)throw Error('Independent cumulative budget failed at '+i);
}
const report={classification:'ASSEMBLY_PILOT_PROPOSALS_NOT_FULL_WINDOW_PROOF',points:prefix.length,cells:prefix.length-1,
 independentPrefixBudget:{lower:Number(minimum)/Number(S),upper:Number(maximum)/Number(S),allowance:1/20000},
 reference:{x:ref.x,lower:String(ref.lower),upper:String(ref.upper),logLower:String(rlog.lower),logUpper:String(rlog.upper)},batches:[]};
// Prefix arithmetic pilots: full set of grid checkpoints in selected chunks.
for(const index of [0,1,10000,70000]){
 const name='C'+String(index).padStart(6,'0'),rec=JSON.parse(fs.readFileSync(path.join(repo,'.lake/build-434/manual-certificates/Count131072',name+'.json'))),p=rec.metadata;
 let L=0n,U=0n;const cuts=[];
 const wanted=new Set(prefix.filter(r=>p.lo-1<=r.x&&r.x<=p.hi+1).map(r=>(r.x-(p.lo-1))/(2*p.W)));
 wanted.add(p.B);
 for(let k=0;k<=p.B;k++){
  if(wanted.has(k))cuts.push({k,lower:String(L),upper:String(U)});
  if(k<p.B){const c=BigInt(counts.readUInt16LE(2*(p.offset+k))),A=BigInt(p.lo-1+2*p.W*k);
   L+=S*c/(A+BigInt(2*p.W));U+=S*c/A+1n;}
 }
 const namespace='ChenEffective.PlattWindow.AssemblyPilot.'+name;
 const src=`import PlattAssemblyKernel\nimport PlattCertificates.Count131072.${name}\nnamespace ${namespace}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef cuts : List PrefixCut := [${cuts.map(c=>`⟨${c.k},${c.lower},${c.upper}⟩`).join(',\n')}]\ntheorem checked : checkPrefixCuts (2^48) ${p.lo} ${p.w} Manual.Count131072.${name}.packed ${p.B} cuts = true := by\n decide +kernel\nend ${namespace}\n`;
 fs.writeFileSync(path.join(out,name+'.lean'),src);
 report.batches.push({module:'PlattAssemblyPilot.'+name,kind:'prefix-arithmetic',index,blocks:p.B,checkpoints:cuts.length,...p});
 // Semantic adapter imports the already checked sieve; it never reruns it.
 const sound=`import PlattAssemblySoundness\nimport PlattAssemblyPilot.${name}\nnamespace ${namespace}\nopen AnalyticNumberTheory.Mertens\nset_option maxHeartbeats 3000000\ntheorem cuts_sound (c : PrefixCut) (hc : c ∈ cuts) :\n (c.lower:ℝ) ≤ (2:ℝ)^48*(primeReciprocalSum (${p.lo}-1+2*2^${p.w}*c.k)-primeReciprocalSum (${p.lo}-1)) ∧\n (2:ℝ)^48*(primeReciprocalSum (${p.lo}-1+2*2^${p.w}*c.k)-primeReciprocalSum (${p.lo}-1)) ≤ (c.upper:ℝ) := by\n have h := checked_prefix_cut checked hc\n have hcount := Nat.eq_of_beq_eq_true Manual.Count131072.${name}.count_checked\n have hh := segment_prefix_reciprocal_certificate (scale:=2^48)\n  (by norm_num : ${p.lo}%2=1) (by norm_num : 3≤${p.lo})\n  (by norm_num [PsiFinite.baseCover] : ${p.lo}+2*2^${p.w}*${p.B}-1≤PsiFinite.baseCover) h.1 hcount h.2\n simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh\n#print axioms cuts_sound\nend ${namespace}\n`;
 fs.writeFileSync(path.join(out,name+'Sound.lean'),sound);
}
// All budget numbers are checked in Lean, but the full cumulative prime bounds
// remain a separate producer obligation; no full window theorem is asserted.
for(const [start,size] of [[0,16],...Array.from({length:8},(_,i)=>[i*256,256]),[10000,256],[239500,256]]){
 const cells=[];
 for(let i=start;i<Math.min(start+size,prefix.length-1);i++){
  const a=prefix[i],b=prefix[i+1];cells.push(`⟨${a.x},${b.x},${a.lower},${b.upper},${logs[i].lower},${logs[i+1].upper}⟩`);
 }
 const name=`Grid${start}N${size}`,ns='ChenEffective.PlattWindow.AssemblyPilot.'+name;
 fs.writeFileSync(path.join(out,name+'.lean'),`import PlattAssemblyKernel\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef cells : List AssemblyCell := [${cells.join(',\n')}]\ntheorem budget_checked : cells.all (checkAssemblyCell (2^48) 20000 ${ref.lower} ${ref.upper} ${rlog.lower} ${rlog.upper}) = true := by\n decide +kernel\ntheorem seams_checked : checkCellChain ${prefix[start].x} ${prefix[start+cells.length].x} cells = true := by\n decide +kernel\nend ${ns}\n`);
 report.batches.push({module:'PlattAssemblyPilot.'+name,kind:'grid-budget-and-seams',cells:cells.length,start});
}
fs.writeFileSync(path.join(out,'pilot-proposals.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report,null,2));
