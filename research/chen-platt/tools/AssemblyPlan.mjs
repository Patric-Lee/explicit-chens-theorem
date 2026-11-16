import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import crypto from 'node:crypto';
import {atomicJson} from '../../../OpenAI/tools/atomic-json.mjs';
export const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
export const kinds=['prefix','totals','grid'];
export const title=k=>k[0].toUpperCase()+k.slice(1);
export function sectionBounds(kind,section,total){
 const width=kind==='grid'?30000:10000;
 return {start:(section-1)*width,end:Math.min(total,section*width)};
}
export function batchSize(kind,section){return kind==='grid'?256:kind==='prefix'?(section===1?4:32):(section===1?8:32);}
export function batchPlan(kind,section,total){
 const {start,end}=sectionBounds(kind,section,total),size=batchSize(kind,section);
 const regions=section===1&&kind!=='grid'?
  [[start,Math.min(end,128),size],[Math.min(end,128),end,kind==='prefix'?16:32]]:[[start,end,size]];
 const plan=[];
 for(const [a,b,width] of regions)for(let i=a;i<b;i+=width)plan.push({index:plan.length,start:i,end:Math.min(b,i+width)});
 return plan;
}

// Proposals only. Each run subsequently kernel checks the relevant leaf facts.
export function prepareAssembly(repo){
 const root=path.join(repo,'research/chen-platt'),out=path.join(root,'PlattAssemblyData');
 fs.mkdirSync(out,{recursive:true});
 const raw=fs.readFileSync(path.join(root,'block-relative-1e10.grid.json.gz'));
 const data=JSON.parse(zlib.gunzipSync(raw));
 const counts=zlib.gunzipSync(fs.readFileSync(path.join(root,'block-relative-1e10.counts.bin.gz')));
 if(sha(counts)!==data.countSha256)throw Error('Count input hash mismatch');
 const verification=JSON.parse(fs.readFileSync(path.join(root,'COUNT_CAMPAIGN_VERIFIED.json')));
 if(verification.chunks!==76265||verification.gridInputHash!==sha(raw)||verification.countInputHash!==data.countSha256)
  throw Error('Current completed-count manifest is missing/mismatched');
 const plans=[];
 for(let g=0;g<data.groups.length;g++){
  const group=data.groups[g],end=data.groups[g+1]?.offset??counts.length/2,W=2**group.w,cap=Math.floor(131072/(2*W));
  for(let offset=group.offset;offset<end;offset+=cap){const B=Math.min(cap,end-offset),lo=group.lo+2*W*(offset-group.offset);
   plans.push({index:plans.length,offset,w:group.w,W,B,lo,hi:lo-1+2*W*B,cuts:[]});}
 }
 const S=1n<<48n,points=[];let L=0n,U=0n,a=data.U,point=0,chunk=0;
 let localL=0n,localU=0n;
 function record(){
  if(data.grid[point]?.x!==a)return;
  const p=plans[chunk],k=(a-(p.lo-1))/(2*p.W);
  p.cuts.push({grid:point,x:a,k,lower:String(localL),upper:String(localU),globalLower:String(L),globalUpper:String(U)});
  points.push({x:a,lower:String(L),upper:String(U)});point++;
 }
 record();
 for(let offset=0;offset<counts.length/2;offset++){
  const p=plans[chunk],c=BigInt(counts.readUInt16LE(2*offset)),h=2*p.W;
  const l=S*c/BigInt(a+h),u=S*c/BigInt(a)+1n;L+=l;U+=u;localL+=l;localU+=u;a+=h;record();
  if(offset+1===p.offset+p.B){
   p.lower=String(localL);p.upper=String(localU);
   // Include the terminal prefix even when it is not a grid point.
   if(p.cuts.at(-1)?.k!==p.B)p.cuts.push({k:p.B,lower:p.lower,upper:p.upper});
   const name='C'+String(chunk).padStart(6,'0');
   const r=JSON.parse(fs.readFileSync(path.join(repo,'.lake/build-434/manual-certificates/Count131072',name+'.json')));
   if(r.classification!=='LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30'||r.metadata.lower!==p.lower||r.metadata.upper!==p.upper||r.metadata.lo!==p.lo||r.metadata.B!==p.B)
    throw Error('Checked count/total proposal mismatch '+name);
   if(chunk+1<plans.length){chunk++;localL=0n;localU=0n;}
   if((p.index+1)%10000===0)console.log(JSON.stringify({assemblyPrepare:'count-receipts',checked:p.index+1,total:plans.length}));
  }
 }
 if(point!==data.grid.length||a!==data.R)throw Error('Incomplete grid alignment');
 const logHashes=[];let logPoint=0;
 for(let i=0;i<Math.ceil(points.length/256);i++){
  const name='C'+String(i).padStart(6,'0'),m='PlattCertificates.Log256.'+name;
  const src=fs.readFileSync(path.join(root,'PlattCertificates/Log256',name+'.lean'));
  const receipt=JSON.parse(fs.readFileSync(path.join(repo,'.lake/build-434/manual-certificates/Log256',name+'.json')));
  if(receipt.classification!=='LEAN_KERNEL_CHECKED_COMPONENT_NOT_FINAL_H30'||receipt.sourceHash!==sha(src))throw Error('Log source/receipt mismatch '+name);
  logHashes.push([m,sha(src)]);
  for(const row of src.toString().matchAll(/⟨(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+)⟩/g)){
   const p=points[logPoint];if(!p||p.x!==Number(row[1]))throw Error('Log row alignment mismatch');
   p.logLower=row[7];p.logUpper=row[8];p.logChunk=i;p.logRow=logPoint%256;logPoint++;
  }
 }
 if(logPoint!==points.length)throw Error('Incomplete logs');
 const ref=points.at(-1);let minimum=0n,maximum=0n;
 for(let i=0;i+1<points.length;i++){
  const lo=BigInt(points[i].lower)-BigInt(ref.upper)-BigInt(points[i+1].logUpper)+BigInt(ref.logLower);
  const hi=BigInt(points[i+1].upper)-BigInt(ref.lower)-BigInt(points[i].logLower)+BigInt(ref.logUpper);
  if(lo*20000n< -S||hi*20000n>S)throw Error('Grid budget does not fit '+i);
  if(lo<minimum)minimum=lo;if(hi>maximum)maximum=hi;
 }
 const files=[];
 for(let section=1;section<=8;section++){
  for(const kind of kinds){
   const total=kind==='grid'?points.length-1:plans.length,{start,end}=sectionBounds(kind,section,total);
   const payload=kind==='grid'?points.slice(start,end+1):kind==='totals'?
    plans.slice(start,end).map(({cuts,...p})=>p):plans.slice(start,end);
   const name=`${kind}-s${section}.json.gz`,bytes=zlib.gzipSync(JSON.stringify({start,end,records:payload}));
   fs.writeFileSync(path.join(out,name),bytes);files.push({kind,section,file:name,hash:sha(bytes)});
  }
 }
 const manifest={schema:1,classification:'ASSEMBLY_PROPOSALS_NOT_FINAL_PROOF',gridInputHash:sha(raw),countInputHash:data.countSha256,
  countVerificationManifest:verification.sourceObjectManifestHash,logSourcesHash:sha(JSON.stringify(logHashes)),
  configurationHash:sha(fs.readFileSync(path.join(repo,'lean-toolchain'),'utf8')+fs.readFileSync(path.join(repo,'lake-manifest.json'),'utf8')),
  counts:plans.length,points:points.length,cells:points.length-1,reference:ref,
  lower:Number(minimum)/Number(S),upper:Number(maximum)/Number(S),files};
 atomicJson(path.join(out,'manifest.json'),manifest);return manifest;
}

export function generateBatch(kind,section,plan,records,manifest){
 const label='B'+String(plan.index).padStart(6,'0'),mod=`PlattAssembly.${title(kind)}.S${section}.${label}`;
 const ns=`ChenEffective.PlattWindow.Assembly.${title(kind)}.S${section}.${label}`;
 const rows=records.slice(plan.start-records[0].index,plan.end-records[0].index);
 let source,metadata;
 if(kind==='prefix'){
  source='import PlattAssemblyKernel\n'+rows.map(p=>'import PlattCertificates.Count131072.C'+String(p.index).padStart(6,'0')).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  for(const p of rows){const n='C'+String(p.index).padStart(6,'0');
   source+=`def cuts${p.index} : List PrefixCut := [${p.cuts.map(c=>`⟨${c.k},${c.lower},${c.upper}⟩`).join(',\n')}]\n`;
   source+=`theorem checked${p.index} : checkPrefixCuts (2^48) ${p.lo} ${p.w} Manual.Count131072.${n}.packed ${p.B} cuts${p.index} = true := by\n decide +kernel\n`;
   const points=p.cuts.filter(c=>c.grid!==undefined);
   if(points.length){
    const baseLower=BigInt(points[0].globalLower)-BigInt(points[0].lower),baseUpper=BigInt(points[0].globalUpper)-BigInt(points[0].upper);
    source+=`def pointBounds${p.index} : List (Nat × Nat × Nat) := [${points.map(c=>`(${c.x},${c.globalLower},${c.globalUpper})`).join(',')}]\n`;
    source+=`theorem point_links_checked${p.index} : (cuts${p.index}.take ${points.length}).map (fun c => (${p.lo}-1+2*2^${p.w}*c.k,${baseLower}+c.lower,${baseUpper}+c.upper)) = pointBounds${p.index} := by\n decide +kernel\n`;
   }
  }
  source+=`end ${ns}\n`;metadata={countStart:plan.start,countEnd:plan.end,checkpoints:rows.reduce((n,p)=>n+p.cuts.length,0)};
 }else if(kind==='totals'){
  source='import PlattSegmentPacket\n'+rows.map(p=>'import PlattCertificates.Count131072.C'+String(p.index).padStart(6,'0')).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  let L=0n,U=0n;
  rows.forEach((p,i)=>{const n='Manual.Count131072.C'+String(p.index).padStart(6,'0');L+=BigInt(p.lower);U+=BigInt(p.upper);
   source+=`def row${i} : IncrementRow := ⟨${p.lo-1},${p.hi},${p.lower},${p.upper}⟩\nopaque packet${i} : SegmentPacket ${p.lo} ${p.w} ${p.B} ${p.lower} ${p.upper} := ⟨${n}.packed,${n}.count_checked,${n}.arithmetic_checked⟩\ntheorem certified${i} : IncrementCertified row${i} := certifyIncrement ${p.lo} ${p.w} ${p.B} packet${i}.packed ${p.lower} ${p.upper}\n (by decide +kernel) (by decide +kernel) (by decide +kernel) packet${i}.counts packet${i}.arithmetic\n`;
  });
  source+=`def rows : List IncrementRow := [${rows.map((p,i)=>'row'+i).join(',')}]\ntheorem all_certified : CertifiedIncrements rows := ${rows.map((p,i)=>`CertifiedIncrements.cons certified${i} (`).join('')}CertifiedIncrements.nil${')'.repeat(rows.length)}\ntheorem checked : checkIncrementSummary ${rows[0].lo-1} ${rows.at(-1).hi} ${L} ${U} rows = true := by\n decide +kernel\nend ${ns}\n`;
  metadata={countStart:plan.start,countEnd:plan.end,a:rows[0].lo-1,b:rows.at(-1).hi,lower:String(L),upper:String(U)};
 }else{
  // Grid records have a global point index supplied by the caller.
  const points=records.slice(plan.start-records[0].index,plan.end-records[0].index+1);
  const chunks=[...new Set(points.map(p=>p.logChunk))];
  source='import PlattAssemblyKernel\nimport PlattLogRows\n'+chunks.map(i=>'import PlattCertificates.Log256.C'+String(i).padStart(6,'0')).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  source+=`def cells : List AssemblyCell := [${points.slice(0,-1).map((a,i)=>{const b=points[i+1];return `⟨${a.x},${b.x},${a.lower},${b.upper},${a.logLower},${b.logUpper}⟩`;}).join(',\n')}]\n`;
  const r=manifest.reference;
  source+=`theorem checked : cells.all (checkAssemblyCell (2^48) 20000 ${r.lower} ${r.upper} ${r.logLower} ${r.logUpper}) = true := by\n decide +kernel\ntheorem seams_checked : checkCellChain ${points[0].x} ${points.at(-1).x} cells = true := by\n decide +kernel\n`;
  const slices=chunks.map(c=>{const subset=points.filter(p=>p.logChunk===c);return `(Manual.Log256.C${String(c).padStart(6,'0')}.rows.drop ${subset[0].logRow}).take ${subset.length}`;});
  source+=`def logRows : List LogCertificate.LogRow := ${slices.map(s=>'('+s+')').join(' ++ ')}\ntheorem log_links_checked : logRows.map (fun r => (r.x,r.lower,r.upper)) = [${points.map(p=>`(${p.x},${p.logLower},${p.logUpper})`).join(',')}] := by\n decide +kernel\nend ${ns}\n`;
  metadata={cellStart:plan.start,cellEnd:plan.end,a:points[0].x,b:points.at(-1).x,logChunks:chunks};
 }
 return {module:mod,source,metadata};
}
