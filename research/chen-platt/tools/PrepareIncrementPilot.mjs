import fs from 'node:fs';import path from 'node:path';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),out=path.join(root,'PlattAssemblyPilot');
const sealed=process.argv.includes('--sealed');
const report=[];
for(const [start,size] of [[0,8],[0,32],[10000,32],[9992,16],[0,256]]){
 if(!sealed&&size===256)continue; // Retain the failed large unsealed trial in the report only.
 const records=Array.from({length:size},(_,j)=>{const i=start+j,name='C'+String(i).padStart(6,'0');return {name,...JSON.parse(fs.readFileSync(path.join(repo,'.lake/build-434/manual-certificates/Count131072',name+'.json'))).metadata};});
 const name=`${sealed?'Sealed':''}Totals${start}N${size}`,ns='ChenEffective.PlattWindow.AssemblyPilot.'+name;
 let src=`import ${sealed?'PlattSegmentPacket':'PlattIncrementKernel'}\n`+records.map(r=>'import PlattCertificates.Count131072.'+r.name).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
 let L=0n,U=0n;
 for(let i=0;i<records.length;i++){
  const r=records[i],p=`Manual.Count131072.${r.name}`;L+=BigInt(r.lower);U+=BigInt(r.upper);
  src+=`def row${i} : IncrementRow := ⟨${r.lo-1},${r.hi},${r.lower},${r.upper}⟩\n`;
  if(sealed)src+=`opaque packet${i} : SegmentPacket ${r.lo} ${r.w} ${r.B} ${r.lower} ${r.upper} :=\n ⟨${p}.packed,${p}.count_checked,${p}.arithmetic_checked⟩\n`;
  const packed=sealed?`packet${i}.packed`:`${p}.packed`,hc=sealed?`packet${i}.counts`:`${p}.count_checked`,ha=sealed?`packet${i}.arithmetic`:`${p}.arithmetic_checked`;
  src+=`theorem certified${i} : IncrementCertified row${i} :=\n certifyIncrement ${r.lo} ${r.w} ${r.B} ${packed} ${r.lower} ${r.upper}\n (by decide +kernel) (by decide +kernel) (by decide +kernel)\n ${hc} ${ha}\n`;
 }
 src+=`def rows : List IncrementRow := [${records.map((r,i)=>'row'+i).join(',')}]\n`;
 src+=`theorem all_certified : CertifiedIncrements rows :=\n ${records.map((r,i)=>`CertifiedIncrements.cons certified${i} (`).join('')}CertifiedIncrements.nil${')'.repeat(records.length)}\n`;
 src+=`theorem summary_checked : checkIncrementSummary ${records[0].lo-1} ${records.at(-1).hi} ${L} ${U} rows = true := by\n decide +kernel\n#print axioms all_certified\nend ${ns}\n`;
 fs.writeFileSync(path.join(out,name+'.lean'),src);report.push({module:'PlattAssemblyPilot.'+name,start,chunks:size,lower:String(L),upper:String(U),crossesSectionBoundary:start===9992});
}
fs.writeFileSync(path.join(out,(sealed?'sealed-':'')+'increment-proposals.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report,null,2));
