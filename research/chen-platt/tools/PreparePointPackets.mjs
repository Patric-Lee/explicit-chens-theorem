import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import {pathToFileURL} from 'node:url';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt');
const {batchPlan}=await import(pathToFileURL(path.join(root,'tools/AssemblyPlan.mjs')).href);
const manifest=JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyData/manifest.json')));
const out=path.join(root,'PlattPointPackets');fs.mkdirSync(out,{recursive:true});
const nodes=[];let L=0n,U=0n;
for(let section=1;section<=8;section++){
 const records=JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(root,`PlattAssemblyData/prefix-s${section}.json.gz`)))).records;
 for(const batch of batchPlan('prefix',section,manifest.counts)){
  const name=`S${section}B${String(batch.index).padStart(6,'0')}`,module='PlattPointPackets.'+name,ns='ChenEffective.PlattWindow.PointPackets.'+name;
  const parent=`PlattAssembly.Prefix.S${section}.B${String(batch.index).padStart(6,'0')}`,pns=`ChenEffective.PlattWindow.Assembly.Prefix.S${section}.B${String(batch.index).padStart(6,'0')}`;
  const rows=records.slice(batch.start-records[0].index,batch.end-records[0].index),a=rows[0].lo-1,l=String(L),u=String(U);
  let src=`import PlattPointPacketKernel\nimport ${parent}\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  for(const p of rows){
   const i=p.index,raw='Manual.Count131072.C'+String(i).padStart(6,'0'),has=p.cuts.some(c=>c.grid!==undefined);
   src+=`abbrev cuts${i} := ${pns}.cuts${i}\n`;
   src+=has?`abbrev points${i} := ${pns}.pointBounds${i}\n`:`def points${i} : List PrimePoint := []\n`;
   src+=`opaque packet${i} : CheckedPointSegment ${p.lo} ${p.w} ${p.B} ${p.lower} ${p.upper} ${L} ${U} cuts${i} points${i} :=\n ⟨${raw}.packed,by decide +kernel,by decide +kernel,by decide +kernel,${raw}.count_checked,${raw}.arithmetic_checked,${pns}.checked${i},${has?pns+'.point_links_checked'+i:'by rfl'}⟩\n`;
   src+=`def segment${i} : PointSegment := ⟨${p.lo},${p.w},${p.B},${p.lower},${p.upper},${L},${U},cuts${i},points${i},packet${i}⟩\n`;
   L+=BigInt(p.lower);U+=BigInt(p.upper);
  }
  const b=rows.at(-1).hi;
  src+=`def segments : List PointSegment := [${rows.map(p=>'segment'+p.index).join(',')}]\ndef points : List PrimePoint := segments.flatMap PointSegment.points\ntheorem checked : checkPointChain ${a} ${l} ${u} ${b} ${L} ${U} segments = true := by decide +kernel\ntheorem certified : PointChainCertificate ${a} ${l} ${u} ${b} ${L} ${U} points := .leaf segments checked\n#print axioms certified\nend ${ns}\n`;
  fs.writeFileSync(path.join(out,name+'.lean'),src);nodes.push({module,ns,a,l,u,b,L:String(L),U:String(U)});
 }
}
if(String(L)!==manifest.reference.lower||String(U)!==manifest.reference.upper)throw Error('carry mismatch');
const leaves=[...nodes],levels=[];let current=nodes,level=0;
while(current.length>1){
 const next=[];
 for(let i=0;i<current.length;i+=32){
  const group=current.slice(i,i+32),name=`L${level}B${String(i/32).padStart(4,'0')}`,module='PlattPointPackets.'+name,ns='ChenEffective.PlattWindow.PointPackets.'+name;
  let src='import PlattPointPacketKernel\n'+group.map(n=>'import '+n.module).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  let expr=group[0].ns+'.certified',points=group[0].ns+'.points';
  for(const n of group.slice(1)){expr=`PointChainCertificate.append (${expr}) ${n.ns}.certified`;points=`(${points} ++ ${n.ns}.points)`;}
  const a=group[0],b=group.at(-1);
  src+=`def points : List PrimePoint := ${points}\ntheorem certified : PointChainCertificate ${a.a} ${a.l} ${a.u} ${b.b} ${b.L} ${b.U} points := ${expr}\n#print axioms certified\nend ${ns}\n`;
  fs.writeFileSync(path.join(out,name+'.lean'),src);next.push({module,ns,a:a.a,l:a.l,u:a.u,b:b.b,L:b.L,U:b.U});
 }
 levels.push(next);current=next;level++;
}
const report={leaves,levels,root:current[0]};fs.writeFileSync(path.join(out,'plan.json'),JSON.stringify(report,null,2));console.log(JSON.stringify({leaves:leaves.length,levels:levels.map(x=>x.length),root:current[0]}));
