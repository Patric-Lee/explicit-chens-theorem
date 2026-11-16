import fs from 'node:fs';import path from 'node:path';import zlib from 'node:zlib';import {pathToFileURL} from 'node:url';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt');
const {batchPlan}=await import(pathToFileURL(path.join(root,'tools/AssemblyPlan.mjs')).href);
const manifest=JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyData/manifest.json')));
const out=path.join(root,'PlattGlobalGrid');fs.mkdirSync(out,{recursive:true});
let nodes=[];
for(let section=1;section<=8;section++){
 const data=JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(root,`PlattAssemblyData/grid-s${section}.json.gz`))));
 for(const batch of batchPlan('grid',section,manifest.cells)){
  const name=`S${section}B${String(batch.index).padStart(6,'0')}`,module='PlattGlobalGrid.'+name,ns='ChenEffective.PlattWindow.GlobalGrid.'+name;
  const parent=`PlattAssembly.Grid.S${section}.B${String(batch.index).padStart(6,'0')}`,pns=`ChenEffective.PlattWindow.Assembly.Grid.S${section}.B${String(batch.index).padStart(6,'0')}`;
  const rows=data.records.slice(batch.start-data.start,batch.end-data.start+1),a=rows[0].x,b=rows.at(-1).x;
  const old=fs.readFileSync(path.join(root,parent.replaceAll('.','/')+'.lean'),'utf8');
  const slices=[...old.matchAll(/Manual\.Log256\.(C\d+)\.rows\.drop (\d+)\)\.take (\d+)/g)].map(m=>({name:m[1],start:m[2],count:m[3]}));
  if(!slices.length)throw Error('No certified log slices '+parent);
  let hlogs=`CheckedLogRows.slice ${slices[0].start} ${slices[0].count} (.checked Manual.Log256.${slices[0].name}.checked)`;
  for(const s of slices.slice(1))hlogs=`CheckedLogRows.append (${hlogs}) (CheckedLogRows.slice ${s.start} ${s.count} (.checked Manual.Log256.${s.name}.checked))`;
  let src=`import PlattGlobalGridKernel\nimport ${parent}\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef points : List PrimePoint := [${rows.map(p=>`(${p.x},${p.lower},${p.upper})`).join(',')}]\ntheorem log_certified : CheckedLogRows ${pns}.logRows := ${hlogs}\ntheorem linked : checkGridLinks ${pns}.cells points ${pns}.logRows=true := by decide +kernel\ntheorem certified : GridWindowCertificate ${a} ${b} points := .leaf ${pns}.cells ${pns}.logRows ${pns}.checked log_certified ${pns}.seams_checked linked\n#print axioms certified\nend ${ns}\n`;
  fs.writeFileSync(path.join(out,name+'.lean'),src);nodes.push({module,ns,a,b});
 }
}
const leaves=[...nodes],levels=[];let level=0;
while(nodes.length>1){const next=[];
 for(let i=0;i<nodes.length;i+=32){
  const group=nodes.slice(i,i+32),name=`L${level}B${String(i/32).padStart(4,'0')}`,module='PlattGlobalGrid.'+name,ns='ChenEffective.PlattWindow.GlobalGrid.'+name;
  for(let j=1;j<group.length;j++)if(group[j-1].b!==group[j].a)throw Error('grid seam mismatch');
  let src='import PlattGlobalGridKernel\n'+group.map(n=>'import '+n.module).join('\n')+`\nnamespace ${ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  let points=group[0].ns+'.points',expr=group[0].ns+'.certified';
  for(const n of group.slice(1)){points=`(${points} ++ ${n.ns}.points)`;expr=`GridWindowCertificate.append (${expr}) ${n.ns}.certified`;}
  const a=group[0].a,b=group.at(-1).b;
  src+=`def points : List PrimePoint := ${points}\ntheorem certified : GridWindowCertificate ${a} ${b} points := ${expr}\n#print axioms certified\nend ${ns}\n`;
  fs.writeFileSync(path.join(out,name+'.lean'),src);next.push({module,ns,a,b});
 }levels.push(next);nodes=next;level++;
}
const report={leaves,levels,root:nodes[0]};fs.writeFileSync(path.join(out,'plan.json'),JSON.stringify(report,null,2));console.log(JSON.stringify({leaves:leaves.length,levels:levels.map(x=>x.length),root:nodes[0]}));
