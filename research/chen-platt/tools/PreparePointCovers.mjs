import fs from 'node:fs';import path from 'node:path';import zlib from 'node:zlib';import {pathToFileURL} from 'node:url';
const repo=process.argv[2],staging=process.argv[3],root=path.join(repo,'research/chen-platt');
const {batchPlan}=await import(pathToFileURL(path.join(root,'tools/AssemblyPlan.mjs')).href);
const manifest=JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyData/manifest.json')));
const pp=JSON.parse(fs.readFileSync(path.join(root,'PlattPointPackets/plan.json'))),gp=JSON.parse(fs.readFileSync(path.join(root,'PlattGlobalGrid/plan.json')));
const owners=new Int32Array(manifest.points);owners.fill(-1);let leafIndex=0;
for(let section=1;section<=8;section++){
 const records=JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(root,`PlattAssemblyData/prefix-s${section}.json.gz`)))).records;
 for(const batch of batchPlan('prefix',section,manifest.counts)){
  for(const p of records.slice(batch.start-records[0].index,batch.end-records[0].index))for(const c of p.cuts)if(c.grid!==undefined){if(owners[c.grid]!==-1)throw Error('Duplicate owner');owners[c.grid]=leafIndex;}
  leafIndex++;
 }
}
if(leafIndex!==pp.leaves.length||owners.some(x=>x<0))throw Error('Incomplete prefix owner map');
const cat=xs=>xs.reduce((a,b)=>`(${a} ++ ${b})`),append=xs=>xs.reduce((a,b)=>`PointSubset.append (${a}) (${b})`);
const trans=xs=>xs.reduce((a,b)=>`PointSubset.trans (${a}) (${b})`);
const coverDir=path.join(root,'PlattPointCovers');fs.mkdirSync(coverDir,{recursive:true});
const covers=[];let gridIndex=0;
for(let section=1;section<=8;section++)for(const batch of batchPlan('grid',section,manifest.cells)){
 const grid=gp.leaves[gridIndex++],sources=[...new Set(owners.slice(batch.start,batch.end+1))],name=`S${section}B${String(batch.index).padStart(6,'0')}`,module='PlattPointCovers.'+name,ns='ChenEffective.PlattWindow.PointCovers.'+name;
 const parents=sources.map(i=>pp.leaves[i]);
 const source='import PlattPointSubsetKernel\n'+parents.map(p=>'import '+p.module).join('\n')+'\nimport '+grid.module+`\nnamespace ${ns}\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\ndef sourcePoints : List PrimePoint := ${cat(parents.map(p=>p.ns+'.points'))}\ntheorem checked : checkPointCoverAux 1000000 sourcePoints ${grid.ns}.points=true := by decide +kernel\ntheorem covered : PointSubset ${grid.ns}.points sourcePoints := .checked checked\n#print axioms covered\nend ${ns}\n`;
 fs.writeFileSync(path.join(coverDir,name+'.lean'),source);covers.push({name,module,ns,grid,sources});
}
// Reusable structural injections from each prefix leaf into the global tree.
const transportDir=path.join(root,'PlattPointTransports');fs.mkdirSync(transportDir,{recursive:true});
let src='import PlattPointSubsetKernel\nimport '+pp.root.module+'\nnamespace ChenEffective.PlattWindow.PointTransports\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';
let children=pp.leaves;const edges=new Map();
for(const level of pp.levels){
 for(let i=0;i<level.length;i++){
  const parent=level[i],group=children.slice(i*32,i*32+32),tag=parent.module.split('.').at(-1),pre=j=>`prefix${tag}_${j}`,step=j=>`step${tag}_${j}`;
  for(let j=0;j<group.length;j++)src+=`def ${pre(j)} : List PrimePoint := ${cat(group.slice(0,j+1).map(c=>c.ns+'.points'))}\n`;
  const last=group.length-1;
  src+=`theorem ${step(last)} : PointSubset ${pre(last)} ${parent.ns}.points := .refl ${pre(last)}\n`;
  for(let j=last-1;j>=0;j--)src+=`theorem ${step(j)} : PointSubset ${pre(j)} ${parent.ns}.points := .trans (.left ${pre(j)} ${group[j+1].ns}.points) ${step(j+1)}\n`;
  for(let j=0;j<group.length;j++){
   const name=`edge${tag}_${j}`;src+=`theorem ${name} : PointSubset ${group[j].ns}.points ${parent.ns}.points := `+(j===0?step(0):`.trans (.right ${pre(j-1)} ${group[j].ns}.points) ${step(j)}`)+'\n';
   edges.set(group[j].module,{name,parent});
  }
 }
 children=level;
}
pp.leaves.forEach((leaf,i)=>{
 let node=leaf;const chain=[];while(node.module!==pp.root.module){const edge=edges.get(node.module);if(!edge)throw Error('Missing tree edge');chain.push(edge.name);node=edge.parent;}
 src+=`theorem leaf${i} : PointSubset ${leaf.ns}.points ${pp.root.ns}.points := ${trans(chain)}\n`;
});
src+='#print axioms leaf0\nend ChenEffective.PlattWindow.PointTransports\n';fs.writeFileSync(path.join(transportDir,'Global.lean'),src);
// Combine local checks with the structural source injections and grid tree.
src='import PlattPointSubsetKernel\nimport PlattPointTransports.Global\nimport '+gp.root.module+'\n'+covers.map(c=>'import '+c.module).join('\n')+'\nnamespace ChenEffective.PlattWindow\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';
const gridProofs=new Map();
for(const c of covers){
 const name='cover'+c.name;
 src+=`theorem ${name} : PointSubset ${c.grid.ns}.points ${pp.root.ns}.points := .trans ${c.ns}.covered (${append(c.sources.map(i=>'PointTransports.leaf'+i))})\n`;
 gridProofs.set(c.grid.module,name);
}
children=gp.leaves;
for(const level of gp.levels){
 for(let i=0;i<level.length;i++){
  const node=level[i],group=children.slice(i*32,i*32+32),name='cover'+node.module.split('.').at(-1);
  src+=`theorem ${name} : PointSubset ${node.ns}.points ${pp.root.ns}.points := ${append(group.map(c=>gridProofs.get(c.module)))}\n`;
  gridProofs.set(node.module,name);
 }children=level;
}
src+=`\n/-- All grid points are covered by small kernel-checked joins and structural
injections into the global cumulative prefix stream. -/\ntheorem global_grid_points_covered : ∀p∈${gp.root.ns}.points,p∈${pp.root.ns}.points := PointSubset.sound ${gridProofs.get(gp.root.module)}\n#print axioms global_grid_points_covered\nend ChenEffective.PlattWindow\n`;
fs.writeFileSync(path.join(root,'PlattGlobalPointCover.lean'),src);if(staging)fs.writeFileSync(path.join(staging,'PlattGlobalPointCover.lean'),src);
const report={classification:'SMALL_POINT_JOINS_GENERATED_NOT_CHECKED',covers,transport:'PlattPointTransports.Global',root:'PlattGlobalPointCover'};
fs.writeFileSync(path.join(coverDir,'plan.json'),JSON.stringify(report,null,2));console.log(JSON.stringify({covers:covers.length,transportBytes:fs.statSync(path.join(transportDir,'Global.lean')).size,rootBytes:Buffer.byteLength(src),maxSourceLeaves:Math.max(...covers.map(c=>c.sources.length))}));
