import fs from 'node:fs';import path from 'node:path';
import {batchPlan,title} from './AssemblyPlan.mjs';
const repo=process.argv[2],root=path.join(repo,'research/chen-platt'),out=path.join(root,'PlattGlobalTotals');fs.mkdirSync(out,{recursive:true});
const manifest=JSON.parse(fs.readFileSync(path.join(root,'PlattAssemblyData/manifest.json')));
let nodes=[];
for(let section=1;section<=8;section++)for(const p of batchPlan('totals',section,manifest.counts)){
 const name='B'+String(p.index).padStart(6,'0'),module=`PlattAssembly.Totals.S${section}.${name}`;
 const r=JSON.parse(fs.readFileSync(path.join(repo,'.lake/build-434/assembly-certificates/Totals','S'+section,name+'.json')));
 nodes.push({module,namespace:`ChenEffective.PlattWindow.Assembly.Totals.S${section}.${name}`,a:r.metadata.a,b:r.metadata.b,lower:r.metadata.lower,upper:r.metadata.upper,leaf:true});
}
for(let i=1;i<nodes.length;i++)if(nodes[i-1].b!==nodes[i].a)throw Error('Totals seam mismatch');
const roots=[],levels=[];let level=0;
while(nodes.length>1){
 const next=[];
 for(let i=0;i<nodes.length;i+=32){
  const group=nodes.slice(i,i+32),name=`L${level}B${String(i/32).padStart(4,'0')}`,module='PlattGlobalTotals.'+name,namespace='ChenEffective.PlattWindow.GlobalTotals.'+name;
  let src='import PlattGlobalBoundKernel\n'+group.map(n=>'import '+n.module).join('\n')+`\nnamespace ${namespace}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n`;
  const proof=[];
  group.forEach((n,j)=>{
   src+=`theorem leaf${j} : ReciprocalBound ${n.a} ${n.b} ${n.lower} ${n.upper} := `+
    (n.leaf?`ReciprocalBound.block (rows:=${n.namespace}.rows) ${n.namespace}.all_certified ${n.namespace}.checked`:`${n.namespace}.bound`)+`\n`;
   proof.push({expr:'leaf'+j,...n});
  });
  let serial=0;
  while(proof.length>1){const merged=[];
   for(let k=0;k<proof.length;k+=2){if(k+1===proof.length){merged.push(proof[k]);continue;}
    const a=proof[k],b=proof[k+1],L=String(BigInt(a.lower)+BigInt(b.lower)),U=String(BigInt(a.upper)+BigInt(b.upper)),n='join'+serial++;
    src+=`theorem ${n} : ReciprocalBound ${a.a} ${b.b} ${L} ${U} :=\n ReciprocalBound.relabel (by decide +kernel) (by decide +kernel) (ReciprocalBound.append ${a.expr} ${b.expr})\n`;
    merged.push({a:a.a,b:b.b,lower:L,upper:U,expr:n});
   }proof.splice(0,proof.length,...merged);
  }
  const r=proof[0];src+=`theorem bound : ReciprocalBound ${r.a} ${r.b} ${r.lower} ${r.upper} := ${r.expr}\n#print axioms bound\nend ${namespace}\n`;
  fs.writeFileSync(path.join(out,name+'.lean'),src);next.push({module,namespace,a:r.a,b:r.b,lower:r.lower,upper:r.upper,leaf:false});roots.push(module);
 }
 levels.push(next.map(n=>n.module));nodes=next;level++;
}
const r=nodes[0];if(r.a!==4000000||r.b!==10000000000||r.lower!==manifest.reference.lower||r.upper!==manifest.reference.upper)throw Error('Global reference sum mismatch');
const report={classification:'GLOBAL_SUM_TREE_GENERATED_NOT_CHECKED',levels,root:r,modules:roots.length};
fs.writeFileSync(path.join(out,'plan.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report,null,2));
