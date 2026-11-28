// One-hot-domain read-once benchmark. Run with: node research/onehot-readonce/check.mjs
const expected = { distinct: 33864, pass: 12672, readOnce: 7488, falsePass: 5184 };
const masks = [15, 240, 3840, 61440, 4369, 8738, 17476, 34952];
const fixtures = [
  { truth: 0x0125, min: 6, gates: [[1,4,6],[0,0,8],[0,1,5],[0,2,4],[1,9,10],[1,12,11]] },
  { truth: 0x0421, min: 5, gates: [[0,0,4],[0,1,5],[0,2,6],[1,8,9],[1,11,10]] },
];
function assert(ok, msg) { if (!ok) throw new Error(msg); }
function formulas(omitRow, omitCol) {
  const leaves = masks.filter((_, i) => i !== omitRow && i !== 4 + omitCol);
  const sets = Array.from({ length: 64 }, () => new Set());
  const add = (s, v) => { s.add(v); s.add(v ^ 65535); };  // arbitrary NOT parity
  for (let s = 1; s < 64; s++) {
    if (!(s & (s - 1))) { add(sets[s], leaves[Math.log2(s)]); continue; }
    for (let a = (s - 1) & s; a; a = (a - 1) & s) {
      const b = s ^ a;
      if (a >= b) continue;
      for (const x of sets[a]) for (const y of sets[b]) {
        add(sets[s], x & y);
        add(sets[s], x | y);
      }
    }
  }
  return sets[63];
}
function check() {
  const sets = Array.from({ length: 16 }, (_, k) => formulas(k >> 2, k & 3));
  const stats = { distinct: 0, pass: 0, readOnce: 0, falsePass: 0 };
  const result = new Map();
  for (let t = 0; t < 65536; t++) {
    const rows = [0,1,2,3].map(i => (t >>> (4 * i)) & 15);
    const cols = [0,1,2,3].map(j => rows.reduce((a, r, i) => a | (((r >>> j) & 1) << i), 0));
    if (new Set(rows).size < 4 || new Set(cols).size < 4) continue;
    stats.distinct++;
    const comparable = (side, i) => side.every(b => (side[i] & b) === side[i] || (side[i] & b) === b);
    let pass = false, found = false;
    for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) {
      const p = comparable(rows, i) && comparable(cols, j);
      const f = sets[4 * i + j].has(t);
      assert(!f || p, "prefilter falsely rejected a read-once result");
      pass ||= p;
      found ||= f;
    }
    stats.pass += Number(pass);
    stats.readOnce += Number(found);
    stats.falsePass += Number(pass && !found);
    if (fixtures.some(f => f.truth === t)) result.set(t, { pass, found });
  }
  for (const k of Object.keys(expected)) assert(stats[k] === expected[k], "census mismatch: " + k);
  for (const f of fixtures) {
    const wires = masks.slice();
    for (const [or, a, b] of f.gates) {
      assert(a < wires.length && b < wires.length, "noncausal wire reference");
      wires.push(or ? wires[a] | wires[b] : wires[a] & wires[b]);
    }
    assert(wires.at(-1) === f.truth, "bad upper witness");
    const target = result.get(f.truth);
    assert(target?.pass && target.found === (f.min === 5), "pair classification mismatch");
    assert(f.gates.length === f.min, "bad witness size");
  }
  return stats;
}

function passesRoot(t, inputs, signs) {
  const pos = [], neg = [];
  for (let k=0;k<16;k++) {
    const r=k>>2,c=k&3;
    const s=inputs.reduce((v,input,b)=>v^((input===r||input===4+c)?1<<b:0),signs);
    ((t>>>k)&1?pos:neg).push(s);
  }
  const forPos=pos.map(p=>neg.map(n=>p&~n));
  const forNeg=neg.map(n=>pos.map(p=>p&~n));
  const allows=(a,b,requirements)=>requirements.every(ds=>ds.every(d=>d&a)||ds.every(d=>d&b));
  for(let a=1;a<32;a++) {
    const b=63^a;
    if(allows(a,b,forPos)||allows(a,b,forNeg))return true;
  }
  return false;
}
function classifySupport(t,rows,cols,r,c) {
  const inputs=[];let signs=0;
  for(const [values,omit,offset] of [[rows,r,0],[cols,c,4]])for(let k=0;k<4;k++)if(k!==omit){
    const a=values[omit],b=values[k],common=a&b;
    if(common!==a&&common!==b)return [false,false,false];
    if(common===b)signs|=1<<inputs.length;
    inputs.push(k+offset);
  }
  if(!passesRoot(t,inputs,signs))return [true,false,false];
  const b=rows[r];
  const constant=(b===0||b===15)&&b===cols[c];
  const normalized=rows.map(row=>row^b);
  return [true,true,!constant||normalized.every(x=>normalized.every(y=>(x&y)===0||x===y))];
}
function census() {
  const table={distinct:0, compare:0,root:0,combined:0,exact:0,errors:0};
  const support={combined:0,exact:0,falsePass:0};
  const examples={};
  const sets=Array.from({length:16},(_,k)=>formulas(k>>2,k&3));
  for(let t=0;t<65536;t++){
    const rows=[0,1,2,3].map(i=>(t>>>(4*i))&15);
    const cols=[0,1,2,3].map(j=>rows.reduce((m,r,i)=>m|(((r>>>j)&1)<<i),0));
    if(new Set(rows).size!==4||new Set(cols).size!==4)continue;
    table.distinct++;
    const best=[false,false,false,false], list=[];
    for(let r=0;r<4;r++)for(let c=0;c<4;c++){
      const stages=[...classifySupport(t,rows,cols,r,c),sets[4*r+c].has(t)];
      for(let k=0;k<4;k++)best[k]||=stages[k];
      support.combined+=+stages[2];support.exact+=+stages[3];support.falsePass+=+(stages[2]&&!stages[3]);
      if(stages[3]&&!stages[2])throw Error("false rejection "+JSON.stringify({t,r,c,stages}));
      if(stages[0])list.push({r,c,stages});
    }
    ["compare","root","combined","exact"].forEach((key,k)=>table[key]+=+best[k]);
    table.errors+=+(best[2]!==best[3]);
    if([0x125,0x136,0x127,0x421].includes(t))examples[t.toString(16)]=list;
  }
  return {table,support,examples};
}

const baseline = check();
const result = census();
assert(result.table.root === 8640 && result.table.combined === 7488 && result.table.errors === 0, "root filter census mismatch");
assert(result.support.combined === 31104 && result.support.exact === 24192 && result.support.falsePass === 6912, "support census mismatch");
const stages = (t,r,c) => result.examples[t.toString(16)].find(x => x.r === r && x.c === c)?.stages.map(Number).join("");
assert(stages(0x0136,3,3)==="1000","root rejection regression");
assert(stages(0x0125,3,3)==="1100","constant-border rejection regression");
assert(stages(0x0127,0,3)==="1110" && stages(0x0127,0,2)==="1111" && stages(0x0127,3,2)==="1111","support provenance regression");

function costBySupport(r,c) {
  const leaves=masks.filter((_,k)=>k!==r&&k!==4+c);
  const dp=Array.from({length:64},()=>new Map());
  for(let s=1;s<64;s++){
    const update=(t,c)=>{if(c<(dp[s].get(t)??127))dp[s].set(t,c);};
    const literal=(t,c)=>{update(t,c);update(t^65535,c+1);};
    if(!(s&(s-1))){literal(leaves[Math.log2(s)],0);continue;}
    for(let p=(s-1)&s;p;p=(p-1)&s){
      const q=s^p;if(p>=q)continue;
      for(const [a,x] of dp[p])for(const [b,y] of dp[q]) {
        literal(a&b,x+y);literal(a|b,x+y);
      }
    }
  }
  return dp[63];
}
function costCensus() {
  const support=Array(7).fill(0),table=Array(7).fill(0),examples={};let gap03=0;
  const sets=Array.from({length:16},(_,k)=>costBySupport(k>>2,k&3));
  for(let t=0;t<65536;t++){
    const rows=[0,1,2,3].map(i=>(t>>>(4*i))&15);
    const cols=[0,1,2,3].map(j=>rows.reduce((a,r,i)=>a|(((r>>>j)&1)<<i),0));
    if(new Set(rows).size!==4||new Set(cols).size!==4)continue;
    const sc=sets.flatMap((m,k)=>m.has(t)?[{r:k>>2,c:k&3,n:m.get(t)}]:[]);
    if(!sc.length)continue;
    for(const {n} of sc)support[n]++;
    const costs=sc.map(x=>x.n);
    const min=Math.min(...costs),max=Math.max(...costs);
    table[min]++;gap03+=+(min===0&&max===3);
    if([0x127,0x135f].includes(t))examples[t.toString(16)]=sc;
  }
  function fixture(r,c,gate,n){
    const seen=new Set;
    function f(node,i,j){
      if(Number.isInteger(node)){seen.add(node);return node<4?node===i:node===4+j;}
      const p=f(node[1],i,j);
      if(node[0]==="not")return !p;
      const q=f(node[2],i,j);
      return node[0]==="and"?p&&q:p||q;
    }
    for(let i=0;i<4;i++)for(let j=0;j<4;j++)assert(+f(gate,i,j)===(0x135f>>>(4*i+j)&1),"cost witness truth");
    assert(seen.size===6&&!seen.has(r)&&!seen.has(4+c),"cost witness support");
    const count=(g,op)=>Number.isInteger(g)?0:+(g[0]===op)+g.slice(1).reduce((s,x)=>s+count(x,op),0);
    assert(count(gate,"not")===n && count(gate,"and")+count(gate,"or")===5,"cost witness gates");
    assert(sets[4*r+c].get(0x135f)===n,"cost witness not minimal for support");
  }
  const a=["or",["or",0,4],["or",["and",1,6],["and",2,5]]];
  const b=["or",4,["and",["not",3],["and",["or",["not",1],6],["or",["not",2],5]]]];
  const transpose=g=>Number.isInteger(g)?g^4:[g[0],...g.slice(1).map(transpose)];
  fixture(3,3,a,0);fixture(0,3,b,3);fixture(3,0,transpose(b),3);
  assert(JSON.stringify(support)===JSON.stringify([384,4416,10368,9024,0,0,0]),"support histogram");
  assert(JSON.stringify(table)===JSON.stringify([384,2688,1152,3264,0,0,0]),"table histogram");
  assert(gap03===288,"gap histogram");
  return {support,table,gap03,examples};
}

console.log(JSON.stringify({ baseline, ...result, costs: costCensus() }));
