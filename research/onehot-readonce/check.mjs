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
console.log(JSON.stringify(check()));
