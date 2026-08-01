// Unit tests for the viewer's word/braid engine. Run with: node test/engine.test.mjs
import assert from 'node:assert/strict';
import {
  parseWord, simulate, strandPaths, DEMO_WORD, DEMO_OBJECT,
} from '../docs/engine.js';

// --- parsing ---------------------------------------------------------------

{
  const toks = parseWord(DEMO_WORD);
  assert.equal(toks.length, 56, 'demo word has 56 generators');
}

{
  const toks = parseWord('F0+ B1- l r- L+');
  assert.deepEqual(
    toks.map((t) => (t.kind === 'sigma' ? `${t.bed}${t.index}${t.sign}` : `${t.dir}${t.sign}`)),
    ['f01', 'b1-1', 'L1', 'R-1', 'L1'],
    'case-insensitive, bare L/R default to +');
}

{
  const toks = parseWord('f0+#junk f1+\nb0-');
  assert.equal(toks.length, 2, 'comments run to end of line');
  assert.equal(toks[1].bed, 'b');
}

assert.throws(() => parseWord('f0f'), /expected an index and a sign/);
assert.throws(() => parseWord('x'), /unexpected character 'x' \(at position 1\)/);
assert.throws(() => parseWord('f0+ q'), /position 5/);

// --- simulation ------------------------------------------------------------

{
  // The demo word is the identity: it must return every strand to its slot.
  const sim = simulate(DEMO_OBJECT.f, DEMO_OBJECT.b, parseWord(DEMO_WORD));
  const first = sim.levels[0], last = sim.levels[sim.levels.length - 1];
  assert.deepEqual(
    last.front.map((s) => s.home + s.num), first.front.map((s) => s.home + s.num),
    'front strands return home');
  assert.deepEqual(
    last.back.map((s) => s.home + s.num), first.back.map((s) => s.home + s.num),
    'back strands return home');
  assert.deepEqual(first.front.map((s) => s.home + s.num), ['F1', 'F2', 'F3', 'F4']);
  assert.deepEqual(first.back.map((s) => s.home + s.num), ['B4', 'B3', 'B2', 'B1'],
    'back row is left-to-right B_b .. B_1');
  assert.equal(sim.height, 56);
}

assert.throws(() => simulate(2, 0, parseWord('f1+')), /at least 3 front strands/);
assert.throws(() => simulate(0, 1, parseWord('L+')), /needs a front strand/);
assert.throws(() => simulate(4, 4, parseWord('f0+ L+ b5-')), /at least 7 back strands.*step 3/);

{
  // Seam moves: L+ takes F1 to the left end of the back row, R- undoes R+.
  const sim = simulate(1, 1, parseWord('L+ R+ L- R-'));
  const [f1, b1] = [sim.levels[1].front, sim.levels[1].back];
  assert.deepEqual(f1.map((s) => s.home + s.num), []);
  assert.deepEqual(b1.map((s) => s.home + s.num), ['F1', 'B1'], 'F1 appended at left of back');
  const last = sim.levels[4];
  assert.deepEqual(last.front.map((s) => s.home + s.num), ['F1']);
  assert.deepEqual(last.back.map((s) => s.home + s.num), ['B1']);
}

// --- geometry --------------------------------------------------------------

const G = { spacing: 1, bedZ: 1.1, crossZ: 0.45, seamMargin: 1.4 };

{
  // Front positive crossing: the x-lesser strand (F1) deviates toward +z.
  const paths = strandPaths(simulate(2, 0, parseWord('f0+')), G);
  const f1 = paths.strands.find((s) => s.home === 'F' && s.num === 1).segments[0];
  const f2 = paths.strands.find((s) => s.home === 'F' && s.num === 2).segments[0];
  assert.equal(f1.t, 'cross');
  assert.equal(f1.x0, -0.5);
  assert.equal(f1.zMid, G.bedZ + G.crossZ, 'left strand of the pair goes outward (+z)');
  assert.equal(f2.zMid, G.bedZ - G.crossZ);
}

{
  // Back positive crossing: b0+ crosses B1/B2; the higher index (B2, x-lesser)
  // deviates toward +z (toward annulus and observer alike).
  const paths = strandPaths(simulate(0, 2, parseWord('b0+')), G);
  const b2 = paths.strands.find((s) => s.home === 'B' && s.num === 2).segments[0];
  const b1 = paths.strands.find((s) => s.home === 'B' && s.num === 1).segments[0];
  assert.equal(b2.x0, -0.5, 'B2 sits page-left of B1');
  assert.equal(b2.zMid, -G.bedZ + G.crossZ, 'higher back index crosses over');
  assert.equal(b1.zMid, -G.bedZ - G.crossZ);
}

{
  // Seam segment endpoints and apex.
  const paths = strandPaths(simulate(1, 0, parseWord('L+')), G);
  const seg = paths.strands[0].segments[0];
  assert.deepEqual(
    { t: seg.t, x0: seg.x0, z0: seg.z0, x1: seg.x1, z1: seg.z1, apexX: seg.apexX },
    { t: 'seam', x0: 0, z0: G.bedZ, x1: 0, z1: -G.bedZ, apexX: -(0 + G.seamMargin) });
}

{
  // Demo paths: every strand has one segment per step, chained continuously.
  const sim = simulate(DEMO_OBJECT.f, DEMO_OBJECT.b, parseWord(DEMO_WORD));
  const paths = strandPaths(sim, G);
  assert.equal(paths.strands.length, 8);
  const startOf = (s) => (s.t === 'cross' ? [s.x0, s.zBed] : s.t === 'seam' ? [s.x0, s.z0] : [s.x0, s.z]);
  const endOf = (s) => (s.t === 'cross' ? [s.x1, s.zBed] : s.t === 'seam' ? [s.x1, s.z1] : [s.x1, s.z]);
  for (const strand of paths.strands) {
    assert.equal(strand.segments.length, sim.height, 'one segment per step');
    strand.segments.forEach((seg, k) => {
      assert.equal(seg.y, k, 'segments stack one unit per step');
      if (k > 0) {
        assert.deepEqual(startOf(seg), endOf(strand.segments[k - 1]),
          `strand ${strand.home}${strand.num} continuous at level ${k}`);
      }
      if (seg.t === 'straight') {
        assert.ok(Math.abs(seg.z) === G.bedZ, 'in-bed strands stay at bed z');
      }
    });
  }
  // Max bed count over the demo is 6 (seam slides) -> half-width 2.5.
  assert.equal(paths.maxHalf, 2.5);
  assert.equal(paths.seamX, 2.5 + G.seamMargin);
}

console.log('all engine tests passed');
