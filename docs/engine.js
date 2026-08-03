// Pure word/braid engine for the tube groupoid viewer.
// No DOM or three.js dependencies, so it can be unit-tested under node.

// The demo the site loads with: at (4, 4), each line multiplies a relation's
// left-hand side by the inverse of its right-hand side, so the whole word is
// the identity of the tube groupoid, written in a complicated way.
export const DEMO_OBJECT = { f: 4, b: 4 };
export const DEMO_WORD = `f0+ f1+ f0+ f1- f0- f1-   # braid, front bed
f0+ f2+ f0- f2-           # distant commute, front
b0+ b1+ b0+ b1- b0- b1-   # braid, back bed
b0+ b2+ b0- b2-           # distant commute, back
f0+ b0+ f0- b0-           # beds commute
f1+ L+ f0- L-             # L bookkeeping (front)
b0+ L+ b0- L-             # L bookkeeping (back)
f0+ R+ f0- R-             # R bookkeeping (front)
b1+ R+ b0- R-             # R bookkeeping (back)
L+ R+ L- R-               # spiral
f0+ L+ L+ b4- L- L-       # seam slide, left
b0+ R+ R+ f4- R- R-       # seam slide, right`;

// ---------------------------------------------------------------------------
// Parsing.
//
// Generators (case-insensitive, whitespace-insensitive, `#` comments to EOL):
//   f<i>+ / f<i>-   crossing of adjacent front strands, 0-based index i
//   b<j>+ / b<j>-   crossing of adjacent back strands, 0-based index j
//   L+ / L-         leftmost front strand around the left seam (and inverse)
//   R+ / R-         rightmost back strand around the right seam (and inverse)
// Bare L / R are accepted as L+ / R+.
// ---------------------------------------------------------------------------

// Rendering-safety caps (generous for real exploration, small enough that a
// crafted shared link cannot freeze the tab).
export const MAX_STRANDS = 50;      // per bed, at the starting object
export const MAX_GENERATORS = 5000; // tokens in a word
export const MAX_COMPLEXITY = 120000; // total strands × word length

export function parseWord(src) {
  // The syntax is genuinely whitespace-insensitive: strip comments and ALL
  // whitespace first, keeping a map back to original positions for errors.
  const chars = [], origin = [];
  for (let i = 0; i < src.length; i += 1) {
    const c = src[i];
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (/\s/.test(c)) continue;
    chars.push(c); origin.push(i);
  }
  const s = chars.join('');
  const sigmaRe = /(\d+)([+-])/y; // sticky: no per-token slicing of the source
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const lc = s[i].toLowerCase();
    if (lc === 'f' || lc === 'b') {
      sigmaRe.lastIndex = i + 1;
      const m = sigmaRe.exec(s);
      if (!m) throw wordError(`expected an index and a sign after '${s[i]}' (e.g. ${lc}0+)`, origin[i]);
      tokens.push({
        kind: 'sigma', bed: lc, index: parseInt(m[1], 10),
        sign: m[2] === '+' ? 1 : -1, at: origin[i], text: s.slice(i, i + 1 + m[0].length),
      });
      i += 1 + m[0].length;
    } else if (lc === 'l' || lc === 'r') {
      let sign = 1, len = 1;
      if (s[i + 1] === '+' || s[i + 1] === '-') { sign = s[i + 1] === '+' ? 1 : -1; len = 2; }
      tokens.push({
        kind: 'seam', dir: lc === 'l' ? 'L' : 'R', sign, at: origin[i], text: s.slice(i, i + len),
      });
      i += len;
    } else {
      throw wordError(`unexpected character '${s[i]}'`, origin[i]);
    }
    if (tokens.length > MAX_GENERATORS) {
      throw wordError(`word too long: more than ${MAX_GENERATORS} generators`,
        tokens[tokens.length - 1].at);
    }
  }
  return tokens;
}

function wordError(message, at) {
  const e = new Error(`${message} (at position ${at + 1})`);
  e.at = at;
  return e;
}

// ---------------------------------------------------------------------------
// Simulation.
//
// Strands are objects {home: 'F'|'B', num} (colored by their home bed).
// Both beds are kept as left-to-right arrays in world x:
//   front = [F_1, ..., F_f]        (F indexed page-left to page-right)
//   back  = [B_b, ..., B_1]        (B indexed page-right to page-left)
// so L+ moves front[0] to the left end of back (F_1 -> B_{b+1}), and
// R+ moves back[last] to the right end of front (B_1 -> F_{f+1}).
// ---------------------------------------------------------------------------

export function simulate(f0, b0, tokens) {
  if (!Number.isInteger(f0) || !Number.isInteger(b0) || f0 < 0 || b0 < 0) {
    throw new Error('the starting object must be a pair of non-negative integers');
  }
  if (f0 > MAX_STRANDS || b0 > MAX_STRANDS) {
    throw new Error(`too many strands: at most ${MAX_STRANDS} per bed at the start`);
  }
  const complexity = (f0 + b0) * Math.max(tokens.length, 1);
  if (complexity > MAX_COMPLEXITY) {
    throw new Error(`braid too large to render: strands × word length = ${complexity} ` +
      `(max ${MAX_COMPLEXITY})`);
  }
  let front = [], back = [];
  for (let k = 1; k <= f0; k += 1) front.push({ home: 'F', num: k });
  for (let k = 1; k <= b0; k += 1) back.unshift({ home: 'B', num: k });

  const levels = [{ front: front.slice(), back: back.slice() }];
  const steps = [];

  tokens.forEach((t, k) => {
    const f = front.length, b = back.length;
    const here = `the object at step ${k + 1} is (${f}, ${b})`;
    if (t.kind === 'sigma') {
      const bed = t.bed === 'f' ? front : back;
      if (t.index + 2 > bed.length) {
        throw stepError(t, k, `'${t.text}' needs at least ${t.index + 2} ${t.bed === 'f' ? 'front' : 'back'} strands, but ${here}`);
      }
      // Left-to-right slot of the left strand of the crossing pair.
      const p = t.bed === 'f' ? t.index : bed.length - 2 - t.index;
      const tmp = bed[p]; bed[p] = bed[p + 1]; bed[p + 1] = tmp;
      steps.push({ kind: 'sigma', bed: t.bed, p, sign: t.sign });
    } else {
      const move = t.dir + (t.sign > 0 ? '+' : '-');
      let strand;
      if (move === 'L+') {
        if (f < 1) throw stepError(t, k, `'${t.text}' needs a front strand to take, but ${here}`);
        strand = front.shift(); back.unshift(strand);
      } else if (move === 'L-') {
        if (b < 1) throw stepError(t, k, `'${t.text}' needs a back strand to take, but ${here}`);
        strand = back.shift(); front.unshift(strand);
      } else if (move === 'R+') {
        if (b < 1) throw stepError(t, k, `'${t.text}' needs a back strand to take, but ${here}`);
        strand = back.pop(); front.push(strand);
      } else { // R-
        if (f < 1) throw stepError(t, k, `'${t.text}' needs a front strand to take, but ${here}`);
        strand = front.pop(); back.push(strand);
      }
      steps.push({ kind: 'seam', move, strand });
    }
    levels.push({ front: front.slice(), back: back.slice() });
  });

  return { levels, steps, height: steps.length };
}

function stepError(token, stepIndex, message) {
  const e = new Error(message);
  e.at = token.at;
  e.step = stepIndex;
  return e;
}

// ---------------------------------------------------------------------------
// Geometry.
//
// Each step k occupies y in [k, k+1]. Beds sit at z = +bedZ (front) and
// z = -bedZ (back); every bed is recentered on x = 0 at every level.
//
// Crossing sign convention ("left over right from every viewpoint"): in a
// positive crossing the world-x-lesser strand of the pair deviates toward
// +z, the other toward -z. On the front bed the +z side faces the outside
// observer; on the back bed it faces both the annulus and the observer.
// ---------------------------------------------------------------------------

export function strandPaths(sim, opts = {}) {
  const { spacing = 1, bedZ = 1.1, crossZ = 0.45, seamMargin = 1.4 } = opts;
  const { levels, steps } = sim;

  let maxCount = 0;
  for (const lv of levels) maxCount = Math.max(maxCount, lv.front.length, lv.back.length);
  const maxHalf = Math.max(0, (maxCount - 1) / 2) * spacing;
  const seamX = maxHalf + seamMargin;
  const xAt = (p, count) => (p - (count - 1) / 2) * spacing;

  const strands = [];
  const recOf = new Map();
  for (const s of levels[0].front.concat(levels[0].back)) {
    const rec = { home: s.home, num: s.num, segments: [] };
    strands.push(rec);
    recOf.set(s, rec);
  }

  // With no generators at all, still draw one unit of straight strands so the
  // starting object is visible.
  if (steps.length === 0) {
    for (const bedName of ['front', 'back']) {
      const z = bedName === 'front' ? bedZ : -bedZ;
      const bed = levels[0][bedName];
      bed.forEach((s, p) => {
        const x = xAt(p, bed.length);
        recOf.get(s).segments.push({ t: 'straight', y: 0, x0: x, x1: x, z });
      });
    }
  }

  steps.forEach((st, k) => {
    const before = levels[k], after = levels[k + 1];
    const handled = new Set();

    if (st.kind === 'sigma') {
      const bed = st.bed === 'f' ? before.front : before.back;
      const z = st.bed === 'f' ? bedZ : -bedZ;
      const sL = bed[st.p], sR = bed[st.p + 1];
      const xL = xAt(st.p, bed.length), xR = xAt(st.p + 1, bed.length);
      recOf.get(sL).segments.push({ t: 'cross', y: k, x0: xL, x1: xR, zBed: z, zMid: z + st.sign * crossZ });
      recOf.get(sR).segments.push({ t: 'cross', y: k, x0: xR, x1: xL, zBed: z, zMid: z - st.sign * crossZ });
      handled.add(sL); handled.add(sR);
    } else {
      const s = st.strand;
      const fromFront = st.move === 'L+' || st.move === 'R-';
      const leftSeam = st.move[0] === 'L';
      const depBed = fromFront ? before.front : before.back;
      const arrBed = fromFront ? after.back : after.front;
      const arrSlot = leftSeam ? 0 : arrBed.length - 1;
      recOf.get(s).segments.push({
        t: 'seam', y: k,
        x0: xAt(leftSeam ? 0 : depBed.length - 1, depBed.length),
        z0: fromFront ? bedZ : -bedZ,
        x1: xAt(arrSlot, arrBed.length),
        z1: fromFront ? -bedZ : bedZ,
        apexX: leftSeam ? -seamX : seamX,
      });
      handled.add(s);
    }

    // Everyone else glides (and recenters) within its own bed.
    for (const bedName of ['front', 'back']) {
      const z = bedName === 'front' ? bedZ : -bedZ;
      const b0 = before[bedName], b1 = after[bedName];
      b1.forEach((s, p1) => {
        if (handled.has(s)) return;
        const p0 = b0.indexOf(s);
        if (p0 < 0) return; // arrived via seam; already handled
        recOf.get(s).segments.push({
          t: 'straight', y: k, x0: xAt(p0, b0.length), x1: xAt(p1, b1.length), z,
        });
      });
    }
  });

  return { strands, seamX, maxHalf, height: sim.height };
}
