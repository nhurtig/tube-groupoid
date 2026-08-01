import * as THREE from './three.module.js';
import { parseWord, simulate, strandPaths, DEMO_WORD, DEMO_OBJECT } from './engine.js';

// --- constants -------------------------------------------------------------

const GEOM = { spacing: 1, bedZ: 1.1, crossZ: 0.45, seamMargin: 1.4 };
const STRAND_RADIUS = 0.07;
const OUTLINE_RADIUS = 0.17;
const FRONT_CAM_DIST = 7;      // camera z in front view: bedZ + FRONT_CAM_DIST
const MOVE_SPEED = 5;          // world units / second
const LOOK_SPEED = 0.005;      // radians / pixel
const COLORS = { F: 0xd62828, B: 0x1d4ed8, outline: 0x1c1c1c, bg: 0xfafafa };

// --- renderer / scene ------------------------------------------------------

const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setPixelRatio(window.devicePixelRatio);
renderer.setSize(window.innerWidth, window.innerHeight);
document.getElementById('scene').appendChild(renderer.domElement);

const scene = new THREE.Scene();
scene.background = new THREE.Color(COLORS.bg);

const camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 0.05, 500);
camera.rotation.order = 'YXZ';

window.addEventListener('resize', () => {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
});

// --- seam curve: eased arc around a seam, vertical tangents at both ends ---

class SeamCurve extends THREE.Curve {
  constructor(seg) { super(); this.seg = seg; }
  getPoint(t, target = new THREE.Vector3()) {
    const s = this.seg;
    const e = t * t * (3 - 2 * t); // smoothstep: vertical entry and exit
    const xm = (s.x0 + s.x1) / 2;
    const x = s.x0 + (s.x1 - s.x0) * e + (s.apexX - xm) * Math.sin(Math.PI * e);
    const z = s.z0 * Math.cos(Math.PI * e); // z1 === -z0 for every seam move
    return target.set(x, s.y + t, z);
  }
}

function segmentCurve(seg) {
  const v = (x, y, z) => new THREE.Vector3(x, y, z);
  if (seg.t === 'straight') {
    return new THREE.CubicBezierCurve3(
      v(seg.x0, seg.y, seg.z), v(seg.x0, seg.y + 0.4, seg.z),
      v(seg.x1, seg.y + 0.6, seg.z), v(seg.x1, seg.y + 1, seg.z));
  }
  if (seg.t === 'cross') {
    const xm = (seg.x0 + seg.x1) / 2;
    const path = new THREE.CurvePath();
    path.add(new THREE.CubicBezierCurve3(
      v(seg.x0, seg.y, seg.zBed), v(seg.x0, seg.y + 0.25, seg.zBed),
      v(xm, seg.y + 0.25, seg.zMid), v(xm, seg.y + 0.5, seg.zMid)));
    path.add(new THREE.CubicBezierCurve3(
      v(xm, seg.y + 0.5, seg.zMid), v(xm, seg.y + 0.75, seg.zMid),
      v(seg.x1, seg.y + 0.75, seg.zBed), v(seg.x1, seg.y + 1, seg.zBed)));
    return path;
  }
  return new SeamCurve(seg);
}

// --- braid group (rebuilt on every word edit) ------------------------------

let braidGroup = null;
const current = {
  height: 1, capX: 2,
  counts: [[0, 0]],  // per level: [front count, back count]
};

function disposeGroup(group) {
  group.traverse((o) => {
    if (o.geometry) o.geometry.dispose();
    if (o.material) {
      if (o.material.map) o.material.map.dispose();
      o.material.dispose();
    }
  });
  scene.remove(group);
}

function buildBraid(paths) {
  const group = new THREE.Group();
  for (const strand of paths.strands) {
    if (strand.segments.length === 0) continue;
    const path = new THREE.CurvePath();
    for (const seg of strand.segments) path.add(segmentCurve(seg));
    const tubular = Math.max(32, strand.segments.length * 14);
    const core = new THREE.Mesh(
      new THREE.TubeGeometry(path, tubular, STRAND_RADIUS, 10, false),
      new THREE.MeshBasicMaterial({ color: COLORS[strand.home] }));
    const outline = new THREE.Mesh(
      new THREE.TubeGeometry(path, tubular, OUTLINE_RADIUS, 10, false),
      new THREE.MeshBasicMaterial({ color: COLORS.outline, side: THREE.BackSide }));
    group.add(core, outline);
  }
  // Seam rails: faint vertical reference lines where L and R swing around.
  const railMat = new THREE.LineBasicMaterial({ color: 0xc9c9c9 });
  for (const sx of [-paths.seamX, paths.seamX]) {
    const g = new THREE.BufferGeometry().setFromPoints([
      new THREE.Vector3(sx, -0.5, 0), new THREE.Vector3(sx, Math.max(paths.height, 1) + 0.5, 0)]);
    group.add(new THREE.Line(g, railMat));
  }
  return group;
}

// --- F / B letters (annulus mode only, behind the beds) --------------------

function letterMesh(text, faceMinusZ) {
  const cv = document.createElement('canvas');
  cv.width = cv.height = 256;
  const ctx = cv.getContext('2d');
  ctx.clearRect(0, 0, 256, 256);
  ctx.font = 'bold 190px ui-sans-serif, system-ui, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillStyle = '#111';
  ctx.fillText(text, 128, 140);
  const tex = new THREE.CanvasTexture(cv);
  const mesh = new THREE.Mesh(
    new THREE.PlaneGeometry(3.2, 3.2),
    new THREE.MeshBasicMaterial({ map: tex, transparent: true }));
  if (faceMinusZ) mesh.rotation.y = Math.PI;
  scene.add(mesh);
  return mesh;
}

const letterF = letterMesh('F', true);   // beyond the front bed, facing the annulus
const letterB = letterMesh('B', false);  // beyond the back bed, facing the annulus

// --- camera state / controls -----------------------------------------------

const state = {
  mode: 'annulus',            // 'annulus' | 'front'
  x: 0, y: 0,
  look: { annulus: { yaw: Math.PI, pitch: 0 }, front: { yaw: 0, pitch: 0 } },
};
const keys = { up: false, down: false, left: false, right: false };

function camZ() { return state.mode === 'annulus' ? 0 : GEOM.bedZ + FRONT_CAM_DIST; }

function clampCamera() {
  state.x = Math.min(Math.max(state.x, -current.capX), current.capX);
  state.y = Math.min(Math.max(state.y, 0), Math.max(current.height, 1));
}

function setMode(mode) {
  state.mode = mode;
  if (mode === 'front') state.look.front = { yaw: 0, pitch: 0 }; // level, toward the front bed
  document.getElementById('viewBtn').textContent =
    mode === 'annulus' ? 'View: annulus (press V for front)' : 'View: front (press V for annulus)';
}

document.getElementById('viewBtn').addEventListener('click', () => {
  setMode(state.mode === 'annulus' ? 'front' : 'annulus');
});

// Pointer look (left-drag pans the frustum in both views).
let dragging = false;
renderer.domElement.addEventListener('pointerdown', (e) => {
  if (e.button !== 0) return;
  dragging = true;
  renderer.domElement.setPointerCapture(e.pointerId);
});
renderer.domElement.addEventListener('pointerup', (e) => {
  if (e.button !== 0) return;
  dragging = false;
  if (renderer.domElement.hasPointerCapture(e.pointerId)) {
    renderer.domElement.releasePointerCapture(e.pointerId);
  }
});
renderer.domElement.addEventListener('pointermove', (e) => {
  if (!dragging) return;
  const look = state.look[state.mode];
  look.yaw -= e.movementX * LOOK_SPEED;
  look.pitch -= e.movementY * LOOK_SPEED;
  look.pitch = Math.min(Math.max(look.pitch, -1.52), 1.52);
});

function isEditing(e) {
  const t = e.target;
  return t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.isContentEditable);
}

window.addEventListener('keydown', (e) => {
  if (isEditing(e)) return;
  let used = true;
  switch (e.code) {
    case 'KeyW': case 'ArrowUp': case 'Space': keys.up = true; break;
    case 'KeyS': case 'ArrowDown': keys.down = true; break;
    case 'ShiftLeft': case 'ShiftRight': keys.down = true; break;
    case 'KeyA': case 'ArrowLeft': keys.left = true; break;
    case 'KeyD': case 'ArrowRight': keys.right = true; break;
    case 'KeyV': setMode(state.mode === 'annulus' ? 'front' : 'annulus'); break;
    case 'Escape': closeHelp(); break;
    default: used = false;
  }
  if (used) e.preventDefault();
});
window.addEventListener('blur', () => {
  keys.up = keys.down = keys.left = keys.right = false;
  dragging = false;
});
window.addEventListener('keyup', (e) => {
  switch (e.code) {
    case 'KeyW': case 'ArrowUp': case 'Space': keys.up = false; break;
    case 'KeyS': case 'ArrowDown': keys.down = false; break;
    case 'ShiftLeft': case 'ShiftRight': keys.down = false; break;
    case 'KeyA': case 'ArrowLeft': keys.left = false; break;
    case 'KeyD': case 'ArrowRight': keys.right = false; break;
    default: break;
  }
});

// --- live word input -------------------------------------------------------

const fInput = document.getElementById('fInput');
const bInput = document.getElementById('bInput');
const wordInput = document.getElementById('wordInput');
const errBox = document.getElementById('errBox');

if (!wordInput.value.trim()) {
  wordInput.value = DEMO_WORD;
  fInput.value = DEMO_OBJECT.f;
  bInput.value = DEMO_OBJECT.b;
}

function rebuild() {
  const f = Math.max(0, Math.floor(Number(fInput.value) || 0));
  const b = Math.max(0, Math.floor(Number(bInput.value) || 0));
  let paths, sim;
  try {
    const tokens = parseWord(wordInput.value);
    sim = simulate(f, b, tokens);
    paths = strandPaths(sim, GEOM);
  } catch (err) {
    errBox.textContent = err.message;
    errBox.hidden = false;
    return; // keep showing the last good braid
  }
  errBox.hidden = true;
  if (braidGroup) disposeGroup(braidGroup);
  braidGroup = buildBraid(paths);
  scene.add(braidGroup);
  current.height = paths.height;
  current.capX = Math.max(paths.maxHalf, 1);
  current.counts = sim.levels.map((lv) => [lv.front.length, lv.back.length]);
  clampCamera(); // if the word shrank, the camera comes back into range
}

let rebuildTimer = null;
function scheduleRebuild() {
  clearTimeout(rebuildTimer);
  rebuildTimer = setTimeout(rebuild, 80);
}
for (const el of [fInput, bInput, wordInput]) el.addEventListener('input', scheduleRebuild);

// --- help modal ------------------------------------------------------------

const helpModal = document.getElementById('helpModal');
function openHelp() { helpModal.hidden = false; }
function closeHelp() { helpModal.hidden = true; }
document.getElementById('helpBtn').addEventListener('click', openHelp);
document.getElementById('helpClose').addEventListener('click', closeHelp);
helpModal.addEventListener('click', (e) => { if (e.target === helpModal) closeHelp(); });
openHelp(); // pops up on first load

// --- render loop -----------------------------------------------------------

const hud = document.getElementById('hud');
let lastT = performance.now();

function frame(now) {
  const dt = Math.min((now - lastT) / 1000, 0.1);
  lastT = now;

  const step = MOVE_SPEED * dt;
  const dy = (keys.up ? 1 : 0) - (keys.down ? 1 : 0);
  const lr = (keys.right ? 1 : 0) - (keys.left ? 1 : 0);
  if (lr !== 0) {
    // 'd' goes toward the frustum's right, projected onto the x axis.
    const right = new THREE.Vector3(1, 0, 0).applyQuaternion(camera.quaternion);
    state.x += lr * (right.x >= 0 ? 1 : -1) * step;
  }
  state.y += dy * step;
  clampCamera();

  const look = state.look[state.mode];
  camera.position.set(state.x, state.y, camZ());
  camera.rotation.set(look.pitch, look.yaw, 0);

  const lettersOn = state.mode === 'annulus';
  letterF.visible = lettersOn;
  letterB.visible = lettersOn;
  if (lettersOn) {
    letterF.position.set(0, state.y, GEOM.bedZ + 2.4);
    letterB.position.set(0, state.y, -GEOM.bedZ - 2.4);
  }

  const lvl = Math.min(Math.max(Math.floor(state.y), 0), current.counts.length - 1);
  const [cf, cb] = current.counts[lvl];
  hud.textContent =
    `y ${state.y.toFixed(1)} / ${current.height} · object here: (${cf}, ${cb})`;

  renderer.render(scene, camera);
  requestAnimationFrame(frame);
}

setMode('annulus');
rebuild();
requestAnimationFrame(frame);
