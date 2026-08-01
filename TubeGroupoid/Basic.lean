/-
Copyright (c) 2026 Nat Hurtig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nat Hurtig
-/
import Mathlib

/-!
# The tube groupoid

This file defines the **tube groupoid** on `n` strands, presented by generators and relations:

* `TubeObj n` — the objects: pairs `(f, b)` with `f + b = n` (front and back strand counts);
* `TubeGen n` — the generating quiver: the in-row crossings `σ^F_i`, `σ^B_j` and the two seam
  moves `L`, `R`;
* `TubeRel n` — the relations (braid, row commutation, `L`/`R` bookkeeping, spiral, and seam
  slides), as a hom-relation on the free groupoid over `TubeGen n`;
* `TubeGroupoid n` — the tube groupoid itself: the quotient of the free groupoid on `TubeGen n`
  by `TubeRel n`, a groupoid via `CategoryTheory.Quotient.groupoid`;
* `TubeGroupoid.proj n` — the presentation functor from the free groupoid onto `TubeGroupoid n`.

The full informal description of the presentation and its conventions is in the doc-string of
`TubeGroupoid`.  Composition is diagrammatic throughout: `x ≫ y` is "do `x`, then `y`", matching
the juxtaposition convention `xy` used there.
-/

open CategoryTheory

/-- An object of the tube groupoid on `n` strands: `f` strands on the front row and `b` strands
on the back row, with `f + b = n`. -/
@[ext]
structure TubeObj (n : ℕ) where
  /-- The number of front strands. -/
  f : ℕ
  /-- The number of back strands. -/
  b : ℕ
  /-- The two rows together carry all `n` strands. -/
  sum_eq : f + b = n

/-- The generating quiver of the tube groupoid on `n` strands: the in-row crossings `σ^F_i` and
`σ^B_j`, and the two seam moves `L` and `R`.  Indices are 1-based, matching the informal
presentation in the doc-string of `TubeGroupoid`; the seam moves are stated at source objects
`(f + 1, b)` resp. `(f, b + 1)` so that no truncated subtraction appears. -/
inductive TubeGen (n : ℕ) : TubeObj n → TubeObj n → Type where
  /-- `σ^F_i` (`1 ≤ i ≤ f - 1`): the crossing of the adjacent front strands `F_i` and
  `F_{i+1}`. -/
  | sigmaF (f b : ℕ) (h : f + b = n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < f) :
      TubeGen n ⟨f, b, h⟩ ⟨f, b, h⟩
  /-- `σ^B_j` (`1 ≤ j ≤ b - 1`): the crossing of the adjacent back strands `B_j` and
  `B_{j+1}`. -/
  | sigmaB (f b : ℕ) (h : f + b = n) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < b) :
      TubeGen n ⟨f, b, h⟩ ⟨f, b, h⟩
  /-- `L : (f + 1, b) → (f, b + 1)`: the leftmost front strand travels up the left seam and
  appends at the left end of the back row (no reindexing of B). -/
  | L (f b : ℕ) (h : f + 1 + b = n) : TubeGen n ⟨f + 1, b, h⟩ ⟨f, b + 1, by omega⟩
  /-- `R : (f, b + 1) → (f + 1, b)`: the rightmost back strand travels down the right seam and
  appends at the right end of the front row (no reindexing of F). -/
  | R (f b : ℕ) (h : f + (b + 1) = n) : TubeGen n ⟨f, b + 1, h⟩ ⟨f + 1, b, by omega⟩

instance (n : ℕ) : Quiver (TubeObj n) :=
  ⟨TubeGen n⟩

/-- A generating move, viewed as an arrow of the free groupoid on the generating quiver. -/
abbrev TubeGen.free {n : ℕ} {X Y : TubeObj n} (g : TubeGen n X Y) :
    (Quiver.FreeGroupoid.of (TubeObj n)).obj X ⟶ (Quiver.FreeGroupoid.of (TubeObj n)).obj Y :=
  (Quiver.FreeGroupoid.of (TubeObj n)).map g

open TubeGen in
/-- The relations of the tube groupoid, as a hom-relation on the free groupoid over `TubeGen n`.
Each relation of the informal presentation is imposed wherever both sides parse; the source
objects are parametrized (e.g. as `(f + 1, b)`) so that every side condition is subtraction-free.
Composition is diagrammatic (`≫`), matching the convention `xy` = "do `x`, then `y`". -/
inductive TubeRel (n : ℕ) : HomRel (Quiver.FreeGroupoid (TubeObj n)) where
  /-- Braid relation for adjacent crossings in the front row:
  `σ^F_i σ^F_{i+1} σ^F_i = σ^F_{i+1} σ^F_i σ^F_{i+1}`. -/
  | braidF (f b : ℕ) (h : f + b = n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < f) :
      TubeRel n
        ((sigmaF f b h i h1 (by omega)).free ≫ (sigmaF f b h (i + 1) (by omega) h2).free ≫
          (sigmaF f b h i h1 (by omega)).free)
        ((sigmaF f b h (i + 1) (by omega) h2).free ≫ (sigmaF f b h i h1 (by omega)).free ≫
          (sigmaF f b h (i + 1) (by omega) h2).free)
  /-- Distant crossings in the front row commute: `σ^F_i σ^F_j = σ^F_j σ^F_i` for
  `|i - j| ≥ 2`.  Stated only for `i + 2 ≤ j`; the other order is the same relation read
  backwards, so it holds in the quotient by symmetry. -/
  | commF (f b : ℕ) (h : f + b = n) (i j : ℕ) (h1 : 1 ≤ i) (hij : i + 2 ≤ j) (h2 : j < f) :
      TubeRel n
        ((sigmaF f b h i h1 (by omega)).free ≫ (sigmaF f b h j (by omega) h2).free)
        ((sigmaF f b h j (by omega) h2).free ≫ (sigmaF f b h i h1 (by omega)).free)
  /-- Braid relation for adjacent crossings in the back row:
  `σ^B_j σ^B_{j+1} σ^B_j = σ^B_{j+1} σ^B_j σ^B_{j+1}`. -/
  | braidB (f b : ℕ) (h : f + b = n) (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 1 < b) :
      TubeRel n
        ((sigmaB f b h j h1 (by omega)).free ≫ (sigmaB f b h (j + 1) (by omega) h2).free ≫
          (sigmaB f b h j h1 (by omega)).free)
        ((sigmaB f b h (j + 1) (by omega) h2).free ≫ (sigmaB f b h j h1 (by omega)).free ≫
          (sigmaB f b h (j + 1) (by omega) h2).free)
  /-- Distant crossings in the back row commute: `σ^B_i σ^B_j = σ^B_j σ^B_i` for
  `|i - j| ≥ 2`.  Stated only for `i + 2 ≤ j`; the other order is the same relation read
  backwards, so it holds in the quotient by symmetry. -/
  | commB (f b : ℕ) (h : f + b = n) (i j : ℕ) (h1 : 1 ≤ i) (hij : i + 2 ≤ j) (h2 : j < b) :
      TubeRel n
        ((sigmaB f b h i h1 (by omega)).free ≫ (sigmaB f b h j (by omega) h2).free)
        ((sigmaB f b h j (by omega) h2).free ≫ (sigmaB f b h i h1 (by omega)).free)
  /-- The rows commute: `σ^F_i σ^B_j = σ^B_j σ^F_i`. -/
  | commFB (f b : ℕ) (h : f + b = n) (i j : ℕ) (hi1 : 1 ≤ i) (hif : i < f) (hj1 : 1 ≤ j)
      (hjb : j < b) :
      TubeRel n
        ((sigmaF f b h i hi1 hif).free ≫ (sigmaB f b h j hj1 hjb).free)
        ((sigmaB f b h j hj1 hjb).free ≫ (sigmaF f b h i hi1 hif).free)
  /-- `L` bookkeeping, front row: `σ^F_{i+1} L = L σ^F_i` (the departure of the leftmost front
  strand shifts the front indices down). -/
  | slideFL (f b : ℕ) (h : f + 1 + b = n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < f) :
      TubeRel n
        ((sigmaF (f + 1) b h (i + 1) (by omega) (by omega)).free ≫ (L f b h).free)
        ((L f b h).free ≫ (sigmaF f (b + 1) (by omega) i h1 h2).free)
  /-- `L` bookkeeping, back row: `σ^B_j L = L σ^B_j` (arrival by appending never disturbs the
  back indices). -/
  | slideBL (f b : ℕ) (h : f + 1 + b = n) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < b) :
      TubeRel n
        ((sigmaB (f + 1) b h j h1 h2).free ≫ (L f b h).free)
        ((L f b h).free ≫ (sigmaB f (b + 1) (by omega) j h1 (by omega)).free)
  /-- `R` bookkeeping, front row: `σ^F_i R = R σ^F_i` (arrival by appending never disturbs the
  front indices). -/
  | slideFR (f b : ℕ) (h : f + (b + 1) = n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < f) :
      TubeRel n
        ((sigmaF f (b + 1) h i h1 h2).free ≫ (R f b h).free)
        ((R f b h).free ≫ (sigmaF (f + 1) b (by omega) i h1 (by omega)).free)
  /-- `R` bookkeeping, back row: `σ^B_{j+1} R = R σ^B_j` (the departure of the rightmost back
  strand shifts the back indices down). -/
  | slideBR (f b : ℕ) (h : f + (b + 1) = n) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < b) :
      TubeRel n
        ((sigmaB f (b + 1) h (j + 1) (by omega) (by omega)).free ≫ (R f b h).free)
        ((R f b h).free ≫ (sigmaB (f + 1) b (by omega) j h1 h2).free)
  /-- The spiral relation: `L R = R L` (imposed for `f ≥ 1` and `b ≥ 1`, stated here at the
  object `(f + 1, b + 1)`). -/
  | spiral (f b : ℕ) (h : f + 1 + (b + 1) = n) :
      TubeRel n
        ((L f (b + 1) h).free ≫ (R f (b + 1) (by omega)).free)
        ((R (f + 1) b h).free ≫ (L (f + 1) b (by omega)).free)
  /-- The left seam slide: `σ^F_1 L L = L L σ^B_{b+1}` (imposed for `f ≥ 2`, stated here at the
  object `(f + 2, b)`). -/
  | seamL (f b : ℕ) (h : f + 1 + 1 + b = n) :
      TubeRel n
        ((sigmaF (f + 1 + 1) b h 1 (by omega) (by omega)).free ≫
          (L (f + 1) b h).free ≫ (L f (b + 1) (by omega)).free)
        ((L (f + 1) b h).free ≫ (L f (b + 1) (by omega)).free ≫
          (sigmaB f (b + 1 + 1) (by omega) (b + 1) (by omega) (by omega)).free)
  /-- The right seam slide: `σ^B_1 R R = R R σ^F_{f+1}` (imposed for `b ≥ 2`, stated here at the
  object `(f, b + 2)`). -/
  | seamR (f b : ℕ) (h : f + (b + 1 + 1) = n) :
      TubeRel n
        ((sigmaB f (b + 1 + 1) h 1 (by omega) (by omega)).free ≫
          (R f (b + 1) h).free ≫ (R (f + 1) b (by omega)).free)
        ((R f (b + 1) h).free ≫ (R (f + 1) b (by omega)).free ≫
          (sigmaF (f + 1 + 1) b (by omega) (f + 1) (by omega) (by omega)).free)

/--
This one pins itself down nicely: once you fix which seam a move uses, there's no choice about
*which* strand travels — it's whichever strand is adjacent to that seam. So "L takes from F"
forces it to take $F_1$ (the strand next to the left seam), and "R takes from B" forces it to
take $B_1$ (next to the right seam, since B is indexed from the page-right). Both moves
therefore take from the *head* of one row and append to the *tail* of the other, in observer
coordinates — this is the FIFO-queue convention, and you'll see below that it's the most
symmetric of the three.

**Conventions.** Diagrammatic composition ($xy$ = do $x$, then $y$); F at the bottom, indexed
$1,\dots,f$ page-left to page-right; B on top, indexed $1,\dots,b$ page-right to page-left;
observer's crossing signs, preserved across both seams.

**Generators.** Objects $(f,b)$, $f+b=n$:

$$
\sigma^F_i\colon (f,b)\to(f,b)\;\;(1\le i\le f-1),\qquad
\sigma^B_j\colon (f,b)\to(f,b)\;\;(1\le j\le b-1),
$$
$$
L\colon (f,b)\to(f-1,\,b+1)\;\;(f\ge 1)\qquad\text{$F_1$ up the left edge, arriving as $B_{b+1}$
(appended, no reindexing of B)},
$$
$$
R\colon (f,b)\to(f+1,\,b-1)\;\;(b\ge 1)\qquad\text{$B_1$ down the right edge, arriving as
$F_{f+1}$ (appended, no reindexing of F)}.
$$

**Relations** (imposed wherever both sides parse):

$$
\begin{aligned}
&\sigma^X_i\sigma^X_{i+1}\sigma^X_i=\sigma^X_{i+1}\sigma^X_i\sigma^X_{i+1},\qquad
\sigma^X_i\sigma^X_j=\sigma^X_j\sigma^X_i\;\;(|i-j|\ge 2),\quad X\in\{F,B\}
&&\text{(braid, each row)}\\[4pt]
&\sigma^F_i\,\sigma^B_j=\sigma^B_j\,\sigma^F_i
&&\text{(rows commute)}\\[4pt]
&\sigma^F_{i+1}\,L=L\,\sigma^F_i\;\;(1\le i\le f-2),
\qquad \sigma^B_j\,L=L\,\sigma^B_j\;\;(1\le j\le b-1)
&&\text{($L$ bookkeeping)}\\[4pt]
&\sigma^F_i\,R=R\,\sigma^F_i\;\;(1\le i\le f-1),
\qquad \sigma^B_{j+1}\,R=R\,\sigma^B_j\;\;(1\le j\le b-2)
&&\text{($R$ bookkeeping)}\\[4pt]
&LR=RL\;\;(f\ge 1,\; b\ge 1)
&&\text{(spiral)}\\[4pt]
&\sigma^F_1\,LL=LL\,\sigma^B_{b+1}\;\;(f\ge 2),
\qquad \sigma^B_1\,RR=RR\,\sigma^F_{f+1}\;\;(b\ge 2)
&&\text{(seam slides)}
\end{aligned}
$$

The bookkeeping is now lopsided in a pleasant way: because both moves *append*, arrival never
disturbs the receiving row's indices — only removal shifts anything (departing $F_1$ shifts F
down; departing $B_1$ shifts B down). The untouched crossings are $\sigma^F_1$ for $L$ and
$\sigma^B_1$ for $R$ (the ones grabbing the departing strand), and those are exactly the
crossings consumed by the seam-slide relations.

Three remarks on this vocabulary. First, symmetry: the entire presentation is *literally*
invariant under the involution $(f,b)\leftrightarrow(b,f)$, $\sigma^F\leftrightarrow\sigma^B$,
$L\leftrightarrow R$ — check each line against its partner. Geometrically this is the half-turn
of the cylinder (front and back trade places, the two seams swap), and unlike the previous two
conventions, here it holds on the nose with no index gymnastics: $L$ and $R$ are the same move
seen from the other side. The left-right mirror, by contrast, is now hidden (it acts by
$L\leftrightarrow R^{-1}$).

Second, the rotation: $\rho := LR = RL$ is a positive two-letter loop at every object, and in
this convention it's the rotation in which every strand steps from F toward B across the left
seam and from B toward F across the right — the *opposite* direction from the previous message's
$\tau_{\mathrm{rot}}$, so $\rho = \tau_{\mathrm{rot}}^{-1}$ if you're keeping both conventions
on the table. Note $LR$ parses even at $b=0$, where it degenerates into the pure "around the
back" move: $F_1$ up the left, straight across the (otherwise empty) back, down the right into
the last slot. So at the basepoint $(n,0)$,

$$
\rho = LR, \qquad \tau_B = LR\,\bigl(\sigma^F_{n-1}\cdots\sigma^F_1\bigr)^{-1}
$$

up to the standing caveat about which side of the hole the loop hugs (which decides the signs in
the sweep).

Third, the cost is the same one as last time: positive words contain loops ($LR$ itself), so
there's no monotone grading on objects and no free sorted-normal-form argument. If you want
that, the both-take vocabulary from two messages ago remains the graded one, and the translation
is a one-liner: this $L$ is that $L$, and this $R$ is that $R^{-1}$.
-/
def TubeGroupoid (n : ℕ) : Type :=
  CategoryTheory.Quotient (TubeRel n)

instance (n : ℕ) : Groupoid (TubeGroupoid n) :=
  inferInstanceAs (Groupoid (CategoryTheory.Quotient (TubeRel n)))

/-- The presentation functor, from the free groupoid on the generating quiver onto the tube
groupoid.  Generators are sent to their classes, and the relations `TubeRel n` become equalities
of morphisms in `TubeGroupoid n`. -/
def TubeGroupoid.proj (n : ℕ) : Quiver.FreeGroupoid (TubeObj n) ⥤ TubeGroupoid n :=
  CategoryTheory.Quotient.functor (TubeRel n)

/-!
Smoke tests: the generators are inhabited at small objects, the rotation `ρ = L R` parses even
with an empty back row, and the relations really identify morphisms in the quotient.  These
guard the presentation against silent index or side-condition drift under future edits.
-/

section SmokeTests

open TubeGen

/- With both of two strands on the front row, the single braid generator `σ^F_1` exists. -/
example : TubeGen 2 ⟨2, 0, rfl⟩ ⟨2, 0, rfl⟩ := sigmaF 2 0 rfl 1 le_rfl one_lt_two

/- The rotation `ρ = L R` is a loop at the basepoint `(n + 1, 0)`: it parses even with an empty
back row, where it degenerates into the pure "around the back" move. -/
example (n : ℕ) :
    (Quiver.FreeGroupoid.of (TubeObj (n + 1))).obj ⟨n + 1, 0, by omega⟩ ⟶
      (Quiver.FreeGroupoid.of (TubeObj (n + 1))).obj ⟨n + 1, 0, by omega⟩ :=
  (L n 0 (by omega)).free ≫ (R n 0 (by omega)).free

/- The spiral relation `L R = R L` becomes an equality of morphisms in the tube groupoid,
here at the object `(1, 1)` of the two-strand groupoid. -/
example :
    (TubeGroupoid.proj 2).map ((L 0 1 (by omega)).free ≫ (R 0 1 (by omega)).free) =
      (TubeGroupoid.proj 2).map ((R 1 0 (by omega)).free ≫ (L 1 0 (by omega)).free) :=
  CategoryTheory.Quotient.sound _ (TubeRel.spiral 0 0 (by omega))

end SmokeTests
