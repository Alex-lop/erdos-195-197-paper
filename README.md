# Monotone arithmetic progressions in lists of the integers

**Partial results on Erdős problems #195 and #197**

Alex Lopez, with Claude (Anthropic). Draft of 12 November 2026.

**PDF version:** [erdos-195-197.pdf](erdos-195-197.pdf), typeset from [erdos-195-197.tex](erdos-195-197.tex) (`tectonic erdos-195-197.tex` rebuilds it). The PDF and this page have the same text.

> **Read this first.** Both problems are open and this paper solves neither. It collects what one project proved, checked by computer, or ruled out, and it says for every statement which of the three it is. The main theorems are verified in the Lean 4 proof assistant, in eight public repositories (table in §7). **No part of this work has been reviewed by a human mathematician.**

## Abstract

Write all the integers in a list, in any order you like, each one exactly once. An arithmetic progression is *monotone* in your list if its terms appear from left to right in increasing order, or in decreasing order. Two problems of Erdős and Graham ask how well a list can avoid monotone progressions.

- **Problem #195.** Every list of the integers contains a monotone progression with 3 terms, and some list contains none with 5 terms. *Is there a list with no monotone progression of 4 terms?*
- **Problem #197.** No list of the positive integers avoids monotone 3-term progressions. *Can the positive integers be split into two sets, each of which has a list that does?*

This paper reports partial results from a project in which AI agents (Claude), directed by Alex Lopez, searched for constructions and for impossibility proofs, attacked each other's claims, and formalized the survivors.

**On #195 we get close from the construction side, and then show that this road ends.** We give lists of the integers that avoid monotone 4-term progressions for more and more common differences *d*: every odd *d*; every *d* not divisible by 4; and one list in which, for each power of two, only finitely many monotone progressions have a difference divisible by exactly that power. Deleting a set of density zero from the last list leaves almost all integers, listed with no monotone 4-term progression at all. But the deleted set cannot be put back in the two most natural ways, and computer-checked certificates show that no list built on the same block layout works, for wide ranges of its parameters.

**On #197 we rule out the natural candidate splittings, one family at a time:** splittings whose lists stay close to increasing order; splittings into long alternating runs (this includes the classical "dyadic" one); splittings with an odd number of equal runs per octave; splittings defined by an irrational rotation; and, with a hand proof, random splittings.

**One idea runs through all of it.** Inside a finite block of integers there is a perfect way to avoid progressions: sort by binary digits read from the right (the *2-adic order*). It is essentially the only way, because orders without monotone 3-term progressions are rigid. But a list must reach every integer after finitely many steps, so blocks have to be cut by size, and the progressions that straddle a cut are where every construction leaks and where every impossibility proof gets its grip.

**How much to trust it.** Statements marked **[Lean]** are checked by the Lean kernel. **[Certified]** means a finite search problem was refuted by a SAT solver and the proof certificate was checked by a separate program. **[Hand]** means a written proof, with the number of adversarial AI referees it survived. **[Evidence]** means one program said so. Nothing here bears on whether the answer to #195 is 3 or 4, and we do not know whether the answer to #197 is yes or no.

**How to read this.** §2 is the common idea, with two complete short proofs. §3 and §4 are #195 (constructions, then obstructions). §5 is #197. §6 says what failed and what is open. §7 is the table of every result with its status and location.

---

## 1. The two problems

A **list** (or *enumeration*) of a set S of integers is a sequence s<sub>0</sub>, s<sub>1</sub>, s<sub>2</sub>, … in which every element of S occurs exactly once. Write x ≺ y when x occurs before y. The important feature is that every element has only finitely many elements before it. "All the even numbers, then all the odd numbers" is not a list.

A progression a, a + d, …, a + (k − 1)d with d ≠ 0 is **monotone** in the list if a ≺ a + d ≺ ⋯ ≺ a + (k − 1)d, or the reverse. A set is **permutable** if it has a list with no monotone 3-term progression.

**Problem #195** ([erdosproblems.com/195](https://www.erdosproblems.com/195)). What is the largest k such that every list of ℤ contains a monotone k-term progression? It is 3 or 4:

- every list of ℤ has a monotone 3-term progression (Davis, Entringer, Graham, Simmons 1977; proof in §2.1);
- some list has no monotone 6-term progression (Geneson 2019), and some list has none with 5 terms (Adenwalla 2022).

So the question is whether some list of ℤ has no monotone 4-term progression (answer 3) or every list has one (answer 4). For the positive integers alone the corresponding question was settled in 2026: B. S. Ho constructed a list of ℕ with no monotone 4-term progression (arXiv:2609.12780). The whole difficulty of #195 is that ℤ has two ends.

**Problem #197** ([erdosproblems.com/197](https://www.erdosproblems.com/197)). Can ℕ be partitioned into two permutable sets? ℕ itself is not permutable (Davis et al.). Three sets are enough (§5.1). W. Kasel showed in 2026 that the most natural two-set candidate, the dyadic partition into blocks (2<sup>k</sup>, 2<sup>k+1</sup>] of alternating colours, fails (arXiv:2609.02939).

## 2. The common mechanism

### 2.1 The midpoint rule, the anchor rule, and doubling chains

**Midpoint rule.** A list has no monotone 3-term progression exactly when, in every progression x < y < z of the set, the middle term y is listed before both ends or after both ends.

**Anchor rule.** Let a < w, with a listed before w. If 2w − a belongs to the set, then 2w − a is listed before w.

*Proof.* In the progression a, w, 2w − a the middle term w is not listed first, so by the midpoint rule it is listed last. ∎

In words: an early element a drags the mirror image of a through w, a number about twice as large as w, in front of w. Everything in this paper about 3-term progressions comes from this rule.

**Theorem (Davis, Entringer, Graham, Simmons).** ℕ is not permutable, and every list of ℤ has a monotone 3-term progression.

*Proof.* Let a be the first element of the list and take any w > a. By the anchor rule w′ = 2w − a comes before w. The rule applies again to w′, so w″ = 2w′ − a comes before w′, and so on. This gives infinitely many elements before w, which a list does not allow. ∎

For a set S that is not everything, the chain w, 2w − a, 2(2w − a) − a, … can leave S, and then the argument stops. The general form is:

**Orbit lemma** (attributed to Kasel in our notes). Let F be a finite subset of S. If S contains an infinite chain u<sub>0</sub> < u<sub>1</sub> < ⋯ with u<sub>k+1</sub> = 2u<sub>k</sub> − f<sub>k</sub> and every f<sub>k</sub> in F, then S is not permutable.

*Proof.* Only finitely many elements are listed before some element of F. So from some k on, f<sub>k</sub> ≺ u<sub>k</sub>, and the anchor rule gives u<sub>k+1</sub> ≺ u<sub>k</sub>: an infinite descent. ∎

So **a permutable set must break every doubling chain**: it needs holes exactly where the chains want to go. That is why #197 asks for two sets. The holes of one set are the other set, and the other set has to break its own chains too.

For 4-term progressions the corresponding rule is: if a is listed before a block, a + 3d after it, and a + d, a + 2d inside it, then a + 2d must come before a + d (otherwise the four terms are in increasing order). We call these the *Case-A relations* of the block.

### 2.2 The 2-adic order: perfect inside a block

Write ν<sub>2</sub>(n) for the number of times 2 divides n. The **2-adic order** puts x before y when the binary digit of x at position ν<sub>2</sub>(y − x) is 0. It lists evens before odds; among the evens, multiples of 4 first; and so on. On {0, …, 7} it gives

```
0, 4, 2, 6, 1, 5, 3, 7
```

**Fact.** No set ordered 2-adically has a monotone 3-term progression. *Proof.* If ν<sub>2</sub>(d) = j, then x and x + 2d have the same binary digit at position j and x + d has the other one. So the middle term is on the same side of both ends. ∎

This is perfect, but it is not a list of an infinite set: infinitely many even numbers would come before the first odd one. A list has to chop the integers into finite blocks by size, order each block 2-adically (or in some other good way), and then list the blocks one after another.

### 2.3 Rigidity: every good order looks 2-adic

The 2-adic order is not just one choice among many.

**Zigzag lemma** (Sharma 2009, Prop. 2.2–2.3; Kasel's "ladder"). In an order of an interval of integers with no monotone 3-term progression, one of the two parity classes is *early*: each of its elements comes before both of its neighbours.

*Proof.* The triple b − 1, b, b + 1 is not monotone, so b is before both neighbours or after both. Two adjacent numbers cannot both be "before both". So the two types alternate. ∎

**Gap lemma** (Sharma 2009, Thm 2.1–2.2). Let p be in the early class and q in the other class. If the mirror image 2p − q or 2q − p is still in the interval, then p comes before q.

So on pairs of opposite parity, every order without monotone 3-term progressions agrees with a 2-adic order as far as the interval allows. A similar statement one level down, for residues modulo 4, is our **Quarter Lemma** (§5.4). This rigidity is the engine of the finite "gadgets" in §5 and of Theorem T0 in §4.4.

### 2.4 Seams

Put §2.1–2.3 together. Inside a block, a good order is forced to be nearly 2-adic. Blocks must be cut by size. A progression that starts in one block and ends in another is not protected by either block's order: the Case-A relations and the anchor rule say what the order near the cut must do, and those demands collide with rigidity. We call a cut inside a residue class a **seam**.

Every construction below is a way of arranging seams so that fewer progressions cross them. Every obstruction below is a proof that some way of arranging seams cannot work.

---

## 3. Problem #195: constructions

Each list here is explicit, and each theorem is **[Lean]**. All of them still contain monotone 4-term progressions with other differences, so none decides #195.

### 3.1 Odd differences

**Theorem 1 [Lean].** There is a list of ℤ with no monotone 4-term progression of odd difference.

*Construction.* Call x ≠ 0 *fast* if it is positive and even, or negative and odd. Give x the key |x|/4 if it is fast and |x| otherwise. List ℤ by increasing key, ties by value:

```
0, -1, 2, -3, 1, 4, -5, 6, -7, -2, 8, -9, 10, -11, 3, 12, ...
```

The proof is a short case analysis: along a 4-term progression with odd difference the keys can never be non-decreasing. Progressions with even difference do occur, for example 2, 4, 6, 8. This is the analogue for ℤ of a 2011 theorem of LeSaulnier and Vijay for ℕ.

### 3.2 Differences not divisible by 4

**Theorem 2 [Lean].** There is a list of ℤ with no monotone 4-term progression whose difference is not divisible by 4.

*Idea ("reflection merge").* List the odd numbers in the order of Theorem 1. Before each odd number y, insert even numbers so that the set of evens listed before y is always symmetric about y. Then no triple even, odd, even with the odd number as midpoint is ever in order, which handles odd differences. Differences ≡ 2 (mod 4) reduce to Theorem 1 on the odd numbers, and to a copy of Theorem 1 with a slowly drifting centre on the even numbers.

### 3.3 Every finite 2-adic depth, and all depths at once

**Theorem G [Lean; a corollary of Geneson 2026, §5].** For every t ≥ 1 there is a list of ℤ with no monotone 4-term progression whose difference is not divisible by 2<sup>t</sup>. (One list for each t.)

**Theorem H [Lean].** There is a single list of ℤ in which, for every v ≥ 0, only finitely many monotone 4-term progressions have ν<sub>2</sub>(d) = v.

*Construction.* Fix the base 3 and moduli m<sub>s</sub> = 2<sup>t<sub>s</sub></sup>. Cut ℤ into finite *bands*: stage s holds the integers whose absolute value lies between two consecutive thresholds, which are powers of 3, and the exact threshold for x depends on its sign and on its residue modulo a power of two. List 0, and then, stage by stage, the negative members of the stage in 2-adic order followed by the positive members in reversed 2-adic order. With t<sub>s</sub> = t constant this is Geneson's block construction without its truncation, and it gives Theorem G. The new ingredient of Theorem H is a modulus that grows with the stage, t<sub>s</sub> = s + 1.

*Why it works.*
- Along a progression with d = 2<sup>j</sup>·(odd), the binary digit at position j alternates. So two consecutive steps can never both go in the direction that the list prescribes.
- Separation lemmas between stages (they need the base to exceed 1 + √2) show that every step *must* go in that direction, with one exception: a **seam step**, which goes from stage s to stage s + 1 inside one residue class modulo m<sub>s+1</sub>.
- So every monotone 4-term progression contains a seam step, which forces 2<sup>t<sub>s+1</sub></sup> to divide d and bounds its terms. If t<sub>s</sub> grows, a fixed ν<sub>2</sub>(d) allows only finitely many stages.

Theorems 1 and 2 are the cases t = 1, 2 of Theorem G, with different constructions. We found them before noticing that Geneson's paper implies them; he does not state the corollary.

### 3.4 A set of density one with no monotone 4-term progression

**Corollary Z1 [Lean].** There is a set S ⊆ ℤ with |S ∩ [−n, n]| / (2n + 1) → 1 and a list of S with no monotone 4-term progression.

S is ℤ minus the *bottom zone* of the Theorem H list: the elements within a factor 7/3 of the lower end of their band. Every seam step lands in the bottom zone, so deleting it removes every monotone progression. The bottom zone has density zero because each zone lies in one residue class of a modulus that grows.

Geneson (2026) showed that such sets exist with density arbitrarily close to 1 and remarked that his construction does not reach density 1. Corollary Z1 reaches it. As far as our referees found, that is new.

| List | No monotone 4-term progression with … | Repository |
| --- | --- | --- |
| key order (Thm 1) | d odd | [erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference) |
| reflection merge (Thm 2) | 4 ∤ d | [erdos-195-difference-not-div-4](https://github.com/Alex-lop/erdos-195-difference-not-div-4) |
| bands, fixed modulus (Thm G) | 2<sup>t</sup> ∤ d | [erdos-195-valuation-bands](https://github.com/Alex-lop/erdos-195-valuation-bands) |
| bands, growing modulus (Thm H) | all but finitely many for each ν<sub>2</sub>(d) | same |
| the same list minus a density-zero set (Z1) | any d | same |

## 4. Problem #195: obstructions

The ladder of §3 stops one rung short. This section explains why we believe it cannot be climbed further by the same method, and what we could and could not prove about any method.

### 4.1 Seams always leak, and the deleted set cannot simply be put back

Every seam carries monotone progressions of the form 0, y, 2y, 3y with y just below the cut. Lean checks two of them: 0, −6, −12, −18 in the Theorem G list with t = 1, and 0, −44, −88, −132 in the Theorem H list.

**Proposition Z3 [Lean].** No list of ℤ that keeps the elements of S (from Corollary Z1) in the same relative order is free of monotone 4-term progressions. Nine elements of S decide it: wherever 280 is inserted, one of (280, 4, −272, −548), (−56, 56, 168, 280), (−40, 280, 600, 920) is monotone.

**Proposition Z3′ [Lean].** The same holds if S is still listed band by band, but the three bands around the first seam are re-ordered by *arbitrary* orders of 2-adic type ("binary orders": an independent choice of which digit goes first at every node of the binary tree). One of 280, 284, 288, 292 always lies on a monotone progression.

These are statements about one instance and its first seam. They do not exclude a repair that re-orders the bands in some non-binary way.

### 4.2 No list that roughly follows size

A list of ℤ has **lag ratio ≤ λ** if, whenever y is listed before x, |y| ≤ λ|x| + C. An increasing-in-size list has lag ratio 1.

**Theorem L1 [Hand, not refereed].** Every list of ℤ with lag ratio < 2 has a monotone 4-term progression.

**Theorem L2 [Certified].** Every list of ℤ with lag ratio ≤ 9/2 has a monotone 4-term progression. This remains true if only pairs of the same sign are controlled, so the relative timing of positives and negatives is free.

The reduction is exact: for each λ, a good list with lag ratio ≤ λ exists if and only if every window [−n, n] has an order satisfying the lag condition with no monotone progression (König's lemma). The window [−140, 140] has none for λ = 9/2. For comparison, the key order of Theorem 1 has lag ratio 3, Adenwalla's 5-term construction has lag ratio below 8, and Ho's list of ℕ places 8 after 2623. A solution of #195 would have to list far elements early, at unbounded ratios.

### 4.3 The block layout cannot be completed: window certificates

Theorems G and H fix a *layout* (which block comes when) and choose the 2-adic order inside blocks. Could a cleverer order inside the same blocks remove the remaining progressions? For wide parameter ranges, no.

**Windows.** Suppose that at some moment a list has listed exactly the integers in (−A, u), and that it now lists the whole block W = [u, w) before anything else. Call W a *sign-split window* with **ratio** w/u and **offset** w/A. A 4-term progression is *decided by the window* if at least two of its terms are in W, at most one was listed before and at most one comes after; whether it is monotone then depends only on the order inside W. The **window problem** SW(u, w, A) asks for an order of W in which no such progression is monotone. If SW(u, w, A) has no solution, no good list passes through that state. A rescaling lemma (multiply everything by M) transfers this to every larger scale with nearly the same ratio and offset.

**Theorem W [Certified].** SW(1, 150, A) has no solution for every A from 10 to 40. Nor do SW(1, 200, 54), SW(1, 144, 12), SW(1, 169, 13), SW(1, 121, 9), SW(1, 130, 9).

**Corollary (dead band) [Certified + Hand; bridge lemmas passed one AI referee per lens].** A list of ℤ with no monotone 4-term progression never lists (−A, u), then all of [u, w), then the rest, when w/u ≥ 200, w ≥ 39800 and the offset w/A lies in [3.704, 16.55]. The mirror statement holds for negative windows.

**Corollary (layouts) [Certified + Hand].** No choice of orders inside the blocks makes Geneson's layout, or the band layout of Theorem H, free of monotone 4-term progressions when the base a lies in (1 + √2, 28/9) or in (3.75, 10.64); the later certificates extend the second range to 16.55. The first range comes from two-window instances, the second from the dead band. This includes the base 3 of Theorem H and Geneson's own integer bases 4, …, 10. Bases between about 3.11 and 3.70, and above 16.55, are not excluded by anything we know.

**The negatives are essential.** If only one sign is present, every single window can be solved: list the top half in reversed 2-adic order and then the bottom half in 2-adic order **[Hand, not refereed; checked on 345 windows]**. The contradiction in Theorem W needs the negative integers that are listed *after* the window. Removing any one of the four families of constraints that involve elements outside the window makes SW(1, 80, 16) solvable. This matches the known picture: ℕ has a good list (Ho), and it is the second end of ℤ that causes trouble.

### 4.4 What the certificates do not give

- **No readable proof.** Minimal contradictory sub-instances keep 74 of the 79 elements of SW(1, 80, 16). A hand theorem **[Hand, no referee round]** says every sub-instance on k elements becomes solvable once the window is large enough, so no finite pattern explains the obstruction.
- **No monotonicity [Certified].** SW(1, 81, 16) has no solution and SW(1, 82, 16) has one. At w = 78, A = 14 fails, A = 15 and 16 succeed, A = 17 fails.
- **Fragility [Evidence].** SW(1, 77, 16) becomes solvable when the single progression 44, 55, 66, 77 is ignored. At (w, A) = (100, 16), deep inside the dead band, some order has only 5 monotone progressions out of 4,167.
- **Thin windows are fine [Evidence].** For A = 2, 3, 4 the window problem is solvable at every size where the solver finished (w up to 120, and A = 2 also at w = 150). A list could try to avoid ever having a thick clean window, by cutting each residue class at a different place. SAT solvers cannot test such "ragged" layouts at the sizes that matter, and we found no rule that produces thin-window solutions at all sizes: every rule with a uniform description broke somewhere between w = 60 and w = 288.
- **A toy theorem with a real proof.** **Theorem T0 [Hand; one AI skeptic did not refute it].** For w ≥ 15 and A ≥ 2, no order of [1, w) *without monotone 3-term progressions* solves SW(1, w, A); the threshold 15 is exact. The proof is five lines from the Gap Lemma: the Case-A relations 2x ≺ x invert an early element and a late one, which rigidity allows at most once, and [w/3, w/2) contains two candidates (a few small sizes are handled directly). Its main lemma is Sharma's published theorem, so only the application is ours. It does not extend to orders that contain monotone 3-term progressions, which is what solutions actually are.

### 4.5 Other routes that are closed

Each of these was tried as a construction and ended in a proof or a computation that it cannot work. Status in brackets.

- Splicing Ho's list of ℕ with its mirror image, under any merge schedule: a monotone progression −u, y, 2y + u, 3y + 2u is always forced **[Hand, not refereed]**.
- Key orders that are homogeneous (scale-invariant) can never avoid all 4-term progressions **[Hand, not refereed]**.
- Thompson's prefix certificates (arXiv:2609.13350): no list of ℤ has all long prefixes certified **[Hand, not refereed]**.
- Magnitude blocks that list residue classes one class at a time, for any modulus; this covers Adenwalla's layout **[Hand + Certified]**.
- Merging two one-sided lists from a family built by Ho-type recursions ("P1 halves"): all 64 pairs of variants fail one stage further **[Evidence; the family itself is unrefereed]**.

---

## 5. Problem #197: which splittings fail

Recall that a set is *permutable* if it has a list with no monotone 3-term progression, and the question is whether ℕ is the union of two disjoint permutable sets. By the orbit lemma, each set must break all of its own doubling chains.

### 5.1 The lists cannot stay close to increasing order

A list has **lag ratio ≤ c** (eventually) if, from some point on, every element m is listed after only elements ≤ c·m.

**Theorem A [Lean].** For c < 2 there is no partition of ℕ into two sets with lists that both avoid monotone 3-term progressions and both have lag ratio ≤ c.

*Idea.* If a is listed before z and 2z − a is in the same class, the anchor rule puts 2z − a before z, and lag ratio below 2 forbids that for large z. So 2z − a must be in the other class; a parity argument then produces a number that fits in neither class.

**Three sets are different [Hand, not refereed].** Colour the block [⌈1.5<sup>k</sup>⌉, ⌈1.5<sup>k+1</sup>⌉) by k mod 3 and list each colour block by block, 2-adically inside blocks. The double of a block lands in blocks of other colours, so no one-colour progression meets two blocks. These lists have lag ratio about 3/2. Theorem A therefore separates two sets from three.

**Theorem B [Certified; the reduction survived three AI referees; not in Lean].** The same holds for lag ratio ≤ 3.

### 5.2 A finite gadget

**Theorem I [Lean].** For every M ≥ 8, no order of the interval [M, 2M + 6] without monotone 3-term progressions satisfies the eight relations "2(M + j) − a comes before M + j" for j = 0, 1, 2, 3 and a = 0, 1.

Those eight relations are exactly what the anchor rule forces when 0 and 1 are listed before the interval. The proof uses the rigidity of §2.3 in 16 cases (M mod 8, times the early parity). The constant 6 cannot be lowered to 5 for M = 8.

**Corollary I [Lean].** If S is permutable and contains two consecutive integers v, v + 1, then S contains only finitely many intervals of the form [P, 2P − v + 6].

So a permutable set with two adjacent elements cannot contain long intervals that reach just past their own double. Kasel's order gadget and its Lean proof by others (trureturing PR #9626) give the same statement with 13 in place of 6.

### 5.3 Long alternating runs

**Theorem R\* (tower obstruction) [Lean].** A set that contains two points u, u + d and an infinite sequence of intervals, each starting well above the previous one and each reaching far enough past twice its own start (explicit inequalities in the repository), is not permutable.

*Idea.* Theorem I, rescaled, says that a block of the gadget's shape above a pair w, w + δ forces some element of the block to be listed before the pair. Five overlapping blocks inside one interval produce a new pair inside that interval, listed before the old pair. Climbing the tower, the position of the pair in the list decreases at every level, which cannot go on forever.

**Corollary R2\* [Lean].** Let 1 ≤ r<sub>0</sub> < r<sub>1</sub> < ⋯ be integers with r<sub>k+1</sub>/r<sub>k</sub> → 2 and colour the run [r<sub>k</sub>, r<sub>k+1</sub>) by the parity of k. Then neither colour class is permutable.

There is no assumption on the lists and none on how fast the ratios converge. Kasel's dyadic partition is the case r<sub>k</sub> = 2<sup>k</sup> + 1. The method needs run ratios of at least 7/4.

### 5.4 An odd number of runs per octave

If each octave [x, 2x) is cut into 2k + 1 runs of alternating colours, doubling a number moves it 2k + 1 runs ahead, into the *other* colour. That breaks doubling chains, so these "ρ-partitions" were among the main candidates for a positive answer after the dyadic partition died.

**Quarter Lemma [Lean; a corollary of Sharma 2009].** In an order of an interval without monotone 3-term progressions, with early parity π and *early quarter* Q (the residue modulo 4, inside the early parity, whose elements x come before x + 2), every q ≡ Q (mod 4) comes before every z of the late parity, provided both are at least 4 away from the ends of the interval.

**Theorem 7.2 [Lean].** For k ≥ 1 and any real phase φ, colour n ≥ 1 by the parity of ⌊(2k + 1)(log<sub>2</sub> n − φ)⌋. Neither colour class is permutable.

*Idea.* The double of the bottom of a run lands zero or one above the bottom of the run 2k + 1 later. So a small window at the bottom of a run is mirrored, through two fixed adjacent anchors, into the run 2k later, which has the same colour. The anchor rule and the Quarter Lemma then put a point of the next window before the current window: an infinite descent again. Colourings whose run boundaries drift away from exact powers are not covered.

### 5.5 Rotation sets and random sets

**Theorem K, one frequency [Lean].** Let α be irrational, β real and 0 ≤ a < b ≤ 1. The set A = {n : frac(nα + β) ∈ (a, b)} is not permutable, and neither is any set containing it.

These are the Sturmian or "rotation" sets: n is in A when the point nα + β on the circle falls in a fixed arc. They are the standard example of a set that is spread out evenly without being periodic.

*Proof.* Write θ(n) = frac(nα + β). Since α is irrational, the values θ(n) are dense, so we can pick two anchors f<sub>1</sub>, f<sub>2</sub> in A with x<sub>1</sub> = θ(f<sub>1</sub>) < x<sub>2</sub> = θ(f<sub>2</sub>), and a start u larger than both with θ(u) between x<sub>1</sub> and x<sub>2</sub>. Doubling acts on the circle by θ(2u − f) = 2θ(u) − θ(f) whenever the right side is in [0, 1). If θ(u) is in the lower half of [x<sub>1</sub>, x<sub>2</sub>], reflect in f<sub>1</sub>: 2θ(u) − x<sub>1</sub> is again in [x<sub>1</sub>, x<sub>2</sub>]. Otherwise reflect in f<sub>2</sub>. Either way the new point 2u − f is larger than u and is in A. This is an infinite doubling chain in A with two anchors, and the orbit lemma finishes. ∎

**Theorem K, general [Hand; survived three AI referees; not in Lean].** The same for several rationally independent frequencies and any open window on the torus. In particular Beatty-type parity colourings fail.

**Theorem RS [Hand; survived three AI referees; not in Lean].** For every 0 < p < 1, a random set that contains each n independently with probability p is almost surely not permutable. The proof finds an interval of anchors and shows that the tree of doubling chains above it dominates a branching process that survives with positive probability; this is then upgraded to probability one. The case p = 1/2 appears as an unproved claim in Kasel's notes.

So both standard models of a "diffuse" set, random and quasi-periodic, are out.

### 5.6 What a positive answer would have to look like

Putting the theorems together, a two-set solution would need all of the following.

- At least one list that runs ahead by a factor of more than 3, infinitely often: infinitely many m are listed after some element larger than 3m (Theorems A, B).
- No class with two adjacent elements and infinitely many intervals [P, 2P − v + 6] (Corollary I), no towers (R\*), not an exact ρ-partition (7.2).
- Not random, not a rotation set (RS, K).
- **[Hand, not refereed]** Across *every* large cut X, some pair y < X ≤ z < 2y of the same class with z listed before y, Also, no schedule that lists ℕ block by block (finishing [1, X) before going on, for infinitely many X) works, whatever the blocks and the orders inside them.

Colourings that survive every tool we have are known: log-periodic colourings with eight arcs per period, and some run patterns with drifting boundaries. What is missing, for a negative answer, is a version of Theorem I that tolerates a few missing points in the interval. Diffuse colourings never contain the complete intervals that all our rigid gadgets need.

---

## 6. What failed, and where the problems stand

**#195.** The construction side has a list that is correct on a set of density one and provably cannot be repaired in the obvious ways. The obstruction side has a certified dead band for clean block layouts and a lag bound of 9/2, with no readable proof and no monotone structure to extrapolate from. The two sides do not meet: a solution could still exist with ragged cuts and thin windows, which nobody can test, and an impossibility proof would need a mechanism that works for lists with unbounded lag, which nobody has. Our last round of work produced eleven further ideas; seven were tested and none survived. We do not have evidence for either answer.

One formulation has not been explored: with 0 listed first, a good list of ℤ is two good one-sided lists (the positives, the negatives) together with a way of merging them, and a rule in our notes **[Hand, not refereed]** says the merge is forced for most pairs p, −q. Building the two halves jointly under that rule was never tried.

**#197.** Every explicit family we could describe fails, and the failures have a common shape: a doubling chain that the colouring does not break. The surviving candidates are exactly those in which chains are broken by log-scale phases and the classes contain no complete near-doubling intervals. We estimate nothing about which answer is right.

**Things that went wrong along the way.**
- Three times an agent "discovered" a lemma that was already published (Sharma's theorem twice, and the corollary of Geneson's §5). The credits above reflect this.
- A claim that four pairs of one-sided lists could be merged was an artefact of a checker that ignored elements not yet placed. With that fixed, all pairs fail.
- Our own certificate checker accepted a fake proof when a file header overstated the number of clauses. No certificate in this paper triggers the flaw, and the newest ones were re-checked with the patched checker.
- Two corollaries of the tower theorem were false in degenerate cases with empty intervals; the AI referees caught this and each received one more hypothesis before formalization.

## 7. Table of results

| Result | Problem | Status | Where |
| --- | --- | --- | --- |
| Thm 1: no monotone 4-AP with odd d | 195 | Lean | [erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference) |
| Thm 2: none with 4 ∤ d | 195 | Lean | [erdos-195-difference-not-div-4](https://github.com/Alex-lop/erdos-195-difference-not-div-4) |
| Thm G: none with 2<sup>t</sup> ∤ d (corollary of Geneson) | 195 | Lean | [erdos-195-valuation-bands](https://github.com/Alex-lop/erdos-195-valuation-bands) |
| Thm H: finitely many for each ν<sub>2</sub>(d) | 195 | Lean | same |
| Cor Z1: density-one set with a 4-AP-free list | 195 | Lean | same |
| Prop Z3, Z3′: the deleted zone cannot be re-inserted | 195 | Lean | same |
| Thm L1: lag ratio < 2 impossible | 195 | Hand, not refereed | working notes |
| Thm L2: lag ratio ≤ 9/2 impossible | 195 | Certified, two encoders | working notes |
| Thm W and the dead band [3.704, 16.55] | 195 | Certified, two encoders; bridge lemmas one AI referee per lens | working notes |
| Layouts dead for a in (1 + √2, 28/9) | 195 | Certified, two encoders | working notes |
| One-sided windows always solvable | 195 | Hand, not refereed | working notes |
| Thm T0 (toy case; corollary of Sharma) | 195 | Hand, one AI skeptic | working notes |
| Thm A: lag ratio < 2 impossible | 197 | Lean | [erdos-197-bounded-lag](https://github.com/Alex-lop/erdos-197-bounded-lag) |
| Thm B: lag ratio ≤ 3 impossible | 197 | Certified; three AI referees | working notes |
| Thm I, Cor I: the gadget [M, 2M + 6] | 197 | Lean | [erdos-197-interval-gadget](https://github.com/Alex-lop/erdos-197-interval-gadget) |
| Thm R\*, Cor R2\*: towers; runs with ratio → 2 | 197 | Lean | [erdos-197-tower-obstruction](https://github.com/Alex-lop/erdos-197-tower-obstruction) |
| Quarter Lemma; Thm 7.2: exact ρ-partitions | 197 | Lean | [erdos-197-rho-partition](https://github.com/Alex-lop/erdos-197-rho-partition) |
| Thm K, one frequency: rotation sets | 197 | Lean | [erdos-197-kronecker](https://github.com/Alex-lop/erdos-197-kronecker) |
| Thm K, several frequencies; Thm RS: random sets | 197 | Hand, three AI referees | working notes |
| Crossing pairs at every cut; no complete prefixes | 197 | Hand, not refereed | working notes |

"Working notes" are files of the project that are not public. Statements that live only there should be treated as claims until someone else checks them.

## 8. How this was produced, and what "verified" means here

The work was done between 1 and 11 November 2026 by Claude models (Opus 5.5, Fable 5.1, Fable 5.2, Sonnet 5.5) running as agents in Claude Code, directed by Alex Lopez. Agents proposed constructions and obstructions; other agents, given no stake in the result and told to refute it, acted as referees with three lenses (the proof, the computation, the scope and novelty); survivors were formalized in Lean by further agents and audited.

- **Lean.** Each repository states its theorems in a file that imports only Mathlib, proves the same statements elsewhere, and checks that both elaborate to identical terms. The proofs use only the three standard axioms and no `native_decide`. The "no monotone progression" predicate is matched against the one in Google DeepMind's formal-conjectures by separate fidelity files. The kernel guarantees the formal statement. That the formal statement says what the prose says was checked by AI audits and by non-vacuity files, not by a human.
- **Certified.** A finite instance was written as a SAT formula by two independently written encoders, refuted by a SAT solver, and the LRAT proof was checked by a separate checker. The step from the finite instance to a statement about all lists is a short hand argument in each case; its review status is given next to each result.
- **AI referees.** They catch real errors (§6), but they are the same kind of model as the authors and can share blind spots. Surviving them is weaker than human review.
- **Novelty.** Claims that something is new mean only that our literature searches found nothing. Several 2026 papers on these problems appeared while the project ran.

## References

- J. A. Davis, R. C. Entringer, R. L. Graham, G. J. Simmons, *On permutations containing no long arithmetic progressions*, Acta Arith. 34 (1977), 81–90.
- A. Sharma, *Enumerating permutations that avoid three term arithmetic progressions*, Electron. J. Combin. 16 (2009), #R63.
- T. D. LeSaulnier, S. Vijay, 2011 (permutations of ℕ and ℤ avoiding monotone progressions; the odd-difference result for ℕ).
- J. Geneson, Discrete Math. 342 (2019), 1489–1491, arXiv:1803.06334.
- S. Adenwalla, arXiv:2211.04451 (2022).
- J. Geneson, arXiv:2608.12604 (2026): block constructions, densities of 4-permutable subsets of ℤ.
- W. Kasel, *Structural rigidity in the Erdős–Graham two-set permutation problem*, arXiv:2609.02939 (2026).
- B. S. Ho, arXiv:2609.12780 (2026): a list of ℕ with no monotone 4-term progression.
- Thompson, arXiv:2609.13350 (2026): binary orders and prefix certificates.
- the-omega-institute/trureturing, pull request #9626: Lean proof that Kasel's order gadget is infeasible for M ≥ 16.
- google-deepmind/formal-conjectures: the formal statements of Erdős #195 and #197.
