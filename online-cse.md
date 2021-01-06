# Optimizing Decision Trees with Online Common Subexpression Elimination

## Abstract

## Introduction

Consider the straightforward compilation of a boxes-of-boxes-of-integers
pattern-matching idiom into a decision tree, in figure 1.

Figure 1:
```
match x
  Box (Box 1): f_1()
  Box (Box 2): f_2()
  ...
  Box (Box n): f_n()
```
    
We might expect a simple compiler front-end to residualize a program
like the one in figure 2: a chain of if/then/else-if statements where
each test is a similar logical conjunction.

Figure 2:
```
if      Box? x and Box? (y_1:=Unbox x) and Equal? (Unbox y_1) 1: f_1()
else if Box? x and Box? (y_2:=Unbox x) and Equal? (Unbox y_2) 2: f_2()
...
else if Box? x and Box? (y_n:=Unbox x) and Equal? (Unbox y_n) n: f_n()
```

We would then hope that this optimizer transforms the program of figure
2 into something like figure 3, hoisting the repeated comparisons to the
top of the program.

Figure 3:
```
if Box? x and Box? (y := Unbox x):
  z := Unbox y
  if      Equal? z 1: f_1()
  else if Equal? z 2: f_2()
  ...
  else if Equal? z n: f_n()
```

Finally, we would expect the inner chain of `if` statements to reduce to
the table switch of figure 4.

Figure 4:
```
if Box? x and Box? (y := Unbox x):
  z := Unbox y
  switch z:
    1: f_1()
    2: f_2()
    ...
    n: f_n()
```

However, that's not what happens.  Neither GCC nor LLVM convert the
program of figure 2 to the equivalent program of figure 3.  Why not?
What algorithm is missing?  This paper analyses the decision tree
reduction problem.  Guided by an instinct that the solution is related
to common subexpression elimination (CSE), we first express the CSE
algorithm in terms of a novel "CPS soup" program representation.  Using
this representation, we show why standard code motion techniques fail to
apply.  We then proceed to define an "online common subexpression
elimination" algorithm as an effective single-pass solution.

## Key Contributions

;; FIXME: Not sure how bold to be regarding tone here.  Normally I would
;; be more circumspect but I understand that reviewers appreciate clues
;; about what authors think their paper is about.

A new intermediate language for optimizing compilers, "CPS soup",
presenting distinct advantages in terms of minimalism and expressiveness
with regards to ANF, traditional CPS, or SSA intermediate languages;

An expression of common subexpression elimination in terms of CPS
soup;

An analysis of the "decision tree reduction problem", in which existing
algorithms fail to optimize direct expansions of pattern-matching
idioms, illuminated by the expression of CSE in CPS soup;

"Online CSE", an extension of CSE that is able to solve the decision
tree reduction problem in a single pass, by folding branches at their
predecessors, and by locally recomputing flow analysis as CSE folds
branches.

## Language: CPS soup

We begin by defining a novel first-order continuation-passing-style
program representation to use in solving the problem, "CPS soup", in
figure 5.

;; FIXME: this is sloppy!

Figure 5:
```
type List<value>
type Set<value>
type Map<key, value>

i, j : Integer
k, l : Label
f, g : FunctionLabel
u, v, w, x, y, z : Var
args, vars : List<Var>

e : Expr
t : Test

Expr ::= Box x | Unbox x | Vals vars | Call f args | i
Test ::= Box? x | Equal? e_1 e_2
Term ::= Continue k e | Branch k_f k_t t
Cont ::= Cont args term
Prog ::= Prog k_init k_tail conts:Map<Label,Cont>
```

CPS soup is inspired by Andrew Kennedy's "Compiling with Continuations,
Continued", but with flow-based variable availability instead of nested
scope trees.

This distinct CPS soup characteristic bears directly on our results, so
it merits explanation.  Consider that in the traditional nested-scope
CPS program in figure 6, all paths from L to K pass through M.  Cont K
could re-use the value bound to *a* in M, except it's not in scope.  It
would be, though, if the scope tree were instead written as in figure 7.
As Stephen Weeks observed in 2003, [a dominator tree is always a valid
scope tree, but not all scope trees are dominator
trees](http://mlton.org/pipermail/mlton/2003-January/023054.html).
Weeks observed that many transformations in intermediate languages with
nested scope need to include extra steps to make the scope tree reflect
the dominator tree.

Figure 6:
```
letcont K b = Q(42) in
  letcont L = letcont M a = K(a) in
                  M(42) in
    L()
```


Figure 7:
```
letcont L = letcont M a = K(a) in
              letcont K b = Q(a) in
                M(42) in
  L()
```

CPS soup avoids this problem by avoiding nested scope.  Because flow
determines variable availability, it is perfectly valid to transform the
equivalent example program expressed in CPS soup, in figure 8, to the
simplified program in figure 9.  

Figure 8:
```
Prog L Q
  {L→Cont [] Continue M 42;
   M→Cont [a] Continue K (Vals [a]);
   K→Cont [b] Continue Q 42}
```

Figure 9:
```
Prog L Q
  {L→Cont [] Continue M 42;
   M→Cont [a] Continue K (Vals [a]);
   K→Cont [b] Continue Q a}
```

Unlike nested-scope formulations of CPS intermediate languages, it is
always sound to eliminating common subexpressions by replacing
expressions with variable references in CPS soup, without needing to
perform non-local tree rewrites to ensure the scope tree reflects the
dominator tree.

We say that a CPS soup program is *well-formed* if the following
conditions hold:

All labels distinct:
  Ensured by map key uniqueness.

All bound variables distinct:
  All [v...] in all (Cont [v...] term) distinct.

Definitions dominate uses:
  For all uses of variable x in label k, all paths from k_init to k
  contain a Cont [... x ...] term.

Arities match:
  For all k, args in {k→Cont args term}, all direct predecessors l of k
  have arity |args|.

Entry and exit:
  k_init in prog's conts; k_tail not in prog's conts.

To avoid clutter, CPS soup is presented in an untyped form.  In the
expression Unbox x, if x is not a box, the program aborts.

It would not be inaccurate to see CPS soup as being the same as static
single-assignment (SSA) form, but where every block contains only a
single expression, and where every variable is a "phi" (having
potentially many definitions).  We discuss the tradeoffs with the more
well-known SSA formulation in section XXX, after having presented an
algorithm in terms of CPS soup.

An implementation of CPS soup is used in practice in the Guile
implementation of Scheme since version 2.2 (2015)
(https://wingolog.org/archives/2015/07/27/cps-soup,
https://www.gnu.org/software/guile/manual/html_node/CPS-Soup.html).  As
an implementation note, Guile represents labels and variables as small
integers, and programs as functional maps from integers to `Cont`.  The
functional map allows optimizations to be expressed naturally as pure
functions from one program to another.

## Classic CSE

Going back to the original decision tree of figure 2, there are a number
of redundant `Unbox` expressions: although `Unbox y_1` and `Unbox y_2`
operate on apparently different variables, in actuality they are the
same.  Eliminating redundant variable definitions sounds like what
common subexpression elimination does.  Let us begin therefore by
expressing the classic common subexpression elimination (CSE) algorithm
in terms of CPS soup.  Our pseudocode will use the notational
conventions of figure 10.

Figure 10: Notational conventions
```
[a,b,c] : List
{a;b;c} : Set
{a→b;c→d} : Map
|list|           // Length of list, set, or map
map[a]           // Return b where a→b in map.  Error if a not in map.
∪(sets), ∪(maps) // Union of list of sets or maps.
∩(sets), ∩(maps) // Intersection of list of sets or maps.
a ∪ b, a ∩ b     // Same as ∪([a,b]) or ∩([a, b]).
a + b            // Same as a ∪ b, but asserting operands are disjoint.
a - b            // The map or set A, but without any element from set B.
map1 / map2      // {for k→v in map1: k→(if k in map2 then map2[k] else v)}
e[[s]], t[[s]]   // For x→y in s, substitute uses of x with y in expr e or test t
```

Figure 11: CSE in terms of CPS soup
```
// For each label L, the set of conts that continue to L.
preds : Map<Label, Set<Label>>

// For each label L, the set of conts whose values are available at L.
avail : Map<Label, Set<Label>>

// For each expr E, the conts that define E, and the variables to which
// the results are bound.
equiv : Map<Expr, Map<Label, List<Var>>>

// For each redundant variable X, the dominating variable Y which should
// be used instead.
subst : Map<Var, Var>

Analysis ::= Analysis preds avail equiv subst

cse (Prog k_init k_tail conts):
  let analysis = analyze(k_init, conts)
  let out = {} : Map<Label,Cont>
  for l, Cont args term in reverse_post_order(k_init, conts):
    out, analysis ← propagate(l, args, term, out, analysis)
  return out
  
analyze conts k_init:
  let preds = {for k→_ in conts:
                k→{for l→cont in conts if cont continues to k: l}}
  // Assume pure language for the moment; no side effect modelling needed.
  let kill = {for k→_ in conts: k→{}}
  compute_avail avail:
    {for l→_ in preds if l in avail:
      l→∩([for pred in preds[l] if pred in avail:
             avail[pred] - kill[pred] + {pred}])}
  let avail = fixpoint(compute_avail, {k_init→{}})
  Analysis(preds, avail, {}, {})

propagate l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      case preds[l] of
        {pred}:
          // For conts with a single predecessor, potentially augment
          // the subst or equiv maps before visiting term.
          case out[pred] of
            Cont _ Continue _ Values vars:
              let subst = subst + {for var,arg in vars,args: var→arg}
              visit(l, args, term, out, Analysis(preds, avail, equiv, subst))
            Cont _ Continue _ exp:
              let equiv = equiv ∪ {exp→(equiv[exp] ∪ {l→args})}
              visit(l, args, term, out, Analysis(preds, avail, equiv, subst))
            _:
              visit(l, args, term, out, analysis)
        _:
          visit(l, args, term, out, analysis)

visit l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst:
      // Rename variable uses as appropriate
      term ← rename(term, subst)
      // If the expression is redundant, eliminate it.
      term ← case rename(term, subst) of
               Continue k exp:
                 case equiv[exp] ∩ avail[l] of
                   {}: Continue(k, exp0)
                   {_→vars; ...}: Continue(k, Values(vars))
               term: term
      let cont = Cont(args, term)
      return (out + {l→cont}), analysis

rename term subst:
  case term of
    Continue k e: Continue(k, e[[subst]])
    Branch k_f k_t t: Branch(k_f, k_t, t[[subst]])
```

In short, the algorithm does an up-front analysis pass to determine
which values are available at every program point.  It then uses this
analysis in a once-through forward pass over the conts of a program.
Visiting in reverse-post-order is a topological sort that will visit
definitions before uses.  As we go, we keep a map of names for values
that we've seen; if we see a new expression that's redundant to an old
one, we replace the expression with a reference to the old values.

Note that when using a conventional SSA or ANF notation, names are bound
to values in one place; you would have `y_1 = Unbox x` or `let y_1 =
Unbox x in ...`, whereas in CPS soup the expression and the name are
usually in different conts, as in `l→Cont _ Continue k Unbox x; k→Cont
[y_1] _`.  CPS soup effectively denotes every variable as potentially a
"phi" variable, with multiple defining expressions; if you want to reach
through to find the unique value of a variable, you need to know that
the label binding the variable has one and only one predecessor, as we
do above.  Generally speaking this difference is immaterial, but later
we will find that CPS soup's notation makes a solution easier.

The complexity of `visit` is O(|conts|), assuming that equiv[exp] ∩
avail[l] is O(1).  `analyze` could have a complexity of O(|conts|^2): it
associates a bit for each variable at each label.  However in practice
this is less than quadratic.  Consider a program without loops: we
compute the fixpoint in a single pass, iterating forward from k_init.
Assume that kill[pred] is {}.  Therefore we have two cases: join points,
where we need to intersect different predecessors, and non-join points.
In the latter case at each label we are only adjoining {pred} to the
avail set; if we use a persistent set this is O(log |conts|) only.  With
multiple predecessors, a persistent intmap can make intersection share
space also.  Therefore we can conclude that in for programs without
loops, the complexity of `analyze` is O(|conts| log |conts|), in space
and in time.

For a program with loops, we note that `analyze` is a effectively a
bitvector flow-analysis pass.  If the graph is reducible, each node will
be visited a maximum of two times plus the graph's loop connectedness
(Hecht and Ullman Knuth 1973), a number almost always bounded by 3 in
practice (Knuth 1974).  While we make no special attempt to preserve
reducibility as we don't need its properties otherwise, most graphs are
reducible, and it seems that practical bounds are enough to consider
this algorithm as O(n log n) for the purposes of deciding whether to
include it in a production compiler.

FIXME: show experimental results, as some of the arguments are based on
"in-practice" heuristics.

## Revisiting the decision tree reduction problem

Let us now express the first two cases of the original decision tree in
figure 1 in terms of CPS soup, and then apply CSE to that program.

Figure 12: Example program, lowered to CPS soup
```
Prog A1 Z
  {A1→Cont [x] Branch A2 B1 Box? x;
   B1→Cont [] Continue C1 Unbox x;
   C1→Cont [y1] Branch A2 D1 Box? y1;
   D1→Cont [] Continue E1 Unbox y1;
   E1→Cont [z1] Branch A2 F1 Equal? z1 1;
   F1→Cont [] Continue Z Call f1;

   A2→Cont [] Branch A3 B2 Box? x;
   B2→Cont [] Continue C2 Unbox x;
   C2→Cont [y2] Branch A3 D2 Box? y2;
   D2→Cont [] Continue E2 Unbox y2;
   E2→Cont [z2] Branch A3 F2 Equal? z2 2;
   F2→Cont [z2] Continue Z Call f2;

   ...}
```

If we apply the CSE algorithm to the original program of figure 1, we
get nothing: no expression is found to be redundant and replaced with a
variable.  The expression of the program in terms of CPS soup in figure
12 allows us to see why this is the case: the branch at A2 is preceded
by A1, C1, and E1; the set of available definitions at A2 is the
intersection of those definitions available at its predecessors; and at
A2, no definitions are available.  (The declaration of `x` is available,
but its definition is not.)  Therefore we can't see at B2 that the
`Unbox x` could be equivalent to anything, because nothing is available.

### Adding branch-folding

The first step towards reducing the graph is to "skip" label A2.  It is
dominated by an equivalent term at A1, but its effect is to branch
instead of defining a value, so we need to extend the CSE algorithm to
fold branches.

From a mechanical perspective, we extend the flow analysis to add
branches to the equiv set, and to keep a record of which branches have
been true or false at any given program point, by adding a `bool` entry
to `Analysis`:

Figure 13: Adding taken-branch analysis
```
BB : 00  ; Neither branch taken
   | 01  ; False branch taken
   | 10  ; True branch taken
   | 11  ; True and false braches taken
bool : Map<Label, Map<Label, BB>>
Analysis ::= Analysis preds avail equiv subst bool
```

We compute `bool` as a bitvector flow analysis:

Figure 14: Computing taken-branch analysis
```
branch_taken conts pred l:
  case conts[pred] of
    Cont _ Branch =l =l t: 11
    Cont _ Branch =l _  t: 01
    Cont _ Branch _  =l t: 10
    _:                     00

compute_taken_branches conts preds:
  let init = {for l→_ in conts:
               l→∪([for p in preds[l]: {p→branch_taken(conts, pred, l)}])}
  saturate bool:
    {for l→v in bool: l→(v ∪ ∪([for p in preds[l]: bool[p]]))}
  return fixpoint(saturate, init)
```

This bitvector flow analysis does not worsen the complexity of
`analyze`.

We extend `visit`, adding a case for branches:

Figure 15: Extension to `visit`, adding branch folding
```
// Return (taken, not-taken), or () if can't fold.
fold_branch l kf kt test equiv avail bool:
  for pred→vals in (equiv[test] ∩ avail[l]):
    case bool[l][pred] of:
      01: return (kf, kt)
      10: return (kt, kf)
      _: _ // Keep looking.
  return ()

visit l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      term ← rename(term, subst)
      term ← case term of
               Branch kf kt test:
                 case fold_branch(l, kf, kt, test, equiv,
                                  avail[l], bool[l]) of
                   (): term
                   (taken, not_taken): Continue(taken, Values([]))
               ...
      ...
```

However, re-running the newly extended CSE doesn't help in this case:
bool[A2][A1] is 11, as it can be reached either by the false branch (A1)
or by the true branch (C1 and E1).

### We need context sensitivity and online reflow

At this point we are starting to see the shape of the solution.  The
branch at A2 can't fold at label A2, but it can fold at each of its
predecessors.  Consider the original terms A1, C1, and E1 from figure
16.  The predecessor of A2 at A1 can continue directly to A2's false
branch target, and the predecessors at C1 and E1 can continue to A2's
true target, resulting in the new terms of figure 17.  A2 is left
unreachable and can be pruned.

Figure 16: Original predecessors of A2
```
  A1→Cont [x] Branch A2 B1 Box? x;
  C1→Cont [y1] Branch A2 D1 Box? y1;
  E1→Cont [z1] Branch A2 F1 Equal? z1 1;
```

Figure 17: Predecessors of A2, after context-sensitive branch-folding
```
  A1→Cont [x] Branch A3 B1 Box? x;
  C1→Cont [y1] Branch B2 D1 Box? y1;
  E1→Cont [z1] Branch B2 F1 Equal? z1 1;
```

We call this desired transformation *context-sensitive* branch folding.
The predecessor of a branching continuation can be thought to call the
continuation, and in that way is a context in the sense of the k-CFA
family of context-sensitive flow analyses.

Before moving on to implement this algorithm, let us look ahead to the
term at B2.  We would like to see the `Unbox x` at B2 as equivalent to
the one at B1.  In the classic CSE algorithm above, this is not
possible, as B1 is not available at B2 -- the "offline" pre-computed
flow analysis does not record B1 as dominating B2.  However, after
context-sensitive branch folding, we can see that B1 is indeed available
at B2.  Therefore our new algorithm needs to perform "online"
recomputation of the flow analysis as it goes, both to enable branch
folding and to detect redundant expressions, to see that the later
`Unbox y2` at D2 is actually `Unbox y1`, and is thus equivalent to `z1`.

## Online CSE

We propose an "online" common subexpression elemination algorithm as a
solution to the decision tree reduction problem.  Relative to classic
global CSE, online CSE has three extensions:

 1. Context-sensitive branch folding.  We use taken-branch flow analysis
    to fold branches *and their prececessors*.  (It would be sufficient
    to just fold predecessors, but sometimes predecessors can't fold
    without violating well-formedness.)

 2. Online flow analysis recalculation.  Branch folding can alter
    avail/bool sets, and it can also cause continuations to go from
    multiple to single predecessors, making more definitions available
    for elimination.  Therefore we update the predecessors map as the
    once-through forward pass proceeds to recalculate flow analysis
    locally at each node.  This recalculation can only increase the
    precision of flow analysis.  Note also that as we add equivalent
    expressions when visiting continuations, not the predecessor, such
    additions can happen after control-flow graph reductions.

 3. Eager elision.  Instead of leaving "useless" conts in the flow graph
    for dead-code elimination to clean up later, online CSE elides these
    terms eagerly.  A useless cont is a `Values` expr that is the sole
    predecessor of its continuation.  The eager elision transformation
    modifies the successor to be the new continuation of all the
    predecessor's predecessors, moving the predecessor's definitions
    there.  This administrative reduction makes it easier to fold
    branches while preserving well-formedness.

These extensions enable each other: context-sensitive branch folding can
uncover common subexpressions, but needs an updated flow analysis to
eliminate them.  Similarly, branch folding can only be exhaustive if
updated flow analysis uncovers redundant branches by renaming branch
operands to their canonical definitions.  The administrative eager
elisions make foldable branches more easily detectable, which may of
course lead to more elidable definitions.

To implement eager elision, in figure 18 we add a case to `propagate` to
remove `Values` expr that is the sole predecessor of its continuation.
We do so from the successor, so that folding can expose more of this
kind of definition.

Figure 18: Eager elision
```
propagate l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      case preds[l] of
        {pred}:
          case out[pred] of
            Cont args' Continue _ Values vars:
              subst ← subst + {for var,arg in vars,args: var→arg}
              analysis ← Analysis(preds, avail, equiv, subst, bool)
              case elide_predecessor(label, pred, out, analysis) of
                (): visit(l, args, term, out, analysis)
                (out, analysis): visit(l, args', term, out, analysis)
            ...
        ...

prune_edge preds pred succ:
  return preds / {succ→(preds[succ] - {pred})}
add_edge preds pred succ
  return preds / {succ→(preds[succ] ∪ {pred})}
forward_edge preds pred old new
  return add_edge(prune_edge(preds, pred, old), pred, new)

elide_predecessor label pred out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      out ← out - {pred}
      for pred_pred of preds[pred]:
        ; Don't elide predecessors that are targets of back-edges.
        if pred_pred not in out:
          return ()
        out ← out / {pred_pred→forward(out[pred_pred], pred, label)}
        preds ← forward_edge(preds, pred_pred, pred, label)
      preds ← prune_edge(preds, pred, label)
      return (out, Analysis(preds, avail, equiv, subst, bool))

forward cont old new;
  fwd k:
    return new if k == old else k
  case cont of
    Cont args Branch kf kt t:
      return Cont(args, Branch(fwd(kf), fwd(kt), t))
    Cont args Continue k e:
      return Cont(args, Continue(fwd(k), e))
```

This transformation removes the bindings for `args` in the successor,
which is sound as the args are substituted.  In that case the reified
cont will declare the predecessor's `args` formals instead.

We implement online flow analysis recalculation in figure 19.  At each
`visit` we will recompute the flow analysis from the immediate
predecessors of the cont being visited.  This refines the analysis
precisely in the forward direction, while continuing to treat back-edges
conservatively.

Figure 19: Online flow analysis recalculation
```
visit l args term out analysis:
  case recompute(analysis, l, out) of
    Analysis preds avail equiv subst bool:
      ...

recompute analysis l out:
  case analysis of
    Analysis preds avail equiv subst bool:
      meet_again labels avail_in bool_in:
        case labels of
          {}: return (avail_in, bool_in)
          {pred} + labels:
            let avail_in', bool_in' = compute_out_edges(avail, pred, l, out)
            return meet_again(labels,
                              avail_in' ∩ avail_in,
                              bool_in' ∪ bool_in')
      let avail_in, bool_in = meet_again(preds[l], [], {}, [])
      let avail = avail / {l→avail_in}
      let bool = bool / {l→bool_in}
      return Analysis(preds, avail, equiv, subst, bool)

compute_out_edges avail pred succ out:
  case analysis of
    Analysis preds avail equiv subst bool:
      let avail_out = avail[pred] + {pred}
      let bool_out = bool[pred] + branch_taken(out, pred, succ)
      return avail_out, bool_out
```

We use the freshly refined flow analysis to perform substitution as
usual.  It may be that the renamed term itself is redundant; in that
case its continuation may replace with a `Continue(k, Values)` term,
which may itself be elided when visiting successors, causing
control-flow graph simplifications as the once-through pass moves
forward in reverse-post-order.

However, there is another interesting possibility, which is that branch
terms may not fold where they are, but can fold at one or more
predecessors: context-sensitive branch folding.  Therefore if the result
of renaming is a branch, in figure 20 we check the `equiv` and `bool`
maps for all immediate predecessors to see if any simplification is
possible.  Such a simplification could cause the branch to become dead
or even to allow the branch to fold in place: a situation that can be
detected by re-running the online flow analysis pass.  Therefore if any
branch predecessor is able to fold, we revisit the term from the top.

Context-sensitive branch folding actually happens before redundant
expressions are eliminated.  In this way, any predecessor of a branch
that can fold continues directly a the new successor, without bouncing
through the cont being visited.  This allows the cont being visited to
become dead if it has no more predecessors, and also better enables
further context-sensitive folding at successors.

Figure 20: Context-sensitive branch folding
```
visit l args term out analysis:
  case recompute(analysis, l, out) of
    Analysis preds avail equiv subst bool:
      term ← rename(term, subst)
      case fold_predecessor_branches(l, args, term, out, analysis) of
        (out, analysis):
          // Context-sensitive branch folding occurred, so predecessors
          // have changed; revisit this cont with a newly refined flow
          // analysis.
          return propagate(l, args, term, out, analysis)
        (): ()
      term ← case term of ...
      ...

fold_predecessor_branches l args term out analysis:
  // We can fold predecessors of Cont [] Branch.  If the term isn't a
  // branch, no folding.  More subtly, as folding predecessors will
  // retarget them to conts that bind no variables, we can only do that
  // if the current cont has compatible arity.
  case (args, term) of
    ([], Branch kf kt test):
      case analysis of
        Analysis preds avail equiv subst bool:
          let changed = False
          for pred in preds[l]:
            if pred <= l: continue
            let avail_out, bool_out = compute_out_edges(avail, pred, l, out)
            case fold_branch(l, kf, kt, test, equiv, avail_out, bool_out) of
              (): continue
              (taken, not_taken): 
                changed ← True
                out ← out / {pred→forward(out[pred], l, taken)}
                preds ← forward_edge(preds, pred, l, taken)
          case changed of
            True: return out, Analysis(preds, avail, equiv, subst, bool)
            False: return ()
    _:
      return ()
```

Finally, we need to revisit the simple branch folding that we added
earlier in figure 15.  In most cases, context-sensitive branch folding
subsumes our earlier branch folding; the branch will be left
unreachable.  In that case it should be pruned from the graph, so as to
make flow analysis refinement for successors more precise; figure 21 has
this extension.  However in the case that only some predecessors can
fold, or in the case where no predecessor can fold due to a non-empty
bound variable set in the branch's cont, our earlier form of branch
folding may still be possible.  In that case, we should take care to
update the predecessors map.  Figure 21 implements these simple CFG
cleanups.

Figure 21: CFG cleanup: dead cont removal
```
propagate l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      case preds[l] of
        // A term with no predecessors was made unreachable by branch
        // folding.  Prune it from the CFG.
        {}: return out, prune_successors(analysis, l, term)
        ...

successors term:
  case term of
    Continue k _: return {k}
    Branch kf kt _: return {kf;kt}

prune_successors analysis label term:
  case analysis of
    Analysis preds avail equiv subst bool:
      for succ of successors(term):
        preds ← prune_edge(preds, label, succ)
      return Analysis(preds, avail, equiv, subst, bool)
```

Figure 22: CFG cleanup: dead branch removal
```
visit l args term out analysis:
  case analysis of
    Analysis preds avail equiv subst bool:
      term ← rename(term, subst)
      case term of
        Branch kf kt test:
          case fold_branch(l, kf, kt, test, equiv,
                           avail[l], bool[l]) of
            (): ()
            (taken, not_taken):
              term ← Continue(taken, Values([]))
              preds ← prune_edge(preds, label, not_taken)
              analysis ← Analysis(preds, avail, equiv, subst, bool)
        ...
      ...
```

Though online CSE may seem a bit verbose to implement, GNU Guile's
production implementation of this algorithm is only around 800 lines of
code including comments and whitespace, operating on a richer
intermediate language.  It also includes a number of other facilities
(sparse constant propagation, impure instructions, synthetic auxiliary
definitions).

## Benchmarks

number of code bytes before and after for guile

gabriel benchmark code size changes?

no speed change for gabriel benchmarks

guile compiling-itself benchmark

another matcher: llvm global isel

## Related work

Luc Maragnet: Compiling Pattern Matching to Good Decision Trees

  https://dl.acm.org/doi/abs/10.1145/1411304.1411311

  Similar high-level goal, but operating on high-level patterns instead
  of naive decision trees.  Strictly better than OCSE, given same source
  language, but OCSE approach can include arbitrary procedural match
  predicates, doesn't require special language support for patterns, and
  can operate on lower-level test decompositions (e.g. (foo? x) -> (and
  (heap-object? x) (struct? x) (eq? (struct-vtable x) foo))).

Global Value Numbering

  Modern formulation of CSE; is essentially what Guile did before adding
  online extensions.  OCSE could be named OGVN.

Global Code Motion

  A sea-of-nodes approach to code motion that first lifts all
  expressions as close to the start-of-program as they can go before
  sinking them to their uses, taking into account control dependencies
  as well as data dependencies.  I think but haven't proven that it
  can't optimize the macro-match problem because it doesn't enable
  context-aware branch folding and doesn't prune control dependencies in
  an online way.

Compiling without Continuations

  An argument that translations that can work on CPS can work just as
  well on a direct-style IR, when extended with join points.  However
  there is no obvious solution to the scope-versus-flow problem
  described by Fluet and Weeks; for many problems, what you want is flow
  analysis, and when that is the case, scope is always in the way.  As
  you fold any branch, you end up needing to rebuild the scope tree to
  reflect the dominator tree, to enable further reductions, and
  sometimes you might need to transform simply in order to make new join
  points be in scope.  Folds can be nonlocal transformations, and in
  OCSE we found they were best done from continuations rather than their
  predecessors, which is a tricky algorithm when rebuilding scope trees.
  Tend to think a direct-style solution would mean iterating to a fixed
  point, with O(n) iterations for N reductions.

  [I tried approaches like this and failed, so a lot of this is personal
  agony.]

  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/join-points-pldi17.pdf

Rapid Case Dispatch in Scheme

  A useful discussion of how to transform chains of comparisons to
  constants into binary searches and table dispatches.  Relative to the
  transformation outlined in this paper, Online CSE is able to avoid a
  layer of indirection because it is specified in terms of a CPS-based
  intermediate language, allowing branch targets to be referred to by
  label.

  http://scheme2006.cs.uchicago.edu/07-clinger.pdf

ref: Donald Knuth. An empirical study of FORTRAN programs.
Software Practice and Experience, 1(12):105–134, 1974.

ref: Matthew S. Hecht and Jeffrey D. Ullman. Analysis of a simple
algorithm for global flow problems.  In Conference Record of the First
Annual ACM Symposium on Principles of Programming Languages, Boston
(Mass.), pages 207–217, October 1973.
