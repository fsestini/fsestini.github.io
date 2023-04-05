---
title: Mu-Kanren in Haskell
---

In this post I want to go through a simple Haskell implementation of
MuKanren. MuKanren is a minimal logic programming DSL, belonging to the Kanren
family. In very few words, relational/logic programming is a paradigm embodying
a highly declarative approach to problem solving. Consider the following
definition of an append function, expressed in the DSL that we will build
shortly:

```
append :: Term -> Term -> Term -> Goal
append l s o =
  disj (conjs [nil === l, s === o])
       (fresh 3 $ \[a,d,r] ->
	 conjs [TPair a d === l, TPair a r === o, appendo d s r])
```

The precise meaning of this definition will be clear soon. For now, it is
sufficient to think of it as a ternary relation between list-like terms. As the
name suggests, this relation holds whenever its third argument is the result of
appending the first and the second.

Given such a definition, the first thing we might want to do is to compute the
result of appending two lists `l1` and `l2`. In relational terms, this amounts
to *querying* the system for all output terms `l3` for which the relation
`append l1 l2 l3` holds.

```
λ> run 1 (callFreshV (\v -> append (nums [1,2,3]) (nums [4,5,6]) v))
(1 2 3 4 5 6)
```

Notice how we produce the output in s-expressions, to easily compare our results
with the original Scheme implementation. As we'll see, the `callFreshV` function
introduces a new *logic variable*, that is used as argument for `append` to bind
its result. The argument of `run` is a _goal_, which the function attempts to
solve, returning one of the possible successful instantiations of the variable
logic variable. Since the `append` relation is functional (i.e., it has the same
output for every pair of inputs), the output we get is the only possible one.

So far, there's not much difference from your usual functional programming
language. A more interesting example could be to query what is the list that
needs to be appended to a given one to obtain another one as a result.

```
λ> run 1 (callFreshV $ \v -> append (nums [1,2,3]) v (nums [1,2,3,4,5]))
(4 5)
```

We start to get a sense of how logic programming allows us to run programs
`backwards', starting from the outputs and synthesizing the desired inputs. But
it gets more interesting: we could try to ask MuKanren to output all possible
combinations of lists that, when appended, produce a specific output that we
provide.

```
λ> f x y z = conjs [appendo y z (nums [1,2,3]), x === list [y, z]]
λ> runAll (fresh 3 (\[x,y,z] -> f x y z))
(() (1 2 3))
((1) (2 3))
((1 2) (3))
((1 2 3) ())
```

The logic program above creates three variables `x`,`y`,`z`, and succeeds
whenever `[1,2,3]` is the result of appending `y` and `z`. The first argument
`x` is used to "store" the two results in a list, for printing convenience. Like
before, the results are instantiations of the first logic variable created in
the goal. But now, as the name `runAll` suggests, we get _all_ the possible
results.

With some motivating examples out of the way, we are ready to dig into the
implementation. The [original
implementation](http://www.webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)
of MuKanren is just a few lines of Scheme, which is a demonstration of how concise
functional programs can be. Remarkably, the equivalent Haskell implementation,
shown below, is of about the same length, including type signatures and datatype
declarations!

## The language

To ease the comparison with the paper, I will try to keep my implementation as
close as possible to the original. The central concepts of a MuKanren program
are _goals_, _states_ and, of course, _terms_. We'll se later how terms are
implemented, but for now we can assume to have a type `Term` of MuKanren terms.

_States_ are basically pairs of a substitution (i.e., a map associating
variables to terms) and a non-negative integer counter used to generate fresh
variable names (represented as natural numbers as well).

```
type Var = Nat
type Sub = [(Var, Term)]
type State = (Sub, Nat)
```

_Goals_ can be seen as _proof-relevant predicates_ on states: a goal is a
function that, when applied to a state assigning values to its free logic
variables, returns a sequence of result states in which the goal is satisfied. A
non-empty list of states is a _proof_ that the predicate is satisfiable,
represented as the actual states that satisfy it.

`
type Goal = State -> [State]
`

A MuKanren program will be represented by a goal, so _running_ a program really
just means applying it to an initial (usually empty) state. The result of a
program execution will be the stream of states resulting from the application.

Goals are constructed and assembled by means of a few basic operations, the most
important of which is _unification_.

`
(===) :: Term -> Term -> Goal
`

The expression `t === s` represents a goal that succeeds if and only if the two
terms `t` and `s` unify (in the given state). Unification goals are those
actually responsible for growing the states, as some variables involved in the
two terms may get instantiated in the process. So for example, trying to unify a
variable `x` with a value `5` in the empty state will produce a stream of just a
single new state: the one that maps `x` to the value `5`. The implementation of
unification is addressed in a later section.

The `callFresh` operation just calls an input goal with a new, fresh unification
variable.

```
callFresh :: (Var -> Goal) -> Goal
callFresh f sc = f c (fst sc , c + 1) where c = snd sc
```

`callFresh` takes as input a continuation that accepts a new variable and
returns a goal, and calls it with a variable freshly generated according to the
variable counter in the current state.

Goals can be combined by conjuction and disjuction operations.

`
conj, disj :: Goal -> Goal -> Goal
`

The disjunction goal `disj g1 g2` returns a non-empty stream if either of the
two goals are successful. We can implement it as a simple interleaving of the
two streams, so that results are selected in a fair way.

```
disj g1 g2 sc = interleave (g1 sc) (g2 sc)
  where interleave xs ys = concat (transpose [xs, ys])
```

The conjunction goal `conj g1 g2` returns a non-empty stream if the second
argument can be achieved in the stream of states generated by the first. In
particular, it returns all the result states of `g2` that are successful in some
result state of `g1`, which is exactly what is achieved by the `>>=` instance
for the list monad.

```
conj g1 g2 sc = g1 sc >>= g2
```

## Terms

The original code uses (a subset of) Scheme itself as the object language. More
precisely, MuKanren expressions are all those S-expressions made of variables
and objects that can be tested for equality, and that are therefore accepted by
the unification algorithm. We won't borrow a piece of Haskell syntax here, but
instead define a data type `Term` that quite faithfully complies with the
specification just given.

```
data Atom where
  AVar :: Var -> Atom
  AData :: (Eq a, Show a, Typeable a) => a -> Atom

type Term = SExpr Atom
pattern TPair a t = SCons a t
pattern TData d = A (AData d)
```

A MuKanren term is an s-expression of atomic values `Atom`, which can be either
variables (`AVar`) or arbitrary data (`AData`). The `SExpr` datatype of
s-expressions comes from the `s-cargot` package, which also conveniently offers
some pretty-printing facility.

The constructor for variables is probably not that mind-blowing. More
interesting is the definition of the `AData` constructor. The notion of "term"
used in the paper clearly assumes an underlying
[unityped](https://existentialtype.wordpress.com/2011/03/19/dynamic-languages-are-static-languages)
programming language, particularly since it accepts objects of any shape or
form, as long as they can be compared for equality by the unification
function. An analogous result might seem quite difficult to achieve in a
strongly typed environment, but it really isn't.

`AData`'s declaration uses an existentially quantified type variable.
Existential quantification over type variables is a known typed FP idiom, and it
enables a principled form of "dynamic typing" through a simple process of
abstraction. In an expressively typed language like Haskell, dynamism is
achieved by selectively forgetting about details of the type structure that we
don't care about, while remembering some others. In our case, `AData` abstracts
over the particular type of data in use, existentially quantifying over `a`, but
explicitly remembers some details, in the form of typeclass instances that must
exist for the type. This definition allows us to treat elements of any type as
terms of our language, as long as their type can be unpacked and inspected later
at runtime (`Typeable a`), as well as tested for equality (`Eq a`). We also ask
them to be `Show`able, as printing out some program results might come in handy.

<!--Here's a small example using the `list :: [Term] -> Term` utility function to
build a an s-expr list out of a Haskell list of terms.

```
λ> putStrLn . printTerm $ list [TData 1, TData "hello", TData 2, TData ()]
(1 "hello" 2 ())
```
-->
## Unification

The unification algorithm is taken almost verbatim from the paper. The `unify`
function tries to unify two terms with respect to a base substitution assigning
a value to some of the terms' free variables. In case of success, a new
substitution is returned that is at least as defined as the input one, but
possibly extended with new bindings. The algorithm relies of an additional
function `walk` (not shown here) that simply traverses a term, applying a
substitution to it.

```
unify :: Term -> Term -> Sub -> Maybe Sub
unify u v s = aux (walk u s) (walk v s)
  where
    aux :: Term -> Term -> Maybe Sub
    aux (TVar u) (TVar v) | u == v = Just s
    aux (TVar u) v = Just ((u, v) : s)
    aux u (TVar v) = Just ((v, u) : s)
    aux Nil Nil    = Just s
    aux (TPair u v) (TPair u' v') = aux u u' >>= unify v v'
    aux (TData x) (TData y) = x ~= y >>= bool Nothing (Just s)
    aux _ _ = Nothing
```

Again, the most interesting part is the test of `TData` elements for equality.
Pattern matching on them has the effect of unpacking the quantified types and
bringing them to scope. Of course, now the type variables of the inner `x` and
`y` are different, since there's no guarantee these objects have the same type
(and that was the point of it all). Luckily, we know that these types can be
inspected to see if they are the same, and if they are, the corresponding
elements can be compared for equality. We do exactly this in the comparison
function `~=` below:

```
(~=) :: (Eq a, Typeable a, Typeable b) => a -> b -> Maybe Bool
x ~= y = fmap (\HRefl -> x == y) (eqTypeRep (typeOf x) (typeOf y))
```

The function `eqTypeRep`, from `Type.Reflection`, returns a `Maybe (a :~~: b)`,
where `a :~~: b` is the type of (kind-heterogeneous) propositional type
equality. The only constructor is `HRefl`, which when pattern matched brings
into scope a witness of `a ~ b`, allowing us to test elements of type `a` and
`b` with the `Eq` instance of `a`.

The unification goal constructor is then one that takes two terms as input and
tries to unify them under the substitution of the provided state.  If
successful, the result is just a singleton stream composed of the output
substitution produced by unification, and an unchanged fresh variable counter.

```
(===) :: Term -> Term -> Goal
(u === v) st = maybe Nil (\nu -> pure (nu, snd st)) (unify u v (fst st))
```

## A first implementation

So far, the implementation seems good enough. We can even run the first example
in the paper and get the correct result:

```
num :: Int -> Term
num = TData

emptyState :: State
emptyState = ([], 0)

aAndB :: Goal
aAndB = fresh 2 $ \[a,b] ->
  conj (a === num 7) (disj (b === num 5) (b === num 6))
```

```
λ> aAndB emptyState
[([(1,5),(0,7)],2), ([(1,6),(0,7)],2)]
```

However, the current state of affairs does not allow us to treat diverging goals
correctly. Consider the following, degenerate example:

```
loop :: Goal
loop = disj loop (num 0 === num 0)
```

The recursion on the left branch of the disjunction clearly
diverges. Nevertheless, according to the meaning of disjunction, we should be
able to witness a success for the overall goal, since the right branch of the
disjunction is trivially satisfied by any state that is passed as input. In
other words, we expect the stream produced by running this goal to be
_productive_. A productive stream is one that always produces a value (i.e., its
head) in finite time.  Notice that we _do not_ want to rule out diverging
programs from the set of valid MuKanren programs. What we want is to be able to
write recursive MuKanren goals so that diverging ones still lead to overall
productive output streams. With the current implementation, this is not
possible.

## Delayed streams

The paper's solution to non-terminating search is twofold. First, the search
strategy is changed from the incomplete depth-first search to a breadth-first
strategy (we already took care of this by implementing `disj` in terms of
`interleave`). This ensures that the algorithm does not loses itself into
infinite branches of the search space, and instead always returns a solution in
finite time, if there is one. This alone is not sufficient to achieve
productivity and avoid non-termination, given Scheme's call-by-value semantics:
the search algorithm would still try to eagerly search an infinite space until
its end, before returning any result. This is avoided by introducing _delay
fences_ in the form of what they call _reverse eta expansion_. More precisely, a
goal `g`, when eta expanded, becomes

```
(lambda (sc) (lambda () (g sc)))
```

This amounts to the well known technique of enclosing an expression in a lambda
abstraction accepting a bogus argument, in order to create a _thunk_, or
suspended computation, that allows to simulate lazy evaluation. Suspension
happens thanks to the fact that computation never happens under binders.

Reverse eta expansion still requires some modification to the rest of the
implementation. In particular, goal constructors need to account for the
presence of suspended computations. An example of how this is done is in the
`mplus` function.

```
(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))
```

What `mplus` does is to interleave streams of states, consuming the first input
stream until a suspended computation is encountered. At that point, the delay
fence is removed, and the inputs are swapped to ensure a breadth-first-like
distribution of search.

The above solution is simple and effective. Unfortunately, the user still has to
manually guard all potentially dangerous recursive calls with delay fences for
the solution to really work. This is anyway in line with the simple and terse
nature of MuKanren.

The techniques we have just seen are quite familiar to a Haskell programmer,
where lazy evaluation and guarded recursion are the default. Guarded recusion
alone, however, is of no help whatsoever if the stream being consumed is not
productive (as in the diverging example above). We still need a way to
explicitly introduce delays in the computation of streams. But since Haskell
constructors are evaluated lazily by default, introducing a delay fence is just
a matter of adding a constructor.

```
type Res = [Maybe State]
```

Goals now return lists/streams of `Maybe State`s as results. In such a list,
elements constructed out of `Just` are to be interpreted as legit outputs,
whereas `Nothing` is used to _"delay"_ a stream-returning computation with a
dummy value that, thanks to lazy evaluation, is enough to prevent divergence and
ensure productivity.

```
λ> import Data.Maybe (catMaybes)
λ> delay = (Nothing :)
λ> loop = delay loop
λ> take 10 . catMaybes $ interleave loop (fmap Just [1..])
[1,2,3,4,5,6,7,8,9,10]
```

Apart from writing a `Maybe` in front of `State`, there are still a couple of
small changes to the `conj` and `disj` functions. `conj` was originally
implemented as

```
conj g1 g2 sc = g1 sc >>= g2
```

This definition doesn't typecheck anymore: since `g1 sc` now produces a list of
`Maybe State`, the `>>=` operator for the list monad ends up feeding `Maybe
State`s into `g2`. But `g2`, being a `Goal`, takes `State` as input rather than
`Maybe State`. We need a way to send to `g2` only those `Maybe State` that are
legit results, namely those constructed from `Just`.  This kind of behaviour
resembles the `Monad` instance for `Maybe`, and indeed, the composition of `[]`
and `Maybe` that we are dealing with forms a monad, with a `>>=` operator having
just the behaviour we need!

To access the `Monad` instance for the composition of `[]` and `Maybe`, we use
the `MaybeT` monad transformer from the `transformers` package. All it takes is
a couple of `MaybeT` wrappers, and a `runMaybeT` to unwrap the result. The types
then take care of selecting the right instance of `>>=` for us.

```
conj g1 g2 sc = runMaybeT (MaybeT (g1 sc) >>= MaybeT . g2)
```

Our current `disj` implementation uses a simple interleaving function to lazily
mix two input streams. In other words, the function switches to the second
stream as soon as the first returns _some_ value, be it a legit value of a delay
(i.e., `Nothing`) value. This means that a basic amout of fairness is ensured
automatically, but it also means that the user of the DSL has no control on it.

The `disj` function in the original Scheme version is slightly different, as it
explores the first disjunct _depth first_, until a suspended computation is
encountered.  At that point, control is yielded and the second disjunct is
explored. The user of the DSL is in complete control of the search strategy for
disjunctive goals, but now fairness must be ensured manually, or by auxiliary
wrapper combinators.

I'll stick with the original version of `disj`, which can be implemented by
tweaking `interleave` according to our needs.

```
interleave
disj g1 g2 sc = concat $ (interleave `on` f) (g1 sc) (g2 sc)
  where f = (split . keepDelimsR . whenElt) isNothing
```

The auxiliary function `f` groups the input streams by contiguous sequences of
`Just`s, splitting at the first occurrence of a `Nothing`. These chunks are then
passed to the `interleave` function, as before. The result is that now, instead
of yielding after one single output, we yield at the end of a contigous sequence
of legit values. Overall, the `disj` function stays concise and declarative,
since preserving the necessary laziness in consuming the input streams is taken
care of automatically.

## A working implementation

We can now write some utility functions

```
conjs, disjs :: [Goal] -> Goal
conjs = foldr1 conj
disjs = foldr1 (\g1 -> disj g1 . (delay .)
```

The meaning of the functions above is quite self-explanatory. As in the Scheme
version, `disjs` inserts a delay in front of the second disjunct, so control is
yielded before attempting to solve the corresponding goal.  This allows to
achieve some fairness when solving goals constructed for example, as simple
disjunctions of conjunctions, as we'll se in a moment.  Unlike the Scheme
implementation, our `conjs` and `disjs` are plain functions, rather than macros.

To print some useful results, we adapt the reification code from the original
Scheme implementation into a function `reifyFst`, which extracts the value
associated to the first variable in an input `State`.

```
deepWalk :: Term -> Sub -> Term
deepWalk t s = case walk t s of
  TPair t1 t2 -> TPair (deepWalk t1 s) (deepWalk t2 s)
  t' -> t'

data ReifiedVar = RV Int deriving Eq
instance Show ReifiedVar where show (RV i) = "_." ++ show i

reifyS :: Term -> Sub -> Sub
reifyS t s = case walk t s of
  TVar v -> let n = TData (RV (length s)) in (v, n) : s
  TPair t1 t2 -> reifyS t2 (reifyS t1 s)
  _ -> s

reifyFst :: State -> Term
reifyFst sc = let v = deepWalk (TVar 0) (fst sc) in deepWalk v (reifyS v [])
```

To query a goal for the first `n` valid instantiations of the first logic
variable, we try to solve it in the empty state,
throw away the bogus `Nothing` results, and take `n` out of what is left:

```
printRes :: [State] -> IO ()
printRes = mapM_ (putStrLn . printTerm) . fmap reifyFst

run :: Int -> Goal -> IO ()
run n g = printRes . take n . catMaybes $ g emptyState
```

```
λ> anyo g = disj g (delay . anyo g)
λ> run 5 $ callFresh $ \x -> disj (anyo (TVar x === num 1)) (anyo (TVar x === num 2))
1
2
1
2
1
```

```
λ> loop = delay . loop
λ> run 5 $ callFresh (\x -> disj loop (anyo (TVar x === num 1)))
1
1
1
1
1
```

Notice the trampolining effect of the delay fences, which is exactly what we
wanted to achieve as a result of breadth-first search.

## A more involved example: `appendo`

```
appendo :: Term -> Term -> Term -> Goal
appendo l s o =
  disj (conj (TData () === l) (s === o)) $
    callFresh $ \a ->
      callFresh $ \d ->
	callFresh $ \r ->
	  conjs [ TPair (TVar a) (TVar d) === l
		, TPair (TVar a) (TVar r) === o
		, appendo (TVar d) s (TVar r) ]
```

The right-leaning chain of `callFresh` and lambdas gets tiresome pretty quickly.
Fortunately, observing the continuation-passing style signature of `callFresh`,
we can exploit the continuation monad and Haskell's do-notation to streamline
the sequence of variable creations.

```
callFresh' :: Cont Goal Var
callFresh' = cont callFresh

appendo :: Term -> Term -> Term -> Goal
appendo l s o =
  disj (conj (TData () === l) (s === o)) $ runG $ do
    a <- callFresh'
    d <- callFresh'
    r <- callFresh'
    pure $ conjs [ TPair (TVar a) (TVar d) === l
		 , TPair (TVar a) (TVar r) === o
		 , appendo (TVar d) s (TVar r) ]
```
