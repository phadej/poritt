# poritt

A type theory implementation used as a demo project for `debruijn`[^debruijn] package.

The comparable theory is implemented in Andras Kovacs' [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
as @02-typecheck-closures-debruijn@.

`poritt` uses "glued" evaluation in the style of Olle Fredriksson's [sixty](https://github.com/ollef/sixty), which provides control over unfolding of top-level definitions, i.e. the unfolding is avoided as much as possible when unneccessary,  e.g. for error displaying.

`poritt` is small, but not minimal, there are

* Sigma type, i.e. dependent pairs

* Finite sets of labels, which allow to define unit type, booleans, etc.

* Description of small universe of types, which allow to define natural numbers, list, etc simple types (with dependent induction on them!). Like in *the gentle art of levitation* https://doi.org/10.1145/1863543.1863547, but without levitation.

* Staging...

* Elaboration...

## Brief history

`poritt` started as a demo project for `debruijn`[^debruijn] package.
Then it served as learning playground.
I added glued evaluation and description of small universe of types.
Concurrently, I was looking into staging / (typed) template haskell in GHC.
Then I (somewhat successfully) tried to add staging to `poritt`.

## Description of small universe of types

`poritt` has an implementation of inductive types following the *The Gentle Art of Levitation*. We use the simples variant.
To add inductive types to `poritt`, we build a universe of datatype descriptions:

```agda
Desc : U
`1 : Desc
`X : Desc -> Desc
`Σ : (S : U) (D : S → Desc) → Desc
```

Using `Desc` values we build a "pattern functors". These all admit a least fixpoint, which we construct by tying the knot with `µ`.

For example the definition of natural numbers looks like this:

```agda
-- finite set for constructors
NatC = #[ :zero :succ ]

-- constructor "fields"
NatF : NatC -> Desc
NatF =  [ `1    (`X `1) ]  -- list syntax for finite-set elimination

-- pattern functor
NatD : Desc
NatD = `S NatC NatF

-- natural numbers
Nat : U
Nat = mu NatD
```

See `examples/nat.ptt` for the rest of natural numbers example.

This approach of adding inductive types to type-theory strikes a compromise.
It's relatively simple to implement, but it's slightly inconvenient to use.

For example, in the implementation we don't need to worry about termination checking,
as the only way to eliminate inductive types is by using induction principles.

We could imagine code looking more like `data` definitions in Haskell and Agda translated to use `Desc`, `mu` etc.
Also, there is no pattern matching, it's possible to translate (dependent) pattern matching into eliminators[^eliminating], but it's quite a lot of work. AFAIK, e.g. Agda only detects when pattern matching and is ok, it doesn't actually compile to eliminators.

## Staging

There aren't many systems combining dependent types and staging overall, and as far as I'm aware, `poritt` is unique in its own way.

The original design constraints for staging in `poritt` were:

- no run-time code generation: all top-level splices can be evaluated at compile-time.
- quotations are treated with care, not mangled by the pipeline.

These are natural restrictions when we look at staging as a tool for meta-programming.
The system should give maximal control to the programmer to generate the code they want to.

### Impredicative code

Type constructor `Code`. Usually, for example in GHC, it has type `Code : U -> U`.
In poritt we have

```agda
Code : Code [| U |] -> U
```

We could think of the definition having implicit staging levels like

```agda
Code : Code [| Uᵢ |] -> Uᵢ₊₁
```

but these are unnecessary.

### Notes about elaboration

TBW

### paradox

See `examples/paradox.ptt`

```agda
include "lib/leibniz.ptt"

id : forall (A : U) -> A -> A
id _ x = x 

-- Unit and id U Unit are beta-equivalent
type %refl : Id {U} Unit (id U Unit)

-- but we don't reduce inside the quotations
fail %refl : Id {Code [| U |]} [| Unit |] [| id U Unit |]
```

## Missing features

These might be implemented

- more support for levitation
- module system
- meta-substitution in type-error messages

These most likely wont be implemented

- general recursion
- data definitions, pattern matching

## Examples

### Push streams

It would been cooler to implement pull streams (like in [^2ltt_2024]), but as `poritt` doesn't have general recursion, it's not really possible.
To show example of some fusion, we do push streams[^push-streams].

See `examples/elaborate/push.ptt`

---

[^push-streams]: https://yanniss.github.io/streams-popl17.pdf

[^debruijn]: https://hackage.haskell.org/package/debruijn, https://github.com/phadej/debruijn

[^2ltt_2022]: *Staged Compilation with Two-Level Type Theory*

[^2ltt_2024]: András Kovács, *Closure-Free Functional Programming in a Two-Level Type
Theory* 
https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf

[^eliminating]: Jesper Cockx, Dominique Devriese, and Frank Piessens. *Pattern matching without K* https://doi.org/10.1145/2628136.2628139

[^ghc-tth-problem]: This example is the core of unsoundness in todays GHC TTH.
