import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 100
set_option verso.slides.panel false

#doc (Slides) "Mathematics in Lean - Lecture 2" =>

# Mathematics in Lean

%%%
backgroundGradient := some "linear-gradient(135deg, #172554 0%, #1e3a8a 52%, #0f766e 100%)"
%%%

:::class "title-kicker"
LECTURE 2
:::

:::fitText
From sets to types
:::

How Lean turns mathematical statements into objects that can be checked.

# Why talk about foundations again?

In ordinary mathematics we write things like

$$`x \in \mathbb{N}`

and reason about collections of objects.

:::fragment fadeUp
But what counts as a collection, and which collections are allowed?
:::

:::fragment fadeUp
A formal system must answer this precisely enough for a computer to check.
:::

# The set-theoretic picture

Set theory begins with a small number of primitive notions:

* sets;
* membership, written $`x \in A`;
* equality of sets.

New sets are built using operations such as union, intersection, and Cartesian product.

$$`A \cup B \qquad A \cap B \qquad A \times B`

# Not every collection can be a set

Suppose there were a set containing exactly the sets that do not contain themselves:

$$`R = \{x \mid x \notin x\}`

Then ask whether $`R \in R`.

:::fragment fadeUp
If $`R \in R`, its defining property says $`R \notin R`.
:::

:::fragment fadeUp
If $`R \notin R`, its defining property says $`R \in R`.
:::

:::fragment fadeUp
This is Russell's paradox: unrestricted set formation is inconsistent.
:::

# A different starting point

Type theory does not begin by putting every object into one universal domain.

:::::::hstack

:::::class "statement-box"
:::vstack
*Set-theoretic question*

Does $`x` belong to $`A`?
:::
:::::

:::class "arrow"
$`\Longrightarrow`
:::

:::::class "statement-box accent"
:::vstack
*Type-theoretic judgement*

Is `x : A` a well-formed term?
:::
:::::

:::::::

# A term is always checked against a type

```lean
#check 3
#check (3 : Nat)
#check true
#check "Lean"
```

Lean reports a type for every accepted term.

:::fragment fadeUp
The judgement `t : T` is relative: it says that `t` is a term of type `T`.
:::

# Sets and types organize information differently

:::table +colHeaders +stripedRows +rowSeps (cellGap := "0.32em 0.55em")
*
  * Set theory
  * Type theory
*
  * Objects live in a common universe
  * Every term is presented with a type
*
  * Ask whether $`x \in A`
  * Check the judgement `x : A`
*
  * Build collections by set operations
  * Build types by formation rules
*
  * Membership is a proposition
  * Ill-typed expressions are rejected
:::

# Types can encode admissible data

Suppose a program should receive a person's New York City address.

:::::::hstack

:::::class "concept-column"
:::vstack
*With an unstructured input*

Accept arbitrary data, then test whether it is a valid NYC address.
:::
:::::

:::::class "concept-column"
:::vstack
*With a suitable type*

Accept a term of type `NYCAddress`; invalid inputs cannot be supplied as such terms.
:::
:::::

:::::::

Types record rules that later programs may rely on.

# Sum types represent alternatives

Given types `A` and `B`, the sum `A ⊕ B` contains a tagged term from either side.

```lean
def byName : String ⊕ Nat := Sum.inl "Ada"
def byNumber : String ⊕ Nat := Sum.inr 42
```

The tag remembers which alternative was used.

```lean
def describe : String ⊕ Nat → String
  | Sum.inl name => name
  | Sum.inr number => s!"#{number}"
```

# Product types package data together

Given types `A` and `B`, the product `A × B` contains pairs.

```lean
def courseEntry : String × Nat := ("Lecture", 2)

#check courseEntry.1
#check courseEntry.2
```

If `p : A × B`, then:

* `p.1 : A`;
* `p.2 : B`.

# Function types describe transformations

The type `A → B` contains functions that turn every term of type `A` into a term of type `B`.

```lean
def next : Nat → Nat :=
  fun n => n + 1

#check next
#check next 4
```

:::fragment fadeUp
A function may only assume what its input type guarantees.
:::

# Two boundary cases

:::::::hstack

:::::class "statement-box"
:::vstack
*The empty type*

`Empty` has no constructors and therefore no terms.
:::
:::::

:::::class "statement-box accent"
:::vstack
*The unit type*

`Unit` has exactly one constructor, written `()`.
:::
:::::

:::::::

```lean
#check Empty
#check ()
#check (Unit.unit : Unit)
```

# Propositions are types

Lean assigns a type to an ordinary piece of data:

```lean
#check (4 : Nat)
```

It also assigns a type to a mathematical statement:

```lean
#check (2 + 2 = 4)
#check (∀ n : Nat, n + 0 = n)
```

These proposition types live in `Prop`.

# Proofs are terms

Under the Curry-Howard correspondence:

:::::::hstack

:::::class "statement-box"
:::vstack
*Logic*

A proposition $`P`

A proof of $`P`
:::
:::::

:::class "arrow"
$`\longleftrightarrow`
:::

:::::class "statement-box accent"
:::vstack
*Type theory*

A type `P : Prop`

A term `p : P`
:::
:::::

:::::::

:::fragment fadeUp
The proposition is provable exactly when its type has a term.
:::

# Logical connectives are type constructors

:::table +colHeaders +stripedRows +rowSeps (cellGap := "0.32em 0.55em")
*
  * Proposition
  * What a proof contains
  * Type-theoretic shape
*
  * $`P \land Q`
  * a proof of each
  * product
*
  * $`P \lor Q`
  * a tagged proof of one
  * sum
*
  * $`P \to Q`
  * a way to transform proofs
  * function
*
  * $`\top`
  * no information
  * unit
*
  * $`\bot`
  * impossible evidence
  * empty
:::

# Conjunction behaves like a product

To prove `P ∧ Q`, provide both a proof of `P` and a proof of `Q`.

```lean
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q :=
  And.intro p q
```

From a proof of the conjunction, either component can be projected.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q :=
  h.2
```

# Implication behaves like a function

A proof of `P → Q` accepts a proof of `P` and returns a proof of `Q`.

```lean
example (P Q : Prop) (q : Q) : P → Q :=
  fun _ => q
```

Using an implication is function application.

```lean
example (P Q : Prop) (f : P → Q) (p : P) : Q :=
  f p
```

# Quantifiers become dependent types

A proof of a universal statement works for every input:

```lean
example : ∀ n : Nat, n = n :=
  fun _ => rfl
```

A proof of an existential statement contains a witness and evidence about it:

```lean
example : ∃ n : Nat, n + 1 = 5 :=
  ⟨4, rfl⟩
```

The type of the evidence may depend on the chosen term.

# What does a theorem prover do?

Given a statement $`\varphi`:

1. Lean elaborates it as a proposition type `φ : Prop`.
2. We construct a candidate proof term `p`.
3. Lean's kernel checks the judgement `p : φ`.

```lean
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩
```

:::fragment fadeUp
Checking a proof is type checking.
:::

# What to carry into the course

:::class "closing-list"
1. Unrestricted collection-building leads to paradoxes.
2. Type theory organizes expressions through typed judgements.
3. Sums, products, and functions build richer types.
4. Propositions are types, and proofs are their terms.
5. Lean verifies mathematics by checking those terms.
:::

:::fragment fadeUp
*Next move:* read the goal as a type and ask what kind of term could inhabit it.
:::
