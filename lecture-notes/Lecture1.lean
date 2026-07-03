import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 100
set_option verso.slides.panel false

#doc (Slides) "Mathematics in Lean - Lecture 1" =>

# Mathematics in Lean

%%%
backgroundGradient := some "linear-gradient(135deg, #172554 0%, #1e3a8a 52%, #0f766e 100%)"
%%%

:::class "title-kicker"
LECTURE 1
:::

:::fitText
When is a mathematical statement true?
:::

From proofs on paper to proofs checked by Lean.

# What is a mathematical statement?

Mathematics is always formulate in the context of a theory. A theory consists of

* Basic objects and definitions
* A set of axioms
* Rules of inference


# The natural numbers

* Basic objects: postitve integers $`0, 1, 2, \dots`$.
* Definitions: addition, multiplication, etc.
* Axioms: Peano axioms about how these definitions and objects interact.

```lean
def statement (n : Nat) := n + 0 = 0 + n
```

What makes this statment true?

# A proof!

A formal proof is a sequence of steps, where each step is either

:::fragment fadeUp
an axiom,
:::

:::fragment fadeUp
an assumption currently in scope, or
:::

:::fragment fadeUp
the result of applying a valid rule to earlier lines.
:::

In the real world, writing proofs like this would take way too long. A mathematical proof aims to convice the reader that a formal proof exists.

Goal of the course: Use a computer program to verify mathematical proofs.


# How to write mathematical statements a.k.a propositions

A proposition is a statement within a theory. A proposition can either have a formal proof or not. If it has a proof, we say the proposition is true or provable.

A proposition consists of
* variables, which are the objects of the theory, $x, y, z, \dots$;
* Predicates, which are functions from objects to propositions, $`P(x), Q(y)`$;
* quantifiers $‹\forall›$ and $‹\exists›$.
* logical connectives, which combine propositions into new propositions, $`\wedge, \vee, \to, \neg`$;
* constants, which are propositions that are by definition provable or not provable, $`⊤, ⊥`$.


# Meaning of these symbols

Let A, B be two propositions. Then
* $`A \wedge B`$ is provable if and only if both A and B are provable;
* $`A \vee B`$ is provable if and only if at least one of A or B is provable;
* $`A \to B`$ is provable if and only if whenever A is provable, B is provable;
* $`\neg A := A \to ⊥`$, i.e. $¬A$ is provable if and only if a proof of A leads to a contradiction;

# The most important rule of inference

Modus Ponens: From $`P \to Q` and $`P`, we can infer $`Q`.


# Back to the natural numbers

The natural numbers are built from the following operations:
* $`0`$ is a natural number;
* Every natural number $`n`$ has a successor $`S(n)`$.
* Every two natural numbers can be added and multiplied together.

These operations follow the following axioms, called the Peano axioms:

(1) $`0`$ is not the successor of any natural number;
(2) $`S(n) = S(m)`$ implies $`n = m`$;
(3) $`\forall n, n + 0 = n`$;
(4) $`\forall n m, n + S(m) = S(n + m)`$;
(5) $`\forall n, n * 0 = 0`$;
(6) $`\forall n m, n * S(m) = n * m + n`$.

Finally, we have the induction axiom: For every predicate $P(n)$

(7) $`P(0) ∧ (\forall n, P(n) → P(S(n))) → \forall n, P(n)`$.

# Example 1

$`P = ∀n, n * S(0)= n`$.

Proof:
* axiom 6 gives $`n * S(0) = n * 0 + n`$;
* axiom 5 gives $`n * 0 = 0`$;
* by substitution $`n * S(0) = 0 + n`$;
* Remains to show $`0 + n = n`$.

# Example 2
$`Q = ∀n, 0 + n= n`$.
Want to use induction.
* Q(0) = $`0 + 0 = 0`$, which is true by axiom 3.
Need to show $`Q(n) → Q(S(n))`$.
* Assume Q(n), i.e. $`0 + n = n`$.
* Q(S(n)): $`0 + S(n) = S(n)`$.
* Axiom 4 gives $`0 + S(n) = S(0 + n)`$.
* $`S(0 + n) = S(n)`$ by Q(n).

# Example 3
S = ∀n, ∀m $`n + m = m + n`$.

:::fragment fadeUp
Proof: Induction on n with S'(n) = ∀m $`n + m = m + n`$.
* Base case: S'(0) = ∀m $`0 + m = m + 0`$, both sides are equal to m by axioms 3 and Example 2.
* Induction step: Assume S'(n), i.e. $`n + m = m + n`$ for all m. Need to show $`S(n) + m = m + S(n)`$ for all m.
* Axiom 4 gives $`S(n) + m = S(n + m)`$.
* By the induction hypothesis, $`S(n + m) = S(m + n)`.
* Axiom 4 gives $`S(m + n) = m + S(n)`
* Therefore $`S(n) + m = m + S(n)`$ for all m
:::
