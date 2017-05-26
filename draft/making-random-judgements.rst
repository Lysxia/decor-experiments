---
title: On Making Random Judgements
---

I am interested in using random testing in the design and implementation of
programming languages.

One scenario is to give random inputs to a compiler, and see what it does,
looking for incorrect behaviors: crashes, rejecting valid programs,
accepting invalid programs, miscompilations.

Another idea is that, a priori, testing is easier than proving.
When trying to prove a complex theorem, it is likely that early versions of it
are stated incorrectly, e.g., because of missing preconditions. Moreover, it
can take some effort to realize that a theorem needs fixing, and to find a way
to fix it. Random testing may alleviate this issue by applying the theorem
on many concrete values: if a counter-example is found, it helps the prover to
correct their theorem; otherwise, if no counter-example is found, it increases
confidence about the theorem's correctness.

The problem I want to talk about in this post is that of generating random
values. Indeed, many programs expect structured inputs, for compilers
these are well-typed programs. Thus to test phases that come after
type-checking, we should be able to generate well-typed programs.

Let's take the simply-typed lambda calculus.

\begin{figure}
\begin{grammar}
   t ::= x
     | \lam{x}{T}{t}
     | \app{t}{t}

   T ::= a
     | \funtype{T}{T}
\end{grammar}
\caption{Lambda terms and simple types}
\end{figure}

A common way to describe well-typed terms is as an inductive relation
between terms and types, \\(\tyj{\Gamma}{t}{T}\\).

\begin{figure}
\begin{gather*}
\infer*[Right=Lam]
  {\tyj{\Gamma, x : T_x}{t}{T}}
  {\tyj{\Gamma}{\lam{x}{T_x}{t}}{T}}
\\
\infer*[Right=App]
  {\tyj{\Gamma}{t_1}{\funtype{T_2}{T}} \\
   \tyj{\Gamma}{t_2}{T_2} }
  {\tyj{\Gamma}{\app{t_2}{t_1}}{T} }
\\
\infer*[Right=Var]
  { }
  {\tyj{\Gamma, x : T_x, \Gamma'}{x}{T_x}}
\end{gather*}
\caption{Simply-typed lambda calculus}
\end{figure}

The paper *Making Random Judgements*. presents a generic method to turn such a
specification into a generator.

We want to satisfy a constraint \\(\tyj{\cdot}{t}{T}\\), for some *unknown*
term \\(t\\) and type \\(T\\), that is, build a derivation with that judgement
at the root. We maintain a *partial derivation*, where the root is the
initial constraint, and the leaves are constraints that remain to be satisfied,
together with an *instantiation* of unknowns.

\begin{gather*}
\left.
\tyj{\cdot}{t}{T}
\hspace{3em}\middle|\quad
\begin{aligned}
t &= ? \\
T &= ?
\end{aligned}
\right.
\end{gather*}

We satisfy that constraint by applying a typing rule at random, for example
\textsc{Lam}. This introduces new constraints: two equality constraints
*instantiate* \\(t\\) to be a lambda--with a fresh body \\(t_1\\)--and \\(T\\)
to be a function type--with fresh argument and result types \\(T_1\\),
\\(T_2\\); one new typing constraint \\({\tyj{x : T_1}{t_1}{T_2}}\\) has to be
satisfied.

\begin{gather*}
\infer*[Right=Lam]
  {\tyj{x : T_1}{t_1}{T_2}}
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= ?
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= ? \\
T_2 &= ?
\end{aligned}
\right.
\end{gather*}

This time, the \textsc{App} rule was picked, refining \\(t_1\\)
and producing two new typing constraints.

\begin{gather*}
\infer*[Right=Lam]
  {\infer*[Right=App]
    {\tyj{x : T_1}{t_2}{T_3} \\
     \tyj{x : T_1}{t_3}{T_4}}
    {\tyj{x : T_1}{t_1}{T_2}}
    }
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= \app{t_2}{t_3} \\
t_2 &= ? \\
t_3 &= ?
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= ? \\
T_2 &= ? \\
T_3 &= \funtype{T_4}{T_2} \\
T_4 &= ?
\end{aligned}
\right.
\end{gather*}

When multiple leaves are available, we pick one at random, and then
apply a random rule. Here, we first pick the leaf on the left (corresponding
to the function term \\(t_2\\) in the application \\(t_1 = \app{t_2}{t_3}\\)),
and apply the \textsc{Var} rule. This yields an equality \\(T_1 = T_3\\) which
we simplify by replacing all occurences of \\(T_3\\) with \\(T_1\\).

\begin{gather*}
\infer*[Right=Lam]
  {\infer*[Right=App]
    {\infer*[Right=Var]
      { }
      {\tyj{x : T_1}{t_2}{T_1}} \quad\\
     \tyj{x : T_1}{t_3}{T_4}}
    {\tyj{x : T_1}{t_1}{T_2}}
    }
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= \app{t_2}{t_3} \\
t_2 &= x \\
t_3 &= ?
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= \funtype{T_4}{T_2} \\
T_2 &= ? \\
T_4 &= ?
\end{aligned}
\right.
\end{gather*}

There is still one leaf. We apply \textsc{Lam} to it, instantiating
\\(t_3\\) to a lambda, and growing another leaf.

\begin{gather*}
\infer*[Right=Lam]
  {\infer*[Right=App]
    {\infer*[Right=Var]
      { }
      {\tyj{x : T_1}{t_2}{T_1}} \quad\\
     \infer*[Right=Lam]
      {\tyj{x : T_1, y : T_5}{t_4}{T_6}}
      {\tyj{x : T_1}{t_3}{T_4}}}
    {\tyj{x : T_1}{t_1}{T_2}}
    }
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= \app{t_2}{t_3} \\
t_2 &= x \\
t_3 &= \lam{y}{T_5}{t_4} \\
t_4 &= ?
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= \funtype{T_4}{T_2} \\
T_2 &= ? \\
T_4 &= \funtype{T_5}{T_6} \\
T_5 &= ? \\
T_6 &= ?
\end{aligned}
\right.
\end{gather*}

We apply \textsc{Var} on the last remaining leaf,
instantiating \\(t_4\\) to the variable \\(y\\).

\begin{gather*}
\infer*[Right=Lam]
  {\infer*[Right=App]
    {\infer*[Right=Var]
      { }
      {\tyj{x : T_1}{t_2}{T_1}} \quad\\
     \infer*[Right=Lam]
      {\infer*[Right=Var]
        { }
        {\tyj{x : T_1, y : T_5}{t_4}{T_5}}}
      {\tyj{x : T_1}{t_3}{T_4}}}
    {\tyj{x : T_1}{t_1}{T_2}}
    }
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= \app{t_2}{t_3} \\
t_2 &= x \\
t_3 &= \lam{y}{T_5}{t_4} \\
t_4 &= y
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= \funtype{T_4}{T_2} \\
T_2 &= ? \\
T_4 &= \funtype{T_5}{T_5} \\
T_5 &= ?
\end{aligned}
\right.
\end{gather*}

Two types remain uninstantiated, and we may instantiate them arbitrarily, e.g.,
with two type variables \\(a, b\\). We obtain a derivation for the following
judgement:

\\[\tyj
  {\cdot}
  {\lam{x}{\funtype{(\funtype{b}{b})}{a}}{\app{x}{(\lam{y}{b}{y})}}}
  {\funtype{(\funtype{(\funtype{b}{b})}{a})}{a}}\\]

### Outline

A **system** is given by:

- a **syntax** of terms \\(x\\) given by some grammar;
- a collection of **judgements**, i.e., tagged tuples \\(J(\bar{x})\\),
  defined by a set of **inference rules**.

\\[\infer{J_1(\bar{x_1}) \\ \dots \\ J_n(\bar{x_n})}{J_0(\bar{x_0})}\\]

where \\(\bar{x_0}, \bar{x_1}, \dots, \bar{x_n}\\) are tuples of
*partial terms*, which may have **unknowns** (or unknown metavariables) in
place of subterms.

We may preprocess inference rules to take the following shape:

\\[\infer{
  \bar{u_0} = \bar{x_0} \\ \bar{u_1} = \bar{x_1} \\ \dots \\ \bar{u_n} = \bar{x_n} \\\\
  J_1(\bar{u_1}) \\ \dots \\ J_n(\bar{u_n})}
  {J_0(\bar{u_0})}\\]

where \\((\bar{u_i})\\) are tuples of unknowns, connected together by the equalities,
which can be seen as a primitive kind of judgement.

A **derivation** \\(D\\) is a directed graph whose edges are judgements, and nodes
are inference rules (equalities are implicit). Each node has one predecessor
(the conclusion of a rule) and zero or more successors (the premises).
Following conclusions leads to a special dangling edge, the **root**.
Following premises may lead to other dangling edges, the **leaves**.
A **partial derivation** may have leaves, as opposed to a
**complete derivation**.

We **grow** a derivation by attaching new rules to the leaves. This corresponds
to a non-deterministic relation between a derivation \\(D\\) and a new one
\\(D'\\) having one more node, together with a set of equalities detached from
it:

\\[D \to_\mathrm{grow} D', E\\]

We gather equalities to form a substitution by **unification**. This is a
partial relation:

\\[\Theta, E \to_\mathrm{unify} \Theta'\\]

The **generator** is obtained by combining these relations.

\\[D,\Theta \to_\mathrm{gen} D',\Theta' \quad\iff\quad
   D\to_\mathrm{deriv}D',E \;\wedge\; \Theta,E \to_\mathrm{unify} \Theta' \\]

We start from a partial derivation \\(D_0\\) consisting of a single edge dangling
on both ends, and an empty substitution \\(\Theta_0\\).
We maintain the invariant that, if we perform the current substitution
\\(\Theta\\) on the current derivation \\(D\\), then every node is a valid
*instantiation* of the corresponding inference rule of the input system.

### Occurs check

In the previous example, in the last step, assume we chose the variable \\(x\\)
rather than \\(y\\).

\begin{gather*}
\infer*[Right=Lam]
  {\infer*[Right=App]
    {\infer*[Right=Var]
      { }
      {\tyj{x : T_1}{t_2}{T_1}} \quad\\
     \infer*[Right=Lam]
      {\infer*[Right=Var]
        { }
        {\tyj{x : T_1, y : T_5}{t_4}{T_1}}}
      {\tyj{x : T_1}{t_3}{T_4}}}
    {\tyj{x : T_1}{t_1}{T_2}}
    }
  {\tyj{\cdot}{t}{T}}
\\
\left|\quad
\begin{aligned}
t   &= \lam{x}{T_1}{t_1} \\
t_1 &= \app{t_2}{t_3} \\
t_2 &= x \\
t_3 &= \lam{y}{T_5}{t_4} \\
t_4 &= x
\end{aligned}
\quad
\begin{aligned}
T   &= \funtype{T_1}{T_2} \\
T_1 &= \funtype{T_4}{T_2} \\
T_2 &= ? \\
T_4 &= \funtype{T_5}{T_1} \\
T_5 &= ?
\end{aligned}
\right.
\end{gather*}

Then we get an infinite type:

\\[T_1 = \funtype{(\funtype{T_5}{T_1})}{T_2}\\]

A simple work around is of course to perform occurs checks. However this
will not be sufficient with more elaborate type systems.

### Polymorphism

The generation of well-typed terms is achieved by *unification* of
unknown terms and types with *patterns* that appear in typing rules.
However, rules sometimes involve *metafunctions* (as they call it in
*Making Random Judgements*), which do not play well with unification.

For instance, the variable rule can be more explicitly expressed
in the following way:

\begin{equation*}
\infer*[Right=Var+]
  {x \in \Gamma = \top}
  {\tyj{\Gamma}{x}{T_x}}
\end{equation*}

where we may define \\(x \in \Gamma\\) as a (meta)function:

\begin{align*}
  x \in (y : T_y, \Gamma) &= x \in \Gamma, \text{ if } x \neq y \\
  x \in (x : T_x, \Gamma) &= \top \\
  x \in \cdot &= \bot
\end{align*}

In the case of a language with polymorphism, we may have the following rule for
type application:

\begin{equation*}
\infer*[Right=TyLam]
  {\tyj{\Gamma}{t}{\forall \alpha. T_2}}
  {\tyj{\Gamma}{\tyapp{t}{T_1}}{\subst{T_2}{T_1}{\alpha}}}
\end{equation*}

Substitution also corresponds to a metafunction, and we can move it
as an premise to our rule so that a judgement always takes the shape of a tuple
of patterns.

\begin{equation*}
\infer*[Right=TyLam+]
  {\tyj{\Gamma}{t}{\forall \alpha. T_2} \\ \subst{T_2}{T_1}{\alpha} = T_3}
  {\tyj{\Gamma}{\tyapp{t}{T_1}}{T_3}}
\end{equation*}

Metafunctions can be defined by pattern matching on the arguments.
*Making Random Judgements* compiles metafunctions to inductive relations.

\begin{gather*}
\infer
  {\subst{T_1}{T}{\alpha} = T_1' \\
   \subst{T_2}{T}{\alpha} = T_2'}
  {\subst{(\funtype{T_1}{T_2})}{T}{\alpha} = \funtype{T'_1}{T'_2}}
\\
\infer
  {\beta = \alpha}
  {\subst{\beta}{T}{\alpha} = T}
\\
\infer
  {\beta \neq \alpha}
  {\subst{\beta}{T}{\alpha} = \beta}
\end{gather*}

