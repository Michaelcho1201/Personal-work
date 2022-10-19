Require Export DMFP.Day10_expressions.
Require Import Coq.Setoids.Setoid.

(* ################################################################# *)
(** * Propositions *)

(** We've spent the last five weeks learning how to program in
    Gallina.  Along the way, we've noticed ways our programs can be
    right or wrong---give 'correct' answers or subtly err.

    We'll spend the next four weeks thinking more rigorously about the
    programs we've written, proving various _properties_.
*)

(** Why care about proofs? Here are two reasons, one pragmatic and one
    academic.

    1. When you write code, the reasoning you do is about questions of
    efficacy, correctness, and efficiency. Efficacy asks, "How can I
    achieve this end?" Correctness asks, "Have I implemented my plan
    correctly? Do I get the correct output for the inputs I care
    about?" Efficiency asks, "Am I doing this in the best way
    possible? Can I achieve the same ends doing less work or using
    less space?" The process of answering these questions is the same
    reasoning exercised when doing proof! Our exercises in proof are
    exercises for your reasoning skills.

    2. An algorithm without proof is just a pile of code. Computer
    science is the rigorous study of computation, and rigor demands
    proof. If you are a computer scientist, you make claims and rely
    on some form of proof for justifying those claims. Proofs vary
    from subjective experimental (e.g., testing a user interface with
    real users) to objective experimental (e.g., testing code on a
    variety of computers) to informal (e.g., argumentation in favor of
    one design over another) to formal (e.g., paper proofs or verified
    proofs in Coq). You'll learn other forms in other courses; in this
    course, you learn formal proof. It's the most important for you to
    learn early: you've likely been exposed to the other forms of
    proof elsewhere in your life, but formal proof is rarely taught
    before college.
  *)

(** Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

(** Here we assert that [3 = 3], read "3 is equal to 3". This
    proposition holds, i.e., it's possible to prove it. Not that we
    know how yet. *)
Check 3 = 3.
(* ===> Prop *)

(** Here we assert that [plus] is commutative. There are several parts
    to this proposition.

    The [forall n m : nat, ... blah ...] part is a _quantifier_. We're
    saying that "for arbitrary [n] and [m] of type [nat], it is the
    case that [... blah ...]". Here, our "[blah]" is [n + m = m + n],
    i.e., for any [n] and [m], the number [n + m] is equal to [m + n],
    i.e., order doesn't matter for addition, i.e., addition is
    commutative.

    This proposition is also provable.
*)
Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** So far we've seen two ways to form a [Prop]: equality and
    quantification. We can give a grammar in BNF (Backus-Naur Form):

   PROP ::= EXPR1 = EXPR2
          | forall x : TYPE, PROP

   where [EXPRi] refers to an expression and [TYPE] refers to some
   type.  When you have multiple variables in a quantifier, it's like
   stringing them together:

   forall n m : TYPE, PROP

   is the same as

   forall n : TYPE, forall m : TYPE, PROP

   You can of course have variables of different types. Here is a
   proposition asserting that the length of [repeat b n] is [n], for
   all [b] and [n]. This proposition is also provable.
*)
Check forall (b : base) (n : nat), length (repeat b n) = n.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true. *)

(** Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)

Check 2 = 2.
(* ===> Prop *)

(** This one seems unlikely. Translating to English, "For any natural
    number [n], it is the case that [n] is equal to 2." There are
    definitely natural numbers other than 2. Like, say, 1. Or 0. Or
    731. None of those are equal to [2]. This proposition does not
    hold---it is not provable. In fact, it's possible to prove that
    this proposition does not hold. *)
Check forall n : nat, n = 2.
(* ===> Prop *)

(** Even more baldly wrong. It is not the case that [3 = 4]. It is
    possible to prove that this proposition does not hold. *)
Check 3 = 4.
(* ===> Prop *)

(** Indeed, propositions don't just have types: they are
    _first-class objects_ that can be manipulated in the same ways as
    the other entities in Coq's world. Propositions can be used in
    many other ways.  For example, we can give a name to a proposition
    using a [Definition], just as we have given names to expressions
    of other sorts. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the notion
    of an _injective function_: no two inputs share the same
    output. Literally: if [f] maps [x] and [y] to the same value, then
    [x] has to be the same as [y]. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

(** The proposition that [S], the successor function, is injective. This
    property holds. *)
Check (injective S).
(** The proposition that [pred], the successor function, is
    injective. This property does not hold: [pred 0 = pred 1 = 0]. *)
Check (injective pred).

(** The equality operator [=] is also a function that returns a
    [Prop]. That's why it showed up in our BNF for [Prop] earlier!

    The expression [n = m] is syntactic sugar for [eq n m] (defined
    using Coq's [Notation] mechanism). Because [eq] can be used with
    elements of any type, it is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, so we need to turn
    off implicit arguments to see the full type of [eq].) *)

(* ################################################################# *)
(** * Simple proofs *)

(** Let's get started with some proofs! The general format of a theorem is:

Theorem NAME : PROP.
Proof.
  TACTICS...
Qed.

    Where [NAME] is the name of the theorem and [PROP] (of type
    [Prop]) is the proposition we'll prove.

    [TACTICS...] are the way we'll do proofs in Coq. They loosely
    correspond to the kinds of things people write in paper proofs,
    but the correspondence isn't one-to-one.
*)

(* ================================================================= *)
(** ** Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.

    A "proof by simplification" can be used to prove a variety of
    properties.  For example, the fact that [0] is a "neutral element"
    for [+] on the left can be proved just by observing that [0 + n]
    reduces to [n] no matter what [n] is, a fact that can be read
    directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl. reflexivity.  Qed.

(** What's happening here? It's worth stepping through the proof
    slowly, looking at the various views: there's the main script
    screen, the screen with the goal and context, and a response
    screen.

    We write [Theorem] and then a name for our theorem---here
    [plus_O_n]. Then we write a _proposition_, in this case [forall n
    : nat, 0 + n = n], i.e., for any possible natural number [n], it
    is the case that [0 + n] is equal to [n]. We'll talk more about
    what counts as a proposition later in the course.

    After we type the [Proof.] keyword, we're shown a screen like the
    following:

1 subgoal, subgoal 1 (ID 50)

  ============================
  forall n : nat, 0 + n = n
*)
(** The first line says how many cases we're considering in our proof
   at present: there's 1 subgoal, and we're currently working on
   it. That is: our proof has only one case.

   Then there's a line. Beneath the line is our *goal*---that's what
   we're trying to prove. Above the line is our *context*, which is
   currently empty.

   The way a proof works is that we try to show that given our
   context, our goal *holds*, that is, that our goal is a true
   proposition.

   In Coq, we use tactics to manipulate the goal and context, where
   Coq will keep track of the goal and context for us. On paper (or on
   a chalkboard or in person), we'll use natural language (for CS 54,
   English) to manipulate the goal and context, which we'll keep
   track of ourselves.

   Throughout the course, we'll try to keep parallel tracks in mind:
   how does proof work in Coq and how does it work on paper? We'll
   only really be _doing_ proofs in Coq at first, and then we'll
   switch and only do proofs on paper. After this course, you'll
   probably only use paper proofs. We'll be using Coq as a tool to
   help you learn the ropes of paper proof. One of the hardest things
   about paper proof is that it can be very easy to get confused and
   make mistakes, breaking the "rules". Coq enforces the rules! Using
   Coq will help you internalize the rules.

   After the [Proof.] keyword comes our *proof script*, a series of
   *tactics* telling Coq how to manipulate the proof state. Each
   tactic is followed by a period.

   Before explaining the proof script, let's see the above proof in
   English.

- _Theorem_: For any natural number [n],

      0 + n = n.

    _Proof_: Let [n] be given. We must show that

     0 + n = n.

    By the definition of [plus], we know that [0+n] reduces to [n].
    Finally, we have

    n = n

    immediately. _Qed_.

    How does the above proof work? To start out, we needed to show
    that [forall n : nat, 0 + n = n]. The line _Let [n] be given_
    phrases the proof as a sort of a game. To show that [0 + n = n]
    for _any_ [n], we let our imaginary "opponent" give us any [n]
    they please. Now we have that [n] in hand---that is, in our
    proof's context---we want to show that [0 + n = n], our new
    goal. Showing this goal is as simple as looking at the definition
    of [plus]: the first case of the pattern match says that when the
    first argument to [plus] is [0], [plus] just returns its second
    argument---in this case [n]. So [0 + n] reduces to [n]; finally,
    we observe that [n = n] immediately---an inarguable fact about
    natural numbers.

    How does the proof in Coq work? Our first tactic is [intros] with
    the argument [n]. Our goal is [forall n : nat, 0 + n = n]; in
    English, our goal is to show that for every possible [n] that is a
    natural number [0 + n] is equal to [n]. The [intros] tactic
    *introduces* things into the context: our goal was a [forall], so
    [intros] will try to introduce whatever's been *quantified* by the
    for all. Here give a name explicitly: [intros n] says to name the
    introduced variable [n] and put it into our context:
*)
(**

1 subgoal, subgoal 1 (ID 51)

  n : nat
  ============================
  0 + n = n
*)
(** We could have chosen a different name---go back and change it to
    read [intros m] and see what goal you get! (It's generally good
    style to use the name in the quantifier, since it's a little
    clearer.)

    Our next tactic is [simpl], which asks Coq to [simplify] our goal,
    running a few steps of computation:

1 subgoal, subgoal 1 (ID 53)

  n : nat
  ============================
  n = n
*)
(** Our context remains the same, but our new goal is to show that [n
    = n]. To do so, we use the [reflexivity] tactic, named after the
    property of equality: all things are equal to themselves.

   When we run the tactic, we get a new readout:

No more subgoals.
(dependent evars: (printing disabled) )
*)
(** Coq is being a little too lowkey here: we proved it! To celebrate
    (and tell Coq that we're satisfied with our proof), we say [Qed.],
    which is short for _quod erat demonstrandum_, which is Latin for
    "that which was to be proved" which is perhaps better said as "and
    we've proved what we want to" or "and that's the proof" or "I told
    you so!" or "mic drop". Then Coq acknowledges that we're truly done:

plus_O_n is defined
*)
(** The paper and Coq proofs are very much in parallel. Here's the
    paper proof annotated with Coq tactics:

- _Theorem_: For any natural number [n],

      0 + n = n.

    _Proof_: Let [n] be given ([intros n.]). We must show that

     0 + n = n.

    By the definition of [plus], we know that [0+n] reduces to [n] ([simpl.]).
    Finally, we have

    n = n

    immediately ([reflexivity.]). _Qed_.

    Later in the course, we'll have to work hard to write good
    proofs. At first our proofs will follow the Coq tactics quite
    closely. But just like any other kind of writing, proof writing is
    a craft to be honed and practiced. *)

(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that [reflexivity] is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to [simpl] were actually not needed, because
    [reflexivity] can perform some simplification automatically when
    checking that two sides are equal; [simpl] was just added so that
    we could see the intermediate state -- after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem: *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters. *)

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal.

    If you want to be extra meticulous, you can use a parameter with
    [simpl]: the name of the function whose definition you want to
    simplify through (e.g. [simpl plus] or [simpl mult]).

 *)

(* ################################################################# *)
(** * The [intros] and [apply] Tactics *)

(** Most of the properties we will be interested in proving
    about programs will begin with some quantifiers (e.g., "for all
    numbers [n], ...") and/or hypothesis ("assuming [m=n], ...").  In
    such situations, we will need to be able to reason by _assuming
    the hypothesis_ -- i.e., we start by saying "OK, suppose [n] is
    some arbitrary number," or "OK, suppose [m=n]."

    The [intros] tactic permits us to do this by moving one or more
    quantifiers or hypotheses from the goal to a "context" of current
    assumptions.
 *)

(** Here's an example of a trivial use of hypothesis: every
    proposition implies itself.

    The arrow symbol [->] is pronounced "implies."  We've already
    defined a notion of implies on booleans [impb]; now we have a
    notion of implies on _propositions_.

    The way a proof with implies works is: you have to prove what's to
    the right of the arrow... but you may assume what's to the left.

    We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma.  We can use [apply] when some hypothesis
    or an earlier lemma exactly matches the goal:
*)

Lemma assumed_A : forall A : Prop, A -> A.
Proof.
  intros A HA.
  (** Let a proposition [A] be given such that [A] holds (call this
      hypothesis [HA]).

      We must prove that [A] holds.
   *)
  apply HA.
  (** We find [A] by [HA]. *)
Qed.

Lemma modus_ponens : forall P Q,
    (P -> Q) ->
    P ->
    Q.
Proof.
  intros P Q HPQ HP.
  apply HPQ.
  apply HP.
Qed.

(** [modus_ponens] is the first theorem we've seen that has multiple
    hypotheses. How should we parse the following proposition?

    (P -> Q) ->
    P ->
    Q.

    The answer is that implication is _right associative_, that is,
    we assume that parentheses go on the right, as in:

     (P -> Q) ->
     (P ->
      Q).

    If we were to read this proposition aloud, we could naively
    read it as:

    if it is the case that [P -> Q],
    then if it is the case that [P]
         then it is the case that [Q].

    But we can read it more naturally as:

    if it is the case that [(P -> Q)]
                       and [P],
    then it is the case that [Q].

    That is, we've translated nested implications to a conjuction,
    with the word "and". We'll talk more about conjunctions in [Logic].
 *)

(** **** Exercise: 2 stars, standard (implies_PQR)

    Remove "[Admitted.]" and fill in the proof. *)

(** Use [intros] and [apply] to show that if [P] implies [Q] and [Q]
    implies [R] and [P] holds, then [R] holds.

    Hint: you'll want to use _backwards_ reasoning. To prove that [R]
    holds, it suffices to show that [Q] holds (because [Q -> R]). To
    prove that [Q] holds, it suffices to show that [P] holds (because
    [P -> Q]). But we know [P] holds, so...  *)
Lemma implies_PQR : forall P Q R : Prop,
  (P -> Q) ->
  (Q -> R) ->
  P ->
  R.
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR.
  apply HPQ.
  apply HP.
Qed.
(** [] *)

(* ################################################################# *)
(** * Logical connectives *)

(** Let's look at more kinds of proposition: logical connectives let
    us form new propositions from others. We've already seen one
    connective: [->], implication. We'll meet many more: [/\],
    conjunction; [\/], disjunction; [~], negation; and [<->],
    if-and-only-if a/k/a iff. For now, we'll look at conjunction,
    disjunction, and the always-true proposition, [True]. *)

(* ================================================================= *)
(** ** Conjunction *)

(** For any propositions [A] and [B], if we assume that [A] is
    true and we assume that [B] is true, we can conclude that [A /\ B]
    is also true.

    Here we have two arrows. We can read the proposition aloud in
    stilted English as:

    - For all propositions [A] and [B], if it is the case that [A]
    holds, then if it is the case that [B] holds, then [A /\ B] (read
    "[A] and [B]") holds.

    Chains of arrows, like curried functions, are pronounced
    idiomatically as a single condition, i.e.:

    - For all propositions [A] and [B], if [A] and [B] hold, then [A
    /\ B] holds.

    Let's look at the proof!  *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  (* Let propositions [A] and [B] be given. Suppose that [A] holds
     (call this hypothesis [HA]) and [B] holds (call this hypothesis
     [HB]. *)
  split.
  (* We need to prove [A /\ B]. To prove a conjunction, we must prove
     both of its parts.

     Whenever you start working on a subpart, you should use a bullet
     [-]. Like in an outline for a paper, bullets nest. You can use
     [-], [+], and [*] as bullets. The order doesn't matter, but each
     level has to be homogeneous. If you run out of bullets, you can
     start doubling or tripling them, as in [--], [+++], [**], etc.
   *)
  - (* To prove the left-hand side of the conjunction, we need to show
       [A]. We have this by hypothesis [HA]. *)
    apply HA.
  - (* To prove the left-hand side of the conjunction, we need to show
       [B]. We have this by hypothesis [HB]. *)
    apply HB.
Qed.

(** In addition to the outlining marks [-], [+], and [*], you can use
    curly braces to enter new outline levels. Every time you use curly
    braces, you reset the tracking of outlines, and you can reuse any
    outlining symbol. *)

Lemma and_intro_braces : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  { apply HA. }
  { apply HB. }
Qed.

(** Formatting matters. Coq will accept proofs in any valid
    formatting, but humans... less so. Keeping things clean is very
    important: for now, it helps us grade your work. Later on, clean
    formatting will make it much easier to work with other people.

    Many software development projects care so much about clean
    formatting that they use automatic formatters, and no code can be
    added to the project unless it meets the formatting guidelines!
    *)
Lemma and_intro_sloppy : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split. apply HA.
apply HB.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  (* [apply] works with everything defined so far, not just
     hypotheses/assumptions in your context. *)
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(** **** Exercise: 2 stars, standard (and_PQ)

    Some more practice with implications and conjunctions. If [P]
    implies [Q] and you know [P], then you know both [P] and [Q]. *)
Lemma and_PQ : forall P Q : Prop,
    (P -> Q) ->
    P ->
    P /\ Q.
Proof.
  intros P Q HQ HP.
  split.
  - apply HP. 
  - apply HQ. apply HP. 
Qed.
(** [] *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop].) *)

(** To show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  (* A fork in the road! Hang a left. *)
  left.
  apply HA.
Qed.

Lemma or_intro_r : forall A B : Prop, B -> A \/ B.
Proof.
  intros A B HB.
  (* You can't go wrong going right! *)
  right.
  apply HB.
Qed.

Check or.
(* ===> or : Prop -> Prop -> Prop *)

(** In natural language 'or' is often interpreted to be exclusive (one
    or the other) rather than inclusive (at least one, possibly
    both). In formal work, disjunction is inclusive, meaning 'at least
    one'.

    Consider the proposition [2 = 2 \/ 4 = 4]. Both sides are true,
    but a proof need only show one side. In fact, it would be a little
    bit strange---not wrong, but strange---for a proof to show both!
 *)
Lemma or_inclusive1 : 2 = 2 \/ 4 = 4.
Proof. left. reflexivity. Qed.

Lemma or_inclusive2 : 2 = 2 \/ 4 = 4.
Proof. right. reflexivity. Qed.

(** **** Exercise: 1 star, standard (or_which) *)
Lemma or_which : forall P Q: Prop,
    (P -> Q) ->
    Q ->
    P \/ Q.
Proof.
  intros P Q HQ HP.
  right.
  apply HP.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Truth *)

(** Coq's standard library also defines [True], a proposition that is
    trivially true. To prove it, we use the predefined constant [I :
    True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** If you can't remember that [I] is the single proof of [True], you
    can also just use the [reflexivity] tactic. *)
Lemma True_is_true' : True.
Proof. reflexivity. Qed.

Lemma True_and_id : True /\ True.
Proof.
  split.
  - apply I.
  - apply I.
Qed.

Lemma True_or_l : forall A : Prop, True \/ A.
Proof.
  left. apply I.
Qed.

Lemma True_or_r : forall A : Prop, A \/ True.
Proof.
  right. apply I.
Qed.

(** [True] is used quite rarely, since it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis.

    But [True] can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see examples of such uses of [True] later on.
*)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a universal claim about all numbers [n]
    and [m], it talks about a more specialized property that only
    holds when [n = m].  The arrow symbol is pronounced "implies."
    We've already defined a notion of implies on booleans [impb]; now
    we have a notion of implies on _propositions_.

    The way a proof with implies works is: you have to prove what's to
    the right of the arrow... but you may assume what's to the
    left. That is, to show that [n + n = m + m], we know (in our
    context) not only that [n] and [m] are natural numbers, but in
    fact it is the case that [n = m].

    As before, we need to be able to reason by assuming we are given
    such numbers [n] and [m].  We also need to assume the _hypothesis_
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.)

    Here's a paper proof of the same theorem, with the tactics
    interwoven. 
- _Theorem_: For any natural numbers [n] and [m],
             if

      n = m

             then

      n + n = m + m.

    _Proof_: Let [n] and [m] be given ([intros n m.]) such that [n = m]
    ([intros H]). We must show:

      n + n = m + m.

    Since we've assumed that [n = m], we can replace each reference to [n] on
    the left-hand side with a reference to [m], and we have

      m + m = m + m

    immediately ([reflexivity.]). _Qed_.
 *)

(** **** Exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H H2.
  rewrite -> H.
  rewrite -> H2.
  reflexivity.
Qed.
(** [] *)

(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** Note that we've just rewritten by an existing theorem: the proof
    of [mult_0_plus] uses the proof of [plus_O_n].

    In an informal proof, we might use language by "by [plus_0_n], we
    know...". For example:

- _Theorem_: For any natural number [n] and [m],

      (0 + n) * m = n * m.

    _Proof_: Let [n] and [m] be given ([intros n m.]). We must show:

      (0 + n) * m = n * m.

    By [plus_0_n], we know that [0 + n = n], so we can replace [0 + n] on
    the left-hand side with just [n], and we have

      n * m = n * m

    immediately ([reflexivity.]). _Qed_.

 *)

(** **** Exercise: 2 stars, standard, optional (mult_S_1)

    Optional exerises are just good practice. They're worth no points. *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity.
Qed.

  (* (N.b. This proof can actually be completed without using [rewrite],
     but please do use [rewrite] for the sake of the exercise.)

    [] *)

(* ################################################################# *)
(** * The [apply] Tactic, Revisited *)

(* Let's look at a silly theorem about natural numbers: *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** Here, we could finish with "[rewrite -> eq2.  reflexivity.]" as we
    have done several times before.  We can achieve the same effect in
    a single step by using the [apply] tactic instead: *)

  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. If there are no premises (i.e., [H]
    isn't an implication), then you're done! *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] that binds some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, standard (silly_ex)

    Complete the following proof without using [simpl]. *)

Print evenb.
Print oddb.
(** It's often helpful to look at definitions before doing proofs! *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq2.
Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) theorem,
    lemma, hypothesis, or other fact being applied must match the goal
    exactly -- for example, [apply] will not work if the left and
    right sides of the equality are swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = eqb n 5  ->
     eqb (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry.
  simpl. (* (This [simpl] is optional, since [apply] will perform
            simplification first, if needed.) *)
  apply H.  Qed.

(** To sum up, one can say [apply H] when [H] is a hypothesis in the
    context or a previously proven lemma of the form [forall x1 ...,
    H1 -> H2 -> ... -> Hn] and the current goal is shape [Hn] (for
    some instantatiation of each of the [xi]). After running [apply H]
    in such a state, you will have a subgoal for each of [H1] through
    [Hn-1]. In the special case where [H] isn't an implication, your
    proof will be completed.

    The informal analogue of the [apply] tactic is phrasing like "by
    H, it suffices to show Hn by proving each of H1, ..., Hn-1",
    followed by a proof of those subsidiary parts. In the case where
    [H] isn't an implication, you can try using language like "we are
    done by [H]" or "which [H] proves exactly".
 *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might like to pull it out
    as a lemma recording, once and for all, the fact that equality is
    transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need to be very clear about how we are [apply]-ing [trans_eq]. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(** If we simply tell Coq [apply trans_eq] at this point, it can tell
    (by matching the goal against the conclusion of the lemma) that it
    should instantiate [X] with [[nat]], [n] with [[a,b]], and [o]
    with [[e,f]].  However, the matching process doesn't determine an
    instantiation for [m]: we have to supply one explicitly by being
    more specific about the theorem we're using.  The proofs we have
    give us truths with parameters, and just as with function
    parameters we can specify those when we use the proof. *)

  apply (trans_eq (list nat) [a;b] [c;d] [e;f]).
  apply eq1. apply eq2.   Qed.

(** Most of the time, context is enough and Coq can guess the
    right parameters using parameter synthesis; we might have instead
    written [apply (trans_eq _ [a;b] [c;d] [e;f])] or even [apply
    (trans_eq _ _ [c;d] _)].

    Why do we need to specify [[c;d]] at all?  Because that particular
    list is our "bridge" between the two facts we know, and Coq
    doesn't look at the theorems in scope when guessing what to apply,
    only at the goal we're matching the applied proof against.

    Informally, we might say "by the transitivity of equality via [[c;d]]".

 *)

(** **** Exercise: 3 stars, standard (trans_eq_exercise)

    Here's a lemma to practice applying theorems with parameters. *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1  eq2.
  apply trans_eq with m.
  apply eq2. apply eq1.
Qed.
(** [] *)

(** The informal analogue of [apply (H m)] is to say "by [H] with [m]
    for [x]" or "which we can see by [H] on [m]".

    Interestingly, we can use these more specific theorems anywhere
 we'd use a regular theorem, including [rewrite]!  *)

(* ################################################################# *)
(** * Propositions so far *)

(** We've seen quite a few different propositions! Equality, universal
    quantification, implication, conjunction, disjunction, and the
    always-true proposition. *)

(** PROP ::= EXPR1 = EXPR2
           | forall x : TYPE, PROP
           | PROP1 -> PROP2
           | PROP1 /\ PROP2
           | PROP1 \/ PROP2
           | True
 *)

(* ################################################################# *)
(** * Tactics so far *)

(** We've seen:

    - intros
    - simpl
    - reflexivity
    - apply
    - split
    - left, right
    - rewrite
    - symmetry
    - apply

    Zounds! That's a lot. We'll meet even more of them tomorrow. It's
    a whole _other_ programming language...
*)

(* ################################################################# *)
(** * What's happening here? *)

(** You might be thinking, "What is this crap? I wanted to learn
    computer programming! Proof? Who cares! Coq and Gallina are for
    the birds."

    A few thoughts.

    1. This is a computer science department, not a computer
    programming department. You'll learn to program because it's a
    critical skill for computer science, but we're not in it just for
    the programming. (Similarly, astronomers learn to use cool
    telescopes, and you could hardly have modern astronomy without
    telescopes... but astronomy isn't just about telescopes.)

    2. If you could make your program _fast_ or _correct_, which would
    you choose?

    3. It is unlikely that your future career in computer science (or
    tech, or whatever) will involve proving programs correct. But
    anyone who _writes_ programs has to _reason_ about
    programs. Learning to prove properties of your programs stretches
    and strengthens your reasoning muscles.

    4. Computer science is a very formal field: to succeed as a
    computer scientist, you must be comfortable with formalism. This
    is practice! After Coq, you'll be ready for anything.
*)

(* 2021-10-04 14:37 *)
