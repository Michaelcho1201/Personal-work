Require Export DMFP.Day11_propositions.

(** Today is a long day: we're going to teach you several tactics and
    proof methods. There are a few more exercises than usual, too. So:
    please start early and ask for help if you need it! *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this.  For example, our earlier
    proof of the [mult_0_plus] theorem referred to a previous theorem
    named [plus_O_n].  We could instead use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a Definition
    so that we can manipulate its right-hand side. We've already met
    the [unfold] tactic when talking about [not], but it's generally
    useful. For example, if we define... *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m,
    (forall n m o, n * (m * o) = (n * m) * o) -> (* we'll prove this later *)
    (forall n m, n * m = m * n) ->               (* same *)
    square (n * m) = square n * square m.
Proof.
  intros n m mult_assoc mult_comm.
  simpl.

(** ... we get stuck: [simpl] doesn't simplify anything at this point,
    and since we haven't proved any other facts about [square], there
    is nothing we can [apply] or [rewrite] with.

    To make progress, we can manually [unfold] the definition of
    [square]: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these facts it is not
    hard to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  eqb (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(** The reason for this is that the definitions of both
    [eqb] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [eqb] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [eqb (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [eqb (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  eqb (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    It's worth contrasting intro patterns with _match patterns_, i.e.,
    what we write in [match] expressions. A match pattern in a branch
    of a [match] expression names each constructor and its arguments,
    with a [|] before each one, e.g.:

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

    In contrast, an intro pattern names only the arguments of each
    constructor, leaving out the constructor name itself, as in:

   destruct n as [| n'].

    You can nest patterns, e.g., to do case analysis on [n] and [n']
    simultaneously, write:

   destruct n as [| [| n']].

    There will be three subgoals: [n = O], [n = S O], and [n = S (S
    n')].
 *)

(** When doing case analysis with [destruct], in each subgoal, Coq
    remembers the assumption about [n] that is relevant for this
    subgoal -- either [n = 0] or [n = S n'] for some n'.  The [eqn:E]
    annotation tells [destruct] to give the name [E] to this equation.
    Leaving off the [eqn:E] annotation causes Coq to elide these
    assumptions in the subgoals.  This slightly streamlines proofs
    where the assumptions are not explicitly used, but it is better
    practice to keep them for the sake of documentation, as they can
    help keep you oriented when working with the subgoals.  *)

(** The [-] signs on the second and third lines are called
    _bullets_, and they mark the parts of the proof that correspond to
    each generated subgoal.  The proof script that comes after a
    bullet is the entire proof for a subgoal.  In this example, each
    of the subgoals is easily proved by a single use of [reflexivity],
    which itself performs some simplification -- e.g., the first one
    simplifies [eqb (S n' + 1) 0] to [false] by first rewriting [(S n'
    + 1)] to [S (n' + 1)], then unfolding [eqb], and then simplifying
    the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse.
- _Theorem_: For any natural number [n],

      eqb (n + 1) 0 = false.

    _Proof_: Let [n] be given ([intros n]).
    We go by cases on [n] ([destruct n as [| n']]):

      - First, suppose [n=0]. We must show that [eqb (0 + 1) 0 = false], which we have by
        definition ([reflexivity]).
      - Next, suppose [n=S n']. We must show that [eqb ((S n') + 1) 0 = false], which holds
        by the definition of [eqb] ([reflexivity]).

    _Qed_.

    Notice how the [destruct] lines up with what we say in the
    paper proof. We open with announcing our intention---to do case
    analysis on [n]. While Coq wants to know the names of any possible
    subparts of [n] up front, in the _[as] pattern_ of the destruct;
    in the paper proof, we find out the names when we write out which
    case we're in explicitly: each subcase is written as its own
    bullet, where we announce the case we're in.

    We've encounted our first significant divergence (of many!)
    between how Coq and paper proofs work. Coq keeps track of the
    context for you, so Coq proof scripts can leave quite a bit
    implicit. Paper proofs are meant to communicate an idea from one
    human to another, so it's important to check in and make sure
    everyone is on the same page---by, for example, saying what each
    case is up front.

    Finally, note that we're not "transliterating" the Coq: the two
    uses of reflexivity in each branch are written slightly
    differently in the paper proof.
 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [ | ]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices. In a paper proof, it'd be good to announce that [b=false]
    in the first case and [b=true] in the second case.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)

Print complement. (* Just to remind you. *)

Lemma complement_involutive : forall (b : base),
    complement (complement b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct c]
    line right above it. *)

(** Besides [-] and [+], we can use [*] (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals: *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(** As you may have noticed, many proofs perform case analysis on a variable
    right after introducing it:

       intros x y. destruct y as [|y].

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem above. *)

Theorem plus_1_neq_0' : forall n : nat,
  eqb (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** **** Exercise: 1 star, standard (minus_n_O) *)
Lemma minus_n_O : forall n : nat, n = n - 0.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.
(** [] *)

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (andb_true_elim2)

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c h. destruct c eqn :Ec.
  - destruct b eqn: Eb.
    + apply h.
    + reflexivity.
  - destruct b eqn: Eb.
    + apply h.
    + apply h.
Qed.
(** [] *)

(** At this point, a deeper discussion of unfolding and simplification
    is in order.

    You may already have observed that tactics like [simpl],
    [reflexivity], and [apply] will often unfold the definitions of
    functions automatically when this allows them to make progress.  For
    example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** then the [simpl] in the following proof (or the [reflexivity], if
    we omit the [simpl]) will unfold [foo m] to [(fun x => 5) m] and
    then further simplify this expression to just [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** However, this automatic unfolding is rather conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  (It is not smart enough to notice that the
    two branches of the [match] are identical.)  So it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that, itself, cannot be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(** At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** A more straightforward way to make progress is to explicitly tell
    Coq to unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

  (** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking too hard. *)

  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(** Finally, it's often useful to do the [unfold]/[fold] 1-2 punch:
    [unfold]ing a recursive definition and then immediately [fold]ing
    it back up will reveal the work one step of recursion is doing
    without doing any simplification. *)

Fixpoint funny_rec (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => if evenb n then 0 else funny_rec n'
  end.

(** **** Exercise: 2 stars, standard (funny_rec_evenb_0)

    In the [n = S n'] case, notice that [simpl] gives you an annoying
    answer, but [unfold]/[fold] works a treat. *)
Lemma funny_rec_evenb_0 : forall n,
    evenb n = true ->
    funny_rec n = 0.
Proof.
  intros n H.
  unfold funny_rec.
  destruct n.
  - reflexivity.
  - rewrite -> H. reflexivity.
Qed.
(** [] *)

(** We can formalize this trick in a new tactic (yet another
    programming language inside of Coq!).  Now, we can say [step
    funny_rec] to go through one level of its recursion.

    [step] here does the work of [unfold] followed by [fold].
    The notations defined below mean we can also use [step] on hypotheses.
 *)

Ltac step_goal A := unfold A; fold A.
Ltac step_in A H := unfold A in H; fold A in H.
Tactic Notation "step" constr(A) := step_goal A.
Tactic Notation "step" constr(A) "in" hyp(H) := step_in A H.

(* ################################################################# *)
(** * Logical Connectives *)

(** Now that we've seen [destruct], we can do more with logical
    connectives. So far we've only _proved_ conjunctions and
    disjunctions. How do you use them? And what about negation? *)

(* ================================================================= *)
(** ** Conjunction *)

(** We've seen that proving a conjunction means using [split] to prove
    each part. To go in the other direction -- i.e., to _use_ a
    conjunctive hypothesis to help prove something else -- we employ
    the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form [A /\
    B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true. *)

(** The following lemmas not only show the general idea, but they're
    generally useful: it's a common situation to know [A /\ B] but
    only really need just [A] (or just [B]). *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ]. (* "Let P and Q be given, and assume P /\ Q." *)
  apply HP. (* "We have to show P; but we've just assumed P, so we're done." *)
Qed.

(** **** Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions.  The following
    commutativity and associativity theorems are handy in such
    cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(** **** Exercise: 2 stars, standard (and_assoc)

    (In the following proof of associativity, notice how the _nested_
    intro pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP. 
    + apply HQ.
  - apply HR.
Qed.
(** [] *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* "Let [n] and [m] be given, and assume [n = 0] and [m = 0].  We
     need to show [n + m = 0] " *)
  intros n m [Hn Hm].
  (* Since n is 0 and m is 0, showing [n + m = 0] means showing [0 + 0
     = 0], .... *)
  rewrite Hn. rewrite Hm.
  (* ... which is immediate by the definition of [plus]. *)
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this theorem, both formulations are fine.  But it's
    important to understand how to work with conjunctive hypotheses
    because conjunctions often arise from intermediate steps in
    proofs, especially in bigger developments. We'll see an example on
    day 12. *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    (Alternatively, we can write [or A B], where [or : Prop -> Prop ->
    Prop].)

    Recall that we used [left] and [right] to choose which branch of
    disjunction to prove. Just as for conjunction, we use [destruct]
    to ask: if we know [P \/ Q], which one holds?  *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP | HQ].
  - (* left *) right. apply HP.
  - (* right *) left. apply HQ.  Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - (* left *) right. apply HP.
  - (* right *) left. apply HQ.  Qed.

(** ... and a slightly more interesting example requiring both [left]
    and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* ================================================================= *)
(** ** Falsehood and Negation

    So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. In Coq, such negative statements are expressed with the
    negation operator [~]. *)

(** To see how negation works, recall the discussion of the _principle
    of explosion_ from the [Tactics] chapter; it asserts that, if
    we assume a contradiction, then any other proposition can be
    derived.  Following this intuition, we could define [~ P] ("not
    [P]") as [forall Q, P -> Q].  Coq actually makes a slightly
    different choice, defining [~ P] as [P -> False], where [False] is
    a specific contradictory proposition defined in the standard
    library. *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** PROP ::= EXPR1 = EXPR2
           | forall x : TYPE, PROP
           | PROP1 -> PROP2
           | PROP1 /\ PROP2
           | PROP1 \/ PROP2
           | True
           | ~ PROP
           | False
 *)

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] on it to complete
    any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

Theorem not_False :
  ~ False.
Proof.
  (* We must show [~ False].  Towards a contradiction, assume [False].  *)
  unfold not. intros H.
  (* But we've already assumed something impossible---that [False]
    holds!  By the principle of explosion, the original claim of [~
    False] must be true. *)
  destruct H. (* Or... [apply H]! *)
Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not)

    (Optionally) show that Coq's definition of negation implies the
    intuitive one mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up.
*)

(** Especially as you're getting used to our notion of negation, using
    the [unfold] tactic is helpful: it will turn a negation into an
    implication. (You can use [unfold] and its partner, [fold], on any
    [Definition] or [Fixpoint], not just [not]!) *)

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

(** **** Exercise: 2 stars, standard (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros HQ HP.
  apply HQ.
  apply H.
  apply HP.
Qed.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 2 stars, standard, optional (boolean_functions)

    Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  destruct b  eqn : Eb.
  - rewrite x. rewrite x. reflexivity.
  - rewrite x. rewrite x. reflexivity.
Qed.

(** Now state and prove a theorem in Coq; call it
    [negation_fn_applied_twice]. It should be similar to the previous
    one but where the second hypothesis says that the function [f] has
    the property that [f x = negb x].

    Just like for definitions, the autograder will reject your program
    if you don't define this theorem at the correct type! If you're
    having trouble, talk to Prof. or a TA.  *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  unfold negb.
  intros f x b.
  destruct b  eqn : Eb.
  - rewrite x. rewrite x. reflexivity.
  - rewrite x. rewrite x. reflexivity.
Qed.
(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O
       | S (n : nat).

    This definition asserts that every number has one of two forms:
    either it is the constructor [O] or it is built by applying the
    constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition are two more facts:

    - The constructor [S] is _injective_, or _one-to-one_.  That is,
      if [S n = S m], it must be that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since [true] and
    [false] take no arguments, their injectivity is neither here
    nor there.)  And so on. *)

(** For example, we can prove the injectivity of [S] by using the
    [pred] function defined in [Basics.v]. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  (* Our use of [assert] here 'captures' [n]: we're proving this just
     for the [n] we have, not for all [n] (though it's true for all
     [n]). *)
  assert (H2: n = pred (S n)). { reflexivity. }
  (* For "obvious" properties like this, we might prefer to write
     [assert (H2: n = pred (S n)) by reflexivity.], avoiding the
     nested proof. *)
  rewrite H2. rewrite H1. reflexivity.
Qed.

(** This technique can be generalized to any constructor by
    writing the equivalent of [pred] -- i.e., writing a function that
    "undoes" one application of the constructor. As a more convenient
    alternative, Coq provides a tactic called [injection] that allows
    us to exploit the injectivity of any constructor.  Here is an
    alternate proof of the above theorem using [injection]: *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
(** By writing [injection H as Hmn] at this point, we are asking Coq
    to generate all equations that it can infer from [H] using the
    injectivity of constructors (in the present example, the equation
    [n = m]). Each such equation is added as a hypothesis (with the
    name [Hmn] in this case) into the context. *)
  injection H as Hnm. apply Hnm.
Qed.

(** Here's a more interesting example that shows how [injection] can
    derive multiple equations at once. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(** Alternatively, if you just say [injection H] with no [as] clause,
    then all the equations will be turned into hypotheses at the
    beginning of the goal. *)

Theorem injection_ex2 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  (* Let n, m, and o be given; assume [[n;m] = [o;o]]. *)
  intros n m o H.
  (* By this assumption and the injectivity of [cons], n must be o and
  m must also be o. *)
  injection H.
  (* WORKED IN CLASS *)
  intros H1 H2. rewrite H1. rewrite H2.
  (* So [[n] = [m]] is just [[o]=[o]], which is immediate. *)
  reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H Hj.
  injection H.
  rewrite Hj.
  intros H1 H2.
  injection H1.
  intros H3.
  rewrite H2.
  rewrite H3.
  reflexivity.
Qed.
(** [] *)

(** So much for injectivity of constructors.  What about disjointness?

    The principle of disjointness says that two terms beginning with
    different constructors (like [O] and [S], or [true] and [false])
    can never be equal.  This means that, any time we find ourselves
    in a context where we've _assumed_ that two such terms are equal,
    we are justified in concluding anything we want, since the
    assumption is nonsensical. *)

(** The [discriminate] tactic embodies this principle: It is used on a
    hypothesis involving an equality between different
    constructors (e.g., [S n = O]), and it solves the current goal
    immediately.  Here is an example: *)

Theorem eqb_0_l : forall n,
   eqb 0 n = true -> n = 0.
Proof.
  intros n.

(** We can proceed by case analysis on [n]. The first case is
    trivial. *)

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(** However, the second one doesn't look so simple: assuming [eqb 0
    (S n') = true], we must show [S n' = 0]!  The way forward is to
    observe that the assumption itself is nonsensical: *)

  - (* n = S n' *)
    simpl.

(** If we use [discriminate] on this hypothesis, Coq confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. *)

    intros H. discriminate H.
Qed.

(** The [discriminate] tactic is an instance of the logical principle
    we met earlier: the _principle of explosion_. *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  (* Let n be given, and assume [S n = 0]. *)
  intros n contra.
  (* But by the disjointness of the constructors for [nat], this is
  impossible---[S] of anything can't possibly be [O].  So we have a
  contradition. *)
  discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are _not_ showing that the conclusion of the
    statement holds.  Rather, they are showing that, _if_ the
    nonsensical situation described by the premise did somehow arise,
    _then_ the nonsensical conclusion would also follow, because we'd
    be living in an inconsistent universe where every statement is
    true.  We'll explore the principle of explosion in more detail in
    the next chapter, [Logic]. *)

(** **** Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.
(** [] *)



(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  (** The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)], that is [not (0 = 1)], which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here
      to illustrate that point, but generally it can be omitted.) *)

  unfold not.

  (** To prove an inequality, we may assume the opposite
      equality... *)

  intros contra.

  (** ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)

  discriminate contra.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. discriminate H.
Qed.

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  (* Let b be given, and assume [b <> true]. Observe that b is either true or false. *)
  intros b H. destruct b.
  - (* b = true *)
    (* If b is true, we must show [b = false]. But we've already
    assumed [b <> true], so this case will never arise. *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    (* If b is false, we have our goal of [b = false] immediately. *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)

    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

(** **** Exercise: 1 star, standard, optional (not_both_true_and_false)

    Some (optional!) practice with logical connectives. *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" a/k/a iff connective, which asserts
    that two propositions have the same truth value, is just the
    conjunction of two implications. *)

(** PROP ::= EXPR1 = EXPR2
           | forall x : TYPE, PROP
           | PROP1 -> PROP2
           | PROP1 /\ PROP2
           | PROP1 \/ PROP2
           | True
           | ~ PROP
           | False
           | PROP1 <-> PROP2
 *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we
    imported a "Setoid" Coq library on Day11. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences... *)

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* We proceed by cases on b1. *)
  intros [].
  - (* Assuming [b1 = true], we must show [true || b2 = true <-> true = true \/ b2 = true]. *)
    (* By the definition of [orb], this is the same as showing [true = true <-> true = true \/ b2 = true]. *)
    simpl. intros b2.
    (* We will prove each direction of the biconditional. *)
    split.
    + (* Assume [true = true].  We must show [true = true \/ b2 = true], and the left disjunct is immediate from our assumption. *)
      intros _. left. reflexivity.
    + (* Now assume [true = true \/ b2 = true]. We must show [true = true]; but this is immediate anyhow. *)
      intros _. reflexivity.
  - (* Assuming [b1 = false], we must show [false || b2 = true <-> false = true \/ b2 = true].  By the definition of [orb] this is the same as showing [b2 = true <-> false = true \/ b2 = true]. *)
    simpl. intros []. (* We go by cases on b2. *)
    + (* If b2 is true, we must show [true = true <-> false = true \/ true = true].  We prove each direction separately. *)
      split.
      * (* Assuming [true = true], we must show [false = true \/ true = true].  The right hand of the disjunction is immediate. *)
        intros _. right. reflexivity.
      * (* Assuming [false = true \/ true = true], we must show [true = true], but that's immediate. *)
        intros _. reflexivity.
    + (* If b2 is false, we must show [false = true <-> false = true \/ false = true]. *)
      (* We prove each direction separately. *)
      split.
      * (* Assuming [false = true], we must show [false = true \/ false = true].  But we've just assumed that [false = true], which is a contradiction by the disjointness of the constructors of bool. *)
        intros H. discriminate H.
      * (* Now assume [false = true \/ false = true].  In either case we must prove [false = true], which is immediate by the (contradictory) assumption. *)
        intros [H | H].
        { apply H. }
        { apply H. }
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the [orb_true_iff] result: *)

Lemma orb_true_3 :
  forall a b c : bool, a || b || c = true <-> a = true \/ b = true \/ c = true.
Proof.
  intros n m p.
  rewrite orb_true_iff. rewrite orb_true_iff. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall a b : bool, a || b = true -> a = true \/ b = true.
Proof.
  intros n m H. apply orb_true_iff. apply H.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** It's common to use iff to relate functions to propositions---like
    we already saw for [orb_true_iff]. Here we relate the [eq_base]
    function to the [=] proposition. All of these are good practice,
    but we leave them optional. *)

(** **** Exercise: 1 star, standard, optional (eq_base_refl) *)
Lemma eq_base_refl : forall (b : base),
    eq_base b b = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eq_base_true) *)
Lemma eq_base_true : forall (b1 b2 : base),
    eq_base b1 b2 = true -> b1 = b2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (eq_base_iff)

    Prove a theorem characterizing equality on DNA bases.

    Proofs relating equality predicates (i.e., functions) to the
    equality proposition tend to take this form: one direction is
    simply reflexivity (if [b1 = b2], then you need only show that
    [eq_blah b1 b1 = true]) and the other is more involved (if
    [eq_blah b1 b2 = true], then [b1 = b2] for real).  *)
Lemma eq_base_iff : forall (b1 b2 : base),
    eq_base b1 b2 = true <-> b1 = b2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (not_P__P_true)

    This lemma is particularly useful for when we have computational
    characterizations of interesting properties. *)
Lemma not_P__P_true : forall P b,
    b = true <-> P ->
    b = false <-> ~P.
Proof.
  intros P b H.
  split.
  - rewrite <-H. intros H1. rewrite H1. apply not_true_iff_false. reflexivity.
  - destruct b eqn: bc.
    + rewrite <-H. intros H1.  apply not_true_iff_false. apply H1.
    + rewrite <-H. intros H1.  apply not_true_iff_false. apply H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (andb_true_iff)

    The following lemma relates the conjunction to the corresponding
    boolean operations. *)
Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, many tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     eqb (S n) (S m) = b  ->
     eqb n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, [apply L in H] matches some conditional statement
    [L] (of the form [L1 -> L2], say) against a hypothesis [H] in the
    context.  However, unlike ordinary [apply] (which rewrites a goal
    matching [L2] into a subgoal [L1]), [apply L in H] matches [H]
    against [L1] and, if successful, replaces it with [L2].

    In other words, [apply L in H] gives us a form of "forward
    reasoning": from [L1 -> L2] and a hypothesis matching [L1], it
    produces a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning": it says that if we know [L1->L2] and we are
    trying to prove [L2], it suffices to prove [L1].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (eqb n 5 = true -> eqb (S (S n)) 7 = true) ->
  true = eqb n 5  ->
  true = eqb (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math
    class), they probably used forward reasoning. They might have even
    told you that backward reasoning was wrong or not allowed! In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about. *)


(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if eqb n 3 then false
  else if eqb n 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (eqb n 3).
  - (* eqb n 3 = true *) reflexivity.
  - (* eqb n 3 = false *) destruct (eqb n 5).
    + (* eqb n 5 = true *) reflexivity.
    + (* eqb n 5 = false *) reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (eqb n 3) then ... else ...].  But either [n]
    is equal to [3] or it isn't, so we can use [destruct (eqb n 3)] to
    let us reason about the two cases.

    Informally, we might read the proof above like so:

    We want to show that for any number n, [sillyfun n = false].  Let
    a number [n] be given.  Observe that [sillyfun] is defined so that
    when [eqb n 3 = true] the result is false, when [eqb n 5 = true]
    the result is false, and if both are false then the result is
    [false].  We handle each case in turn.

    First, suppose that [eqb n 3 = true].  Then we hit the first
    branch of [sillyfun] and return false, and [false = false] is
    immediate.

    Second, suppose that [eqb n 5 = true].  Then we hit the second
    branch of [sillyfun] and likewise return false.

    Finally, suppose that neither of those cases hold.  Then
    [sillyfun] also returns false and the same reasoning holds. *)

(** In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(** More practically, we can use these case analyses to reason about
    the complex decisions made in programs.  As a rule of thumb, you
    will need this trick whenever you are stuck on a [match] or an
    [if] which depends on the result of some function call rather than
    some ready-to-hand value.

    Here's a function that computes the minimum of three
    arguments. First, let's make sure we have a good [leb] defined. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition min3 (n1 n2 n3 : nat) : nat :=
  if leb n1 n2
  then if leb n1 n3
       then n1
       else n3
  else if leb n2 n3
       then n2
       else n3.

Definition argmin3 {A:Type} (cost : A -> nat) (o1 o2 o3 : A) : A :=
  let c1 := cost o1 in
  let c2 := cost o2 in
  let c3 := cost o3 in
  if leb c1 c2
  then if leb c1 c3
       then o1
       else o3
  else if leb c2 c3
       then o2
       else o3.

(** **** Exercise: 2 stars, standard (argmin3_min3_eqs)

    Relate [min3] to [argmin3]. Your proof will need to navigate why
    [argmin3] should go one direction or another by using [destruct]
    with a compound term relevant to the decision-making process of
    [arg3min]. *)
Lemma argmin3_min3_eqs : forall {A:Type} (cost : A -> nat) (o1 o2 o3 : A) (n1 n2 n3 : nat),
    cost o1 = n1 ->
    cost o2 = n2 ->
    cost o3 = n3 ->
    cost (argmin3 cost o1 o2 o3) = min3 n1 n2 n3.
Proof.
  intros A cost o1 o2 o3 n1 n2 n3 H1 H2 H3.
  unfold argmin3.
  unfold min3.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  destruct( leb n1 n2).
  -destruct (leb n1 n3).
   + apply H1.
   + apply H3.
  -destruct (leb n2 n3).
   + apply H2.
   + apply H3.
Qed.


(** To prove this one, you should be able to just use [argmin3_min3_eqs]. *)
Corollary argmin3_min3 : forall {A:Type} (cost : A -> nat) (o1 o2 o3 : A),
    cost (argmin3 cost o1 o2 o3) = min3 (cost o1) (cost o2) (cost o3).
Proof.
  intros A cost o1 o2 o3. apply argmin3_min3_eqs.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(** [] *)

(** However, [destruct]ing compound expressions requires a bit of
    care, as such [destruct]s can sometimes erase information we need
    to complete a proof.

    For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if eqb n 3 then true
  else if eqb n 5 then true
       else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  By analogy with the proofs we did with [sillyfun] above, it
    is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
    (forall n m, eqb n m = true -> n = m) ->
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n eqb_true eq. unfold sillyfun1 in eq.
  destruct (eqb n 3).
  (* stuck... *)
Abort.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution performed by [destruct] is too brutal -- it threw
    away every occurrence of [eqb n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that, since [eqb n 3 = true] in this
    branch of the case analysis, it must be that [n = 3], from which
    it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [eqb n 3], but at the same time add an equation to
    the context that records which case we are in.  Recall that the
    [eqn:] qualifier allows us to introduce such an equation, giving
    it a name that we choose. *)

Theorem sillyfun1_odd : forall (n : nat),
    (forall n m, eqb n m = true -> n = m) ->
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  (* Let n be given, and assume that for all n and m, if [eqb n m =
  true] then [n = m].  Also assume [sillyfun1 n = true].  *)
  intros n eqb_true eq. unfold sillyfun1 in eq.
  (* "Observe that [eqb n 3] is either true or false." *)
  destruct (eqb n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra equality
     assumption, which is exactly what we need to make progress. *)
  - (* e3 = true *) apply eqb_true in Heqe3.
    (* If it is true, then we know that [n = 3] by our earlier assumption. *)
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
    (* Otherwise, [eqb n 5] is also either true or false. *)
    (* When we come to the second equality test in the body of
       the function we are reasoning about, we can use [eqn:] again in
       the same way, allow us to finish the proof. *)
    destruct (eqb n 5) eqn:Heqe5.
    + (* e5 = true *)
      (* If it is true, then we know [n = 5]. *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + (* e5 = false *)
      (* If [n] is neither 3 nor 5, [sillyfun1] could not possibly
         have returned true, so we have a contradiction in our
         assumptions. *)
      discriminate eq.  Qed.

(* 2021-10-04 14:37 *)
