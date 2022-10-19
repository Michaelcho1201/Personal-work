Require Export DMFP.Day15_induction2.

(* ################################################################# *)
(** * Inductive propositions *)

(** We've seen several ways of writing propositions, including
    conjunction, disjunction, and quantifiers.  In this chapter, we
    bring a new tool into the mix: _inductively defined propositions_.

    Inductive propositions are a powerful tool: they offer an
    alternative way of defining "evidence" of a proposition, while
    avoiding direct computation. Doing so lets us reason more
    directly, without reference to any particular implementation.

    In the early parts of the course, we defined many invariants:
    e.g., [natset]s that have no duplicates, or are sorted strictly
    ascending, or binary trees with the strict search
    invariant. Inductively defined propositions are perfect for this:
    we don't want to actually run code to check validity of our sets
    (it'd be slow!), but we do want to prove things about them! *)

(* ================================================================= *)
(** ** Evenness *)

(** Recall that we have seen two ways of stating that a number [n] is
    even: We can say (1) [evenb n = true], or (2) [exists k, n =
    double k].  Yet another possibility is to say that [n] is even if
    we can establish its evenness from the following rules:

       - Rule [ev_0]:  The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this definition of evenness works, let's
    imagine using it to show that [4] is even. By rule [ev_SS], it
    suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation:

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [ev], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
*)

(** Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears _unnamed_, to the _right_ of the colon, it is allowed
    to take different values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : (H : wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)

(** We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with primitive theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [ev] for particular numbers... *)

Theorem ev_4 : ev 4.
(* We want to prove 4 is even.  4 is even if 2 is even (by [ev_SS]),
   and 2 is even if 0 is even (by [ev_SS]), and 0 is even (by
   [ev_0]). *)
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** More generally, we can show that any number multiplied by 2 is even: *)

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
    ev (double n).
Proof.
  intros n. induction n as [| n' Hn].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply Hn.
Qed.
  (** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [ev]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and we
    are given [ev n] as a hypothesis.  We already know how to perform
    case analysis on [n] using the [inversion] tactic, generating
    separate subgoals for the case where [n = O] and the case where [n
    = S n'] for some [n'].  But for some proofs we may instead want to
    analyze the evidence that [ev n] _directly_.

    By the definition of [ev], there are two cases to consider:

    - If the evidence is of the form [ev_0], we know that [n = 0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n']. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** But the proof is straightforward using our inversion lemma. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' EQ].
  (* We are definitely in the [E = ev_SS n' E'] case now.  *)
  apply E'.
Qed.

(** We used an [as] pattern with [inversion] above, but it can be very
    hard to predict what variables and hypothesis [inversion] will
    produce. There's nothing wrong with running [inversion], seeing
    what gets produced, and then going back and naming it using [as].

    An alternative approach is to use some tactics to clean up your
    context.

    - The [subst] tactic tries to minimize the number of variables you
      have. To try to get rid of a particular variable, write [subst
      ...].

    - The [clear] tactic drops a variable or a hypothesis. But don't
      drop things you'll need!

    - The [rename ... into ...] tactic renames a variable.

    Here's an example:
  *)

Theorem evSS_ev'_subst : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E. subst n0. clear E. rename H0 into Hevn.
  apply Hevn.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (SSSSev__even)

    Prove the following result using [inversion]. *)
Theorem SSSSev__even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E.  apply evSS_ev' in H0. apply H0.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
    intros H. inversion H.  inversion H1. inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to reprove some theorems from day 12.
    (Here we are being a bit lazy by omitting the [as] clause from
    [inversion], thereby asking Coq to choose names for the variables
    and hypotheses that it introduces.) *)
Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  (* Let n, m, and o be given, and assume [[n; m] = [o; o]].

     We want to prove that [[n = m]].

     By inversion on our assumption, we know that [n = o] and [m = o].
     So we have [[o] = [o]] immediately.  *)
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in Day 14, we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma: *)

Lemma ev_even_firsttry : forall n,
    ev n -> exists k, n = double k.
Proof.
  (* WORKED IN CLASS *)

  (** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for [ev].  Indeed,
    the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
    
    (** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to an similar
    one that involves a _different_ piece of evidence for [ev]: [E'].
    More formally, we can finish our proof by showing that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

    (* However, at this point we can go no further. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've
    encountered similar problems early on, when trying to use case
    analysis to prove results that required induction.  And once again
    the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question. Just like for induction on ordinary
    data---naturals, lists, etc.---it takes some practice to predict
    what induction means for an inductive proposition. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds to
    [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
    ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in the case studies that follow, induction on
    evidence is a recurring technique across many areas. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H H'.  induction H as [| n1 H1 Hn].
  -destruct  H' as [| n2 H2].
   + simpl. apply ev_0.
   + simpl. apply ev_SS. apply H2.
  -destruct H' as [| n2 H2].
   + simpl. apply ev_SS. apply Hn.
   + simpl. apply ev_SS.  apply Hn.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev)

    Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H H'.   induction H' as [| n1 H1 Hn].
  -simpl in H. apply H.
  -simpl in H. apply evSS_ev in H. apply Hn in H. apply H.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
    ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
  numbers. *)

(** The following definition should be fairly intuitive.  It
  says that there are two ways to give evidence that one number is
  less than or equal to another: either observe that they are the
  same number, or give evidence that the first is less than or equal
  to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
| le_n (n : nat)                : le n n
| le_S (n m : nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
  [le_S] follow the same patterns as proofs about properties, like
  [ev] above. We can [apply] the constructors to prove [<=]
  goals (e.g., to show that [3<=3] or [3<=6]), and we can use
  tactics like [inversion] to extract information from [<=]
  hypotheses in the context (e.g., to prove that [(2 <= 1) ->
  2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
  although these are the same kind of simple "unit tests" as we gave
  for the testing functions we wrote in the first few lectures, we
  must construct their proofs explicitly -- [simpl] and
  [reflexivity] don't do the job, because the proofs aren't just a
  matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
  in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** Here's a heterogeneous relation, relating lists to numbers. What
    is it doing? *)

Inductive listnum {X : Type} : list X -> nat -> Prop :=
  | ln_nil : listnum [] 0
  | ln_cons (h : X) (t : list X) (n : nat) (H: listnum t n) : listnum (h::t) (S n).

(** Resist peeking at the next theorem... think about it! *)

Lemma listnum_iff : forall {X : Type} (l : list X) n,
    listnum l n <-> length l = n.
Proof.
  induction l as [| x l' IHl'].
  - intros. split.
    + intros. inversion H. subst n. reflexivity.
    + intros. subst n. apply ln_nil.
  - intros. split.
    + intros. inversion H. subst. rename n0 into n'.
      simpl. apply f_equal. apply IHl'. apply H3.
    + intros. simpl in H. destruct n as [| n'].
      * discriminate H.
      * apply ln_cons. apply IHl'. injection H as H. apply H.
Qed.

(** Here's a relation on arbitrary values and binary trees. What is it
    doing? *)

Inductive btx {X : Type} : X -> bt X -> Prop :=
  | bx_found (x : X) (l r : bt X)                        : btx x (node l x r)
  | bx_left  (x : X) (l r : bt X) (v : X) (Hl : btx x l) : btx x (node l v r)
  | bx_right (x : X) (l r : bt X) (v : X) (Hr : btx x r) : btx x (node l v r).

(** Don't peek! *)

Fixpoint nat_in_tree (n : nat) (t : bt nat) : bool :=
  match t with
  | empty => false
  | node l v r => eqb n v || nat_in_tree n l || nat_in_tree n r
  end.

Lemma btx__nat_in_tree : forall n t,
    btx n t <-> nat_in_tree n t = true.
Proof.
  intros n t. induction t as [| l IHl v r IHr].
  - split; intros H.
    + inversion H.
    + discriminate H.
  - simpl. rewrite orb_true_iff. rewrite orb_true_iff. split.
    + intros H. inversion H; subst.
      * left. left. symmetry. apply eqb_refl.
      * left. right. apply IHl. apply Hl.
      * right. apply IHr. apply Hr.
    + intros [[H | H] | H].
      * apply eqb_true_iff in H. subst n. apply bx_found.
      * apply bx_left. apply IHl. apply H.
      * apply bx_right. apply IHr. apply H.
Qed.

(** Last one. Here's a relation on DNA bases and binary trees. What is
    it doing? *)

Inductive btbase : base -> bt base -> Prop :=
  | bb_empty (b : base) : btbase b empty
  | bb_node  (b : base) (l : bt base) (v : base) (r : bt base) (Hne : v <> b) (Hl : btbase b l) (Hr : btbase b r) : btbase b (node l v r).

(* What's it do? *)

Fixpoint forallb_bt {X : Type} (f : X -> bool) (t : bt X) : bool :=
  match t with
  | empty => true
  | node l v r => f v && forallb_bt f l && forallb_bt f r
  end.

Lemma btbase__not_found : forall b t,
    btbase b t <-> forallb_bt (fun b' => negb (eq_base b b')) t = true.
Proof.
  intros b t. induction t as [| l IHl v r IHr].
  - split; intros H.
    + reflexivity.
    + apply bb_empty.
  - simpl. rewrite andb_true_iff. rewrite andb_true_iff. split.
    + intros H. inversion H; subst.
      split.
      * split.
        -- destruct (eq_base b v) eqn:E.
           ++ apply eq_base_iff in E. exfalso. apply Hne. symmetry. apply E.
           ++ reflexivity.
        -- apply IHl. apply Hl.
      * apply IHr. apply Hr.
    + intros [[Hbv Hl] Hr]. apply bb_node.
      * intros contra. subst v. rewrite eq_base_refl in Hbv. discriminate Hbv.
      * apply IHl. apply Hl.
      * apply IHr. apply Hr.
Qed.

(** **** Exercise: 3 stars, standard (sums_to)

    This question has two parts.

    1. Define an inductive relation [sums_to] that relates a [list nat] to its
       [sum], i.e.,

     sums_to [] 0

    and

     sums_to [10] 10

    and

     sums_to [1;2;3;4;5] 15

    should all be provable.

    2. Prove that [sums_to l (sum l)].
 *)
Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | n::l' => n + sum l'
  end.

Inductive sums_to : list nat -> nat -> Prop :=
| sums_to_nil               : sums_to [] 0
| sums_to_cons (h : nat) (t : list nat) ( n: nat)(H: sums_to t n) : (sums_to (h::t) (S n)).

Theorem Sums_to_proof: forall (n : nat) ( l : list nat),
    (sums_to l n) <-> sum l = n.
Proof.
    Admitted.
  (*
  intros.
  generalize dependent n.
  induction l.
  - split.
    intros H. inversion H. simpl. reflexivity.
    intros H. simpl in H. rewrite <- H. apply sums_to_nil.
  - split.
    intros H. destruct H.
    + simpl. reflexivity.
    + inversion H. rewrite <- H1 in H. rewrite <- H0 in H.
    *)
  
  
(* Do not modify the following line: *)
Definition manual_grade_for_sums_to : option (nat*string) := None.
(** [] *)

Module R.

  (** We can define three-place relations, four-place relations, etc.,
      in just the same way as binary relations.  For example, consider
      the following three-place relation on numbers: *)

  Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

  (** **** Exercise: 3 stars, standard (R_fact) *)
  (** The relation [R] above actually encodes a familiar function.
      Figure out which function; then state and prove this equivalence
      in Coq? *)

  Definition fR : nat -> nat -> nat := plus.

  Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
  Proof.
    (*unfold fR.
    split.
    -intros h. induction h.
     + simpl. reflexivity.
     + Search plus. rewrite plus_Sn_m. rewrite IHh. reflexivity.
     + Search plus. rewrite <- plus_n_Sm. rewrite IHh. reflexivity.
     + inversion IHh. rewrite <-plus_n_Sm in H0. inversion H0. reflexivity.
     + rewrite <-IHh. apply plus_comm.
    - intros h. induction o.
      + induction m .
       * simpl in h. rewrite h. apply c1.
       * rewrite plus_Sn_m in h. inversion h.
      +  destruct  m eqn: Em.
         * simpl in h. rewrite h. apply c3. apply c4. *)Admitted.
      
  (* Do not modify the following line: *)
Definition manual_grade_for_R_fact : option (nat*string) := None.
  (** [] *)

End R.

(* 2021-10-04 14:37 *)
