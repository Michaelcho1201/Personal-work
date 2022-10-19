Require Export DMFP.Day14_exists.

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose
    we want to show that the [double] function is injective -- i.e.,
    that it maps different arguments to different results:

    Theorem double_injective: forall n m,
      double n = double m -> n = m.

    The way we _start_ this proof is a bit delicate: if we begin with

      intros n. induction n.

    all is well.  But if we begin it with

      intros n m. induction n.

    we get stuck in the middle of the inductive case...

    The strategy of doing fewer [intros] before an [induction]
    to obtain a more general IH doesn't always work by itself;
    sometimes some _rearrangement_ of quantified variables is needed.
    Suppose, for example, that we wanted to prove [double_injective]
    by induction on [m] instead of [n]. *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m eq. induction n as [| n'].
  - (* n = O *) destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) simpl in eq. discriminate eq.
  - (* n = S n' *) destruct m as [| m'].
    + (* m = O *) simpl in eq. discriminate eq.
    + (* m = S m' *) simpl in eq. injection eq as eq'.

(** At this point, the induction hypothesis, [IHn'], does _not_ give us
    [n' = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)

      Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context --
    intuitively, we have told Coq, "Let's consider some particular [n]
    and [m]..." and we now have to prove that, if [double n = double
    m] for _these particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove, for
    _all_ [n], that the proposition

      - [P n] = "if [double n = double m], then [n = m]"

    holds, by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help at all with proving
    [R]!  (If we tried to prove [R] from [Q], we would start with
    something like "Suppose [double (S n) = 10]..." but then we'd be
    stuck: knowing that [double (S n)] is [10] tells us nothing about
    whether [double n] is [10], so [Q] is useless.) *)

(** Trying to carry out this proof by induction on [n] when [m] is
    already in the context doesn't work because we are then trying to
    prove a relation involving _every_ [n] but just a _single_ [m]. *)

(** The successful proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) intros m eq. simpl in eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.

(** Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for _every_ [m]), but the IH
    is correspondingly more flexible, allowing us to choose any [m] we
    like when we apply the IH. *)

    intros m eq.

(** Now we've chosen a particular [m] and introduced the assumption
    that [double n = double m].  Since we are doing a case analysis on
    [n], we also need a case analysis on [m] to keep the two "in sync." *)

    destruct m as [| m'].
    + (* m = O *) simpl.

(** The 0 case is trivial: *)

      discriminate eq.

    + (* m = S m' *)

(** At this point, since we are in the second branch of the [destruct
    m], the [m'] mentioned in the context is the predecessor of the
    [m] we started out talking about.  Since we are also in the [S]
    branch of the induction, this is perfect: if we instantiate the
    generic [m] in the IH with the current [m'] (this instantiation is
    performed automatically by the [apply] in the next step), then
    [IHn'] gives us exactly what we need to finish the proof. *)

      
      injection eq as goal. apply IHn' in goal. rewrite goal. reflexivity. Qed.

(** What you should take away from all this is that we need to be
    careful about using induction to try to prove something too
    specific: To prove a property of [n] and [m] by induction on [n],
    it is sometimes important to leave [m] generic.

    In an informal proof, you should simply be careful about what is
    given and what isn't. If you're _deliberately_ delaying
    introducing a variable, it's good to be explicit. For example, in
    an informal analogue of the above, we might say, "by induction on
    [n], leaving [m] general". *)

(** A brief pause, for a theorem that'll come in handy. The
    injectivity of constructors allows us to reason that [forall (n m
    : nat), S n = S m -> n = m].  The converse of this implication is
    an instance of a more general fact about both constructors and
    functions, which we will find convenient in a few places below: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(** The following exercise requires the same pattern. *)

(** **** Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m,
    eqb n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  -intros m eq. simpl in eq. destruct m as [| m'].
   +reflexivity.
   +discriminate eq.
  -simpl.
   intros m eq.
   destruct m as [| m'].
   +discriminate eq.
   +simpl. apply IHn' in eq.   rewrite eq. reflexivity.
Qed.
(** [] *)

(** Having proved [eqb_true], we can use [eqb_refl] to show that [eqb]
    computes equality. *)

Theorem eqb_true_iff : forall n1 n2 : nat,
  eqb n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(** **** Exercise: 1 star, standard, optional (eqb_false_iff)

    The following theorem is an alternate "negative" formulation of
    [eqb_true_iff] that is more convenient in certain situations
    (we'll see examples in later chapters). Hint: look at
    [not_P__P_true]. *)
Theorem eqb_false_iff : forall x y : nat,
  eqb x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** When to Vary *)

(** To better understand general IHs, let's look back to
    [plus_n_Sm]. *)

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* WORKED IN CLASS *)
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Both [eqb_true] and [plus_n_Sm] are functions involving two
    variables and equality, so why does the former need a general
    hypothesis and not the latter?

    The general rule is that you need a general IH when:

    - There is more than one variable.

    - Variables other than the IH will have different values in
      different cases.

    The problem with general rules is that they are, well, general. We
    can be more specific about when you'll need a general IH:

    - When more than one variable changes during recursion in one of
      your definitions.

    That's very specific! Let's look.
*)

Print eqb. (* both [n] and [m] change *)
Print Nat.add. (* only [n] changes *)

(** The only problem with the more specific explanation is that it's,
    well, clearly not right! Looking back at [double_injective], our
    definition of [double] only has one argument, but we needed to
    vary our hypothesis! What gives? *)

Print double.

Check double_injective.
(* double_injective
     : forall n m : nat, double n = double m -> n = m
*)

(** Look closely at [eqb_true_iff]. We could have equivalently stated
    [double_injecive] as:

Theorem double_injective_eqb
     : forall n m : nat, eqb (double n) (double m) = true -> eqb n m = true.

    A proof that [n = m] on [nat]s [n] and [m] is low key also about [eqb].

    But then why _don't_ we need for [plus_n_Sm], which is also about
    equality on numbers?

Theorem plus_n_Sm : forall n m : nat,
  eqb (S (n + m)) (n + (S m)) = true.

    While it's true that both _sides_ of [eqb] change here, a change
    in [n] without a change in [m] is enough for [eqb] to make a
    recursive call. So: only one variable changes during recursion!
*)

(** Whew: that was a lot. There's another, more practical, way to
    figure out when you need to generalize your IH: you get to the
    inductive case and the IH and your goal are 'incompatible' because
    your IH is about a specific variable. *)

(** **** Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall (n m : nat),
    eqb n m = eqb m n.
Proof.
  intros n. induction n as [| n' IHn'].
  -intros m. destruct m as [| m'].
   +reflexivity.
   +simpl. reflexivity.
  -intros m. destruct m as [| m'].
   +simpl. reflexivity.
   +apply IHn'.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (eqb_trans) *)
Theorem eqb_trans : forall n m p,
    eqb n m = true ->
    eqb m p = true ->
    eqb n p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Generalizing the IH Explicitly *)

(** The strategy of doing fewer [intros] before an [induction] to
    obtain a more general IH doesn't always work by itself; sometimes
    some _rearrangement_ of quantified variables is needed.  Suppose,
    for example, that we wanted to prove [double_injective] by
    induction on [m] instead of [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce [n]
    for us!)  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. *)

(** What we can do instead is to first introduce all the quantified
    variables and then _re-generalize_ one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The [generalize dependent]
    tactic does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) discriminate eq.
    + (* n = S n' *) simpl. apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    _Theorem_: For any nats [n] and [m], if [double n = double m], then
      [n = m].

    _Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
      any [n], if [double n = double m] then [n = m].

      - First, suppose [m = 0], and suppose [n] is a number such
        that [double n = double m].  We must show that [n = 0].

        Since [m = 0], by the definition of [double] we have [double n =
        0].  There are two cases to consider for [n].  If [n = 0] we are
        done, since [m = 0 = n], as required.  Otherwise, if [n = S n']
        for some [n'], we derive a contradiction: by the definition of
        [double], we can calculate [double n = S (S (double n'))], but
        this contradicts the assumption that [double n = 0].

      - Second, suppose [m = S m'] and that [n] is again a number such
        that [double n = double m].  We must show that [n = S m'], with
        the induction hypothesis that for every number [s], if [double s =
        double m'] then [s = m'].

        By the fact that [m = S m'] and the definition of [double], we
        have [double n = S (S (double m'))].  There are two cases to
        consider for [n].

        If [n = 0], then by definition [double n = 0], a contradiction.

        Thus, we may assume that [n = S n'] for some [n'], and again by
        the definition of [double] we have [S (S (double n')) =
        S (S (double m'))], which implies injectivity of constructors that [double n' =
        double m'].  Instantiating the induction hypothesis with [n'] thus
        allows us to conclude that [n' = m'], and it follows immediately
        that [S n' = S m'].  Since [S n' = n] and [S m' = m], this is just
        what we wanted to show. [] *)

(** **** Exercise: 3 stars, standard, especially useful (gen_dep_practice)

    Prove this by induction on [l]. *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x l' Hl].
  -simpl. intros n eq. reflexivity.
  -simpl. intros n eq. destruct n as [| n'].
    +discriminate eq.
    +simpl. apply Hl. injection  eq as goal. apply goal.
Qed.
(** [] *)

(* ################################################################# *)
(** * To vary or not to vary *)

(** One of the following theorems doesn't need a varied hypothesis;
    the others do. Which? Why? (These are rhetorical questions---but
    do try to build up a mental model of when you need varied
    hypotheses. *)

(** **** Exercise: 2 stars, standard (complementary_complementary')

    Let's prove that two versions of the [complementary] predicate are
    equivalent. *)
Print complementary.

(** You defined this yourself, but let's prove things about our
    definition. *)
Definition complementary' (dna1 dna2 : strand) : bool :=
  eq_strand dna1 (map complement dna2).

Lemma complementary_complementary' : forall dna1 dna2,
    complementary dna1 dna2 = complementary' dna1 dna2.
Proof.
  unfold complementary'.
  intros  dna1 dna2.
  generalize dependent dna1.
  induction dna2 as [| b2 dna2' Hb2].
   -intros dna1. destruct dna1 as [| b1 dna1'].
    +simpl. reflexivity.
    +simpl. reflexivity.
  -intros dna1. destruct dna1 as [| b1 dna1'].
   +simpl. reflexivity.
   +simpl. destruct eq_base eqn: Eb.
    *simpl. apply Hb2.
    *simpl. reflexivity.
 Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (complement_correct)

    It's always good to check that your functions do what you think
    they do! Does our [complementary] predicate agree with our
    definition of [complement]? *)
Lemma complement_correct : forall (dna : strand),
    complementary dna (map complement dna) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (eq_strand_iff)

    Prove an equality-iff theorem for DNA strand equality. *)
Lemma eq_strand_iff : forall (dna1 dna2 : strand),
    eq_strand dna1 dna2 = true <-> dna1 = dna2.
Proof.
  split.
  -intros h. generalize dependent dna1.  induction dna2 as [| b2 dna2' Hb2].
   +destruct dna1 as [| b1 dna1'].
    *reflexivity.
    * discriminate.
   +destruct dna1 as [| b1 dna1'].
    *discriminate.
    *simpl. destruct eq_base eqn: Eb.
     simpl. intros h. apply Hb2 in h. apply eq_base_true in Eb.
     rewrite h. rewrite Eb. reflexivity.
     simpl. intros h. discriminate h.
  -intros h. rewrite h. apply eq_strand_refl.
Qed.
(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

       - If [l] is the empty list, then [x] cannot occur on it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if either it is equal to [x'] or it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition: *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  (* Let A, B, f, l, and x be given.  WTP [In x l -> In (f x) (map f l)]. *)
  intros A B f l x.
  (* We go by induction on l. *)
  induction l as [|x' l' IHl'].
  (* In the base case, [l = nil] and we must show [In x [] -> In (f x) (map f [])].
     But assuming [In x []] immediately leads to a contradiction. *)
  - (* l = nil, contradiction *)
    simpl. intros [].
  (* In the inductive case, [l = x' :: l'], our IH is that [In x l' ->
     In (f x) (map f l')].  We must show [In x x'::l' -> In (f x) (map
     f x'::l')], in other words [In x x'::l' -> (f x) = (f x') \/ In
     (f x) (map f l')] by the definitions of [map] and [In]. *)
  - (* l = x' :: l' *)
    (* Assume [In x x'::l'].  That means either [x = x'] or else [In x
       l']. We treat each case separately. *)
    simpl. intros [H | H].
    (* If [x = x'], we will show [In (f x) (map f x'::l')] by showing
       [(f x) = (f x')], which is immediate since [x' = x]. *)
    + rewrite H. left. reflexivity.
    (* If [In x l'], we must show [In (f x) (map f x'::l')] by showing
       [In (f x) (map f l')].  By our IH (and our assumption here that
       [In x l']), we already know [In (f x) (map f l')]. *)
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff) *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  -induction l as [|x' l' H'].
   +simpl. intros [ ].
   +simpl.  intros  [IH | IH].
    *exists x'. split.
     apply IH.
     left. reflexivity.
    *destruct H'.
     apply IH.
     destruct H. exists x. split.
     apply H.
     right. apply H0.
  -intros H.  induction l as [|x' l' H'].
   +simpl. simpl in H. destruct H. destruct H. apply H0.
   +simpl. simpl in H. simpl in H'. destruct H. destruct H. destruct H0.
    *left. rewrite <- H0 in H. apply H.
    *right. apply H'. exists x. split.
     apply H.
     apply H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (In_app_iff) *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (In_flat_map) *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)  :=
  match l with
  | []     => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Lemma In_flat_map:
  forall (A B : Type) (f : A -> list B) (l : list A) (y : B),
  In y (flat_map f l) -> (exists x : A, In y (f x) /\ In x l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (All)

    Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => (P x) /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  split.
  -intros h. induction l as [| x' l' Ihl'].
   +simpl. apply I.
   +simpl. simpl in h. split.
    *apply h. left. reflexivity.
    *apply Ihl'. intros x1 h1. apply h. right. apply h1.
  -induction l as [| x' l' Ihl'].
   +simpl. intros h x. apply ex_falso_quodlibet.
   +simpl. intros h x1 h1. destruct h1.
    *rewrite <- H. apply h.
    *apply Ihl'.
     apply h.
     apply H.
Qed.    
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (All_forallb)

    Recall the function [forallb]:: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  split.
  -intros h. induction l as [| x' l' IHl'].
   +simpl. simpl in h. reflexivity.
   +simpl. simpl in h. destruct test.
    *simpl. simpl in h. split.
     reflexivity.
     apply IHl' in h. apply h.
    *simpl. simpl in h. split.
     apply h. apply IHl'. discriminate h.
  -intros h. induction l as [| x' l' IHl'].
   +simpl. reflexivity.
   +simpl. simpl in h. destruct test.
    *simpl. apply proj2 in h. apply IHl' in h. apply h.
    *simpl. apply proj1 in h. apply h.
Qed.

(** Are there any important properties of the function [forallb] which
    are not captured by this specification? That is, if we take [All]
    as a given, would it be possible to define a version of [forallb]
    that (a) allowed us to prove the theorem above, but (b) was 'bad'
    in some other way? That is, the [forallb] function would be
    'correct' according to [All], but people would agree that it
    wasn't a 'good' function in some sense. *)

(* Forallb can determine whether a type in the list does not fit in test, and returns false if it does not. However, All cannot state that a type in the list does not have the property of Prop.
    [] *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce just one or two more in the coming days.  But basically
    we've got what we need to get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold ... in H]: ... or a hypothesis

      - [fold]: replace a defined constant's right hand side with the
        constant in the goal

      - [fold ... in ...]: ... or a hypothesis

      - [step ...]: A convenience for our one-two [unfold]/[fold]
        trick.

      - [step ... in ...]: ... in an hypothesis.

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [injection]: reason by injectivity of constructors

      - [discriminate]: reason by disjointness of constructors

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula

    That's a lot! We'll learn just a few more in the next day of class
    when we learn a final, critical concept; then we'll do some small
    case studies; then we'll finally transition to informal proof.  *)

(* 2021-10-04 14:37 *)
