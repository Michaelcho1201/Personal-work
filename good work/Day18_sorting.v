Require Export DMFP.Day17_indprop2.

(* ################################################################# *)
(** * Permutations *)

(** A _permutation_ of a list is a rearrangement of its elements.

    We can define permutations using the following inductive
    proposition.  We'll worry about whether or not this is _exactly_
    the right proposition later on.
 *)

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
| perm_nil: Permutation [] []
| perm_skip (x:A) (l l':list A) (H : Permutation l l') : Permutation (x::l) (x::l')
| perm_swap (x y:A) (l:list A) : Permutation (y::x::l) (x::y::l)
| perm_trans (l1 l2 l3 : list A) (H12 : Permutation l1 l2) (H23 : Permutation l2 l3)
  : Permutation l1 l3.

Example permutation_eg :
  Permutation [true;true;false] [false;true;true].
Proof.
  apply (perm_trans _ [true;false;true] _).
  { apply perm_skip.
    apply perm_swap. }
  { apply perm_swap. }
Qed.

(** **** Exercise: 1 star, standard (Permutation_refl) *)
Theorem Permutation_refl : forall A (l : list A),
    Permutation l l.
Proof.
  intros A l. induction l.
  -apply perm_nil.
  -apply perm_skip. apply IHl.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (Permutation_length) *)
Theorem Permutation_length : forall A (l1 l2 : list A),
  Permutation l1 l2 -> length l1 = length l2.
Proof.
  intros A l1 l2 H. induction H.
  -reflexivity.
  -simpl. Search S. apply eq_S. apply IHPermutation.
  -simpl. reflexivity.
  -rewrite IHPermutation1. apply IHPermutation2.
Qed.
(** [] *)

(** How might [Permutation_length] look as in informal proof?

    - _Theorem_: if [l1] is a permutation of [l2], then [l1] and [l2]
      have the same length.

    _Proof_: Let lists [l1] and [l2] be given such that [l1] is a
    permutation of [l2]. We go by induction on the derivation of
    [Permutation l1 l2]. There are four cases.

    - ([perm_nil]) We have [l1 = []] and [l2 = []], both of which have
      [length] 0.

    - ([perm_skip]) We have [l1 = x::l1'] and [l2 = x::l2'] and
      [Permutation l1' l2']; our IH shows that [length l1' = length
      l2']. We have [length (x::l1') = length (x::l2')] immediately by
      the IH.

    - ([perm_swap]) We have [l1 = y::x::l] and [l2 = x::y::l]. We have
      [length (y::x::l) = length (x::y::l)] immediately.

    - ([perm_trans]) We have [l1 = l] and [l2 = l''] and a list [l']
      such that [Permutation l l'] and [Permutation l' l'']; our IHs
      show that [length l = length l'] and [length l' = length
      l'']. We can find [length l1 = l2] by transitivity of equality
      and our IHs. _Qed_.  *)

(** Notice that we get IHs in the [perm_skip] and [perm_trans] cases
    but not in [perm_nil] and [perm_swap]. Why is that?

    Induction hypothesis come from "smaller" things---for [nat]s, we
    get an IH for the [n = S n'] case because there's a smaller [nat]
    involved---[n']. For inductive propositions, we'll get an IH when
    there's a recursive reference to the proposition we're
    defining. Both [perm_skip] and [perm_trans] refer back to the
    [Permutation] definition as a premise (and so we get an IH) but
    [perm_nil] and [perm_swap] don't (and so we don't get an IH). *)

(** More generally, induction on propositions works as
    follows. We have the following rules:


             -----------------             (perm_nil)
             Permutation [] []

              Permutation l l'
         --------------------------        (perm_skip)
         Permutation (x::l) (x::l')

       -------------------------------     (perm_swap)
       Permutation (y::x::l) (x::y::l)

    Permutation l l'    Permutation l' l''
    -------------------------------------- (perm_trans)
                Permutation l l''
*)
(** We want to prove that for all [l1] and [l2], if [Permutation l1
    l2] and then [length l1 = length l2].

    Having let [l1] and [l2] be given such that [Permutation l1 l2],
    we go by induction on the derivation to show that [length l1 =
    length l2]. What cases do we have? When do we have an IH and where
    does it come from?

    We will have _one case for each rule_. If the rule is of the form
    [Permutation a b], then we will have to show our goal for [a] and
    [b]. Here, that means showing that [length a = length b]. So in
    the [perm_nil] case, we have to prove that [length [] = length
    []], since [perm_nil] only applies when both [l1 = []] and [l2 =
    []]. In [perm_trans], we'll get to keep our hypotheses (that
    [Permutation l l'] and [Permutation l' l'']) and we'll have to
    prove that [length l = length l''] (since the [a] and [b] in the
    goal are [l] and [l''], respectively).

    We get an IH for each premise that is a recursive reference. That
    is, [perm_nil] and [perm_swap] are _axioms_, so there's no IH. But
    [perm_skip] and [perm_trans] both have premises that involve
    recursive references to the inductive relation we're looking at,
    so we get IHs.

    In a case where we have a recursive reference of the form
    [Permutation a b], we'll have a corresponding IH based on our
    goal, using [a] and [b]. That is, for this proof, we get an IH
    saying that [length a = length b]. Concretely, the [perm_skip]
    rule will give us [length l = length l']; the [perm_trans] rule
    will give us _two_ IHs: one saying that [length l = length l'] and
    one saying that [length l' = length l''].

    One final remark: we've called something an _axiom_ when it has no
    premises and a _rule_ otherwise. But not every rule gets an IH!

    We could have given the following rule instead of [perm_nil]:


             l = []   l' = []
             ----------------             (perm_nil')
             Permutation l l'

    In this case [perm_nil'] isn't _strictly speaking_ an axiom, but
    we still wouldn't get an IH. You only get an IH for each
    _recursive use_ of the inductive predicate.
 *)

(** **** Exercise: 1 star, standard (Permutation_sym) *)
Lemma Permutation_sym : forall A (l1 l2 : list A),
  Permutation l1 l2 -> Permutation l2 l1.
Proof.
  intros A l1 l2 H. induction H.
  -apply perm_nil.
  -apply perm_skip. apply IHPermutation.
  -apply perm_swap.
  -apply perm_trans with l2.
   +apply IHPermutation2.
   +apply IHPermutation1.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (All_perm) 

    To close, a useful utility lemma.  Prove this by induction; but is
    it induction on [al], or on [bl], or on [Permutation al bl], or on
    [All f al]? Some choices are _much_ easier than others! If
    you're stuck, try a different one. *)

Theorem All_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  All f al -> All f bl.
Proof.
  intros A f al bl H Ha. induction H.
  -apply Ha.
  -inversion Ha. simpl. split.
   +apply H0.
   +apply IHPermutation. apply H1.
  -inversion Ha. inversion H0. simpl. split.
   +apply H1.
   +split. 
    *apply H.
    *apply H2.
  -apply IHPermutation2. apply IHPermutation1. apply Ha.
Qed.
(** [] *)

(* ================================================================= *)
(** ** A computational interpretation *)

(** What does our function [permutations] have to do with the
    inductive proposition [Permutation]? We can prove that our
    function [permutations] is in some sense _complete_: everything it
    produces is a permutation of the given list. First, recall our
    definitions. *)

Fixpoint everywhere {A:Type} (a:A) (ls:list A) : list (list A) :=
  match ls with
  | [] => [[a]]
  | h :: t => (a :: ls) :: (map (fun t' => h::t') (everywhere a t))
  end.

Fixpoint permutations {A:Type} (ls:list A) : list (list A) :=
  match ls with
  | [] => [[]]
  | h :: t => flat_map (everywhere h) (permutations t)
  end.

(** **** Exercise: 2 stars, standard (everywhere_perm) *)
Lemma everywhere_perm : forall A (l l' : list A) (x : A),
  In l' (everywhere x l) ->
  Permutation (x :: l) l'.
Proof.
  intros A l l' x H.
  generalize dependent l'. generalize dependent x. generalize dependent A.
  induction l as [| x' l'' IH].
  -intros x l'  H. simpl in H. destruct H.
   +rewrite H. apply Permutation_refl.
   +destruct H.
  -intros x  l' H. induction H.
   +rewrite H. apply Permutation_refl.
   +apply In_map_iff in H. induction H. induction H.
    rename x0 into l. apply IH in H0. apply perm_trans with ( x' :: x :: l'').
    *apply perm_swap.
    *rewrite <- H. apply perm_skip. apply H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (permutations_complete) *)
Theorem permutations_complete : forall A (l l' : list A),
    In l' (permutations l) -> Permutation l l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (permutations_correct)

    It's possible to prove the converse, that [Permutation l l']
    implies [In l' (permutations l)]. Feel free to give it a go, but
    it's very challenging!

    [] *)

(** * Sortedness*)

Fixpoint insert_sorted (i:nat) (l: list nat) :=
  match l with
  | nil => i::nil
  | h::t => if leb i h then i::h::t else h :: insert_sorted i t
 end.

Fixpoint sort (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => insert_sorted h (sort t)
end.

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.

    What does it mean for a list to be sorted? We can define an
    inductive proposition that seems to do the trick: *)

Inductive sorted: list nat -> Prop :=
  | sorted_nil          : sorted []
  | sorted_1    (x:nat) : sorted [x]
  | sorted_cons (x y:nat) (l:list nat) (Hxy : x <= y) (H : sorted (y::l))
                        : sorted (x::y::l).

Example sorted_one_through_four :
  sorted [1;2;3;4].
Proof.
  (* WORKED IN CLASS *)
  apply sorted_cons. { apply le_S. apply le_n. }
  apply sorted_cons. { apply le_S. apply le_n. }
  apply sorted_cons. { apply le_S. apply le_n. }
  apply sorted_1.
Qed.

(** Is this really the right definition of what it means for a list to
    be sorted?  One might have thought that it should refer to list
    indices, i.e., for valid indices i,j into the list, the ith item
    is less than or equal to the jth item: *)

Fixpoint nth {X:Type} (n:nat) (l:list X) (default:X) : X :=
  match n,l with
  | _,[] => default
  | 0,h::_ => h
  | (S n'),_::t => nth n' t default
  end.

Example nth_in_list : nth 3 [1;2;3;4;5] 0 = 4.
Proof. reflexivity. Qed.

Example nth_default : nth 7 [1;2;3;4;5] 0 = 0.
Proof. reflexivity. Qed.

Definition sorted' (al: list nat) :=
 forall i j, i < j < length al -> nth i al 0 <= nth j al 0.

(** Note: the notation [i < j < length al] really means [i < j /\ j <
    length al]: *)
Compute (0 < 1 < 2).

(** This is a reasonable definition too.  It should be equivalent.
    Later on, we'll prove that the two definitions really are
    equivalent.  For now, let's use the first one to define what it
    means to be a correct sorting algorthm. *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).

(** That is: the result [(f al)] should not only be a [sorted]
    sequence, but it should be some rearrangement (Permutation) of the
    input sequence. *)

(* ################################################################# *)
(** * Proofs with Sortedness *)

(** Before proving that we can write a sorting algorithm, let's get
    some intution for how the [sorted] predicate behaves.
 *)

(** First, let's reflect [sorted]. *)

Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x::(y::_) as l => leb x y && is_sorted l
  end.

Lemma is_sorted_iff_sorted : forall l,
    is_sorted l = true <-> sorted l.
Proof.
  (* WORKED IN CLASS *)
  intros. split.
  - intros H. induction l as [|n l' IHl'].
    + apply sorted_nil.
    + destruct l' as [|m l''].
      * apply sorted_1.
      * simpl in H.  apply andb_true_iff in H.  apply sorted_cons.
        { destruct H as [H _]. apply leb_complete. apply H. }
        { destruct H as [_ H]. apply IHl'. apply H. }
  - intros H. induction H as [|n|n m l' Hnm H IH].
    + reflexivity.
    + reflexivity.
    + simpl. apply leb_correct in Hnm. rewrite Hnm. simpl. apply IH.
Qed.

(** In particular, what operations _preserve_ sortedness? Which
    functions will return a sorted list when given a sorted list?
    We can formalize the notion of preservation as follows:
*)

Definition preserves_sortedness (f : list nat -> list nat) :=
  forall al, sorted al -> sorted (f al).

(** What operations on lists do we have? Let's start with simple ones,
    like mapping ([map]). If we map the successor function [S] over a
    sorted list, the list should still be sorted.
*)

Lemma add1_preserves_sortedness :
    preserves_sortedness (map S).
Proof.
  intros al H. induction H.
  - simpl. apply sorted_nil.
  - simpl. apply sorted_1.
  - simpl. simpl in IHsorted.
    apply sorted_cons.
    apply n_le_m__Sn_le_Sm.
    apply Hxy.
    apply IHsorted.
Qed.

(** We can do more than add one... we can add two! *)

Lemma add2_preserves_sortedness :
    preserves_sortedness (map (plus 2)).
Proof.
  intros al H. induction H.
  - simpl. apply sorted_nil.
  - simpl. apply sorted_1.
  - simpl. simpl in IHsorted.
    apply sorted_cons.
    apply n_le_m__Sn_le_Sm.
    apply n_le_m__Sn_le_Sm.
    apply Hxy.
    apply IHsorted.
Qed.

(** There are lots of functions that preserve sortedness. So many, in
    fact, that we can characterize a set of them: the _monotonic_
    functions are those that preserve ordering, i.e., if [x <= y] then
    [f x <= f y]. Both [S] and [(plus 2)] are monotonic.
*)

Definition monotonic f := forall x y, x <= y -> f x <= f y.

(** Every monotonic function preserves sortedness. *)

Lemma monotonic_preserves_sortedness : forall f,
    monotonic f -> preserves_sortedness (map f).
Proof.
  intros f Hf.
  intros al H. induction H.
  - simpl. apply sorted_nil.
  - simpl. apply sorted_1.
  - simpl. simpl in IHsorted.
    apply sorted_cons.
    apply Hf. apply Hxy.
    apply IHsorted.
Qed.

(** **** Exercise: 3 stars, standard, optional (addn_preserves_sortedness)

    Now prove that adding _any_ number preserves sortedness. *)

Lemma addn_preserves_sortedness : forall n,
    preserves_sortedness (map (plus n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Other operations preserve sortedness, too. For example, we can
    remove any elements we want from a sorted list and the list will
    still be sorted. We can formalize this idea using the [filter]
    function---for any predicate [p], [filter p] preserves
    sortedness. *)

(** **** Exercise: 4 stars, standard, optional (sorted_filter_cons)

    Our proof goes in two stages. First, we show that if something is
    good at the front of a sorted list, it's also good at the front of
    a [filter]ed sorted list.

    Think carefully about what you do induction on. You may need a
    helper lemma in a particularly tricky case!
*)

Lemma sorted_filter_cons : forall l p x,
    sorted (x :: l) ->
    sorted (x :: filter p l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (filter_preserves_sortedness)

    Using the (optional) lemma above, we can prove the more general
    property: [(filter p)] preserves sortedness for all predicates
    [p].

    There are two ways to prove this function, and one is much easier
    than the other... but both require [sorted_filter_cons].  *)

  
Lemma filter_preserves_sortedness : forall p,
    preserves_sortedness (filter p).
Proof.
  intros p l h. induction  h.
  - simpl. apply sorted_nil.
  - simpl. destruct (p x).
    +apply sorted_1.
    +apply sorted_nil.
  - simpl. induction (p x).
    + induction (p y).
     * apply sorted_cons.
       apply Hxy.
       apply sorted_filter_cons. apply h.
     * apply sorted_filter_cons. destruct l as [| x' l'].
       apply sorted_1. inversion h. apply sorted_cons.
       rewrite Hxy. apply Hxy0.
       apply H0.
   + simpl in IHh. apply IHh.
Qed. 
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bad_function_breaks_sortedness) *)

(** Not _every_ function preserves sortedness. Define a non-recursive
    function that doesn't preserve sortedness. You may use any other
    function we've defined so far. (You can even write a recursive
    function, if you want, but it's possible to solve this exercise
    without it. *)

Definition bad_function : nat -> nat (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Now prove that your function doesn't preserve sortedness. *)

Lemma bad_function_breaks_sortedness :
  ~ preserves_sortedness (map bad_function).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** **** Exercise: 3 stars, standard (insert_sorted_perm)

    Prove the following auxiliary lemma, [insert_sorted_perm], which will be
    useful for proving [sort_perm] below.  Your proof will be by
    induction, but you'll need some of the permutation facts from the
    above. *)

Lemma insert_sorted_perm: forall x l, Permutation (x::l) (insert_sorted x l).
Proof.
  intros x l. generalize dependent x. induction l as[| x l' Ihl'].
  -intros x'. simpl. apply Permutation_refl.
  -intros x'. simpl. destruct leb.
   +apply Permutation_refl.
   +simpl. apply perm_trans with (x :: x' :: l').
    *apply perm_swap. 
    *apply perm_skip. apply Ihl'.
Qed.
  (** [] *)

(** **** Exercise: 3 stars, standard, optional (sort_perm)

    Now prove that sort is a permutation. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard (insert_sorted_sorted)

    This one is a bit tricky.  However, there is just a single
   induction right at the beginning, and you do _not_ need to use
   [insert_sorted_perm] or [sort_perm]. The [leb_spec] lemma from day
   16 may come in handy, or you can [(destruct leb ...)] and use
   [leb_iff] and [leb_n_m__leb_m_n].

   Remember you can destruct anything that comes in multiple
   cases---and remember that you can write expressions that "evaluate"
   theorems as if they were functions.  "Note that by [leb_spec n m],
   either [leb n m = true] or else [leb n m = false] and [leb m n =
   true]; first, consider the case where [leb n m = true]..."  *)
Lemma false_leb : forall n1 n2,
    ( leb n1 n2) = false -> leb n2 n1 = true.
Proof.
  intros n1 n2 h.
  Check (leb_spec n1 n2).
  destruct (leb_spec n1 n2).
  - rewrite H in h. discriminate h.
  - destruct H. apply H0.
Qed.

Lemma insert_sorted_sorted:
  forall a l, sorted l -> sorted (insert_sorted a l).
Proof.
  intros a l h.  induction h.
  -simpl. apply sorted_1.
  -simpl.  destruct leb eqn: E.
    +apply sorted_cons.
      *apply leb_complete in E. apply E.
      *apply sorted_1.
    +apply sorted_cons.
      *apply false_leb in E. apply leb_complete in E. apply E.
      *apply sorted_1.
  -simpl. simpl in IHh. destruct (leb a x) eqn: Ex.
    +apply sorted_cons.
     *apply leb_complete in Ex. apply Ex.
     *apply sorted_cons.
       apply Hxy.
       apply h.
    +destruct (leb a y) eqn: Ey.
      *apply sorted_cons.
        apply false_leb in Ex. apply leb_complete in Ex. apply Ex.
        apply IHh.
      *apply sorted_cons.
        apply Hxy.
        apply IHh.
   Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (sort_sorted)

    This one is shorter. *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
 intros l. induction l.
 -apply sorted_nil.
 -simpl. induction (sort l).
  +simpl. apply sorted_1.
  +apply insert_sorted_sorted. apply IHl.
Qed.
(** [] *)

(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  split. apply sort_perm. apply sort_sorted.
Qed.

(** **** Exercise: 2 stars, standard, optional (sort_stable)

    It's a nice exercise to prove the idempotence and stability lemmas
    from the informal work in Coq.

    Two terms of art are used here: _idempotent_ and _stable_. A
    function [f] is _idempotent_ when [f (f x) = f x].

    A sort is _stable_ when it doesn't change the original orderings
    of two elements. To generally show stability, we'd have to prove
    that for _any_ two elements [x] and [y] in a list [l], if [x <= y]
    and [x] comes before [y] in [l], then [x] comes before [y] in
    [sort l].

    We're not going ot prove stability proper (which doesn't really
    make sense if we're only talking about [nat]s, but a weaker
    concept. *)
Lemma sort_already_sorted : forall l,
    sorted l -> sort l = l.
Proof.
  (* FILL IN HERE *) Admitted.

Corollary sort_idempotent : forall l,
    sort (sort l) = sort l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Making Sure the Specification is Right *)

(** It's really important to get the _specification_ right.  You can
    prove that your program satisfies its specification (and Coq will
    check that proof for you), but you can't prove that you have the
    right specification.  Therefore, we take the trouble to write two
    different specifications of sortedness ([sorted] and [sorted']),
    and prove that they mean the same thing.  This increases our
    confidence that we have the right specification, though of course
    it doesn't _prove_ that we do. *)

(** **** Exercise: 4 stars, standard, optional (sorted_sorted') *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.

(** Hint: Instead of doing induction on the list [al], do induction
    on the _sortedness_ of [al]. This proof is a bit tricky, so
    you may have to think about how to approach it, and try out
    one or two different ideas.*)

(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (sorted'_sorted) *)
Lemma sorted'_sorted: forall al, sorted' al -> sorted al.

(** Here, you can't do induction on the sorted'-ness of the list,
    because [sorted'] is not an inductive predicate. *)

Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Proving Correctness from the Alternate Spec *)

(** Depending on how you write the specification of a program, it can
    be _much_ harder or easier to prove correctness.  We saw that the
    predicates [sorted] and [sorted'] are equivalent; but it is really
    difficult to prove correctness of insertion sort directly from
    [sorted'].

    Try it yourself, if you dare!  I managed it, but my proof is quite
    long and complicated.  I found that I needed all these facts:
    - [insert_sorted_perm], [sort_perm]
    - [All_perm], [Permutation_length]
    - [Permutation_sym], [Permutation_trans]
    - a new lemma [All_nth], stated below.

    Maybe you will find a better way that's not so complicated.

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted_sorted], or
    [sort_sorted] in these proofs! *)

(** **** Exercise: 3 stars, standard, optional (All_nth) *)
Lemma All_nth:
  forall {A: Type} (P: A -> Prop) d (al: list A),
     All P al <-> (forall i,  i < length al -> P (nth i al d)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (insert_sorted_sorted') *)
(* Prove that inserting into a sorted list yields a sorted list, for
   the index-based notion of sorted.

   You'll find [leb_spec] handy again. If you find that your context
   gets cluttered, you can run [clear H] to get rid of the hypothesis
   [H]; you can run [clear - H] to get rid of everything _but_ [H]. Be
   careful---you can't undo these tactics! *)
Lemma insert_sorted_sorted':
  forall a l, sorted' l -> sorted' (insert_sorted a l).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (sort_sorted') *)
Theorem sort_sorted': forall l, sorted' (sort l).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** The Moral of This Story *)

(** The proofs of [insert_sorted_sorted] and [sort_sorted] were easy;
    the proofs of [insert_sorted_sorted'] and [sort_sorted'] were
    difficult; and yet [sorted al <-> sorted' al].  _Different
    formulations of the functional specification can lead to great
    differences in the difficulty of the correctness proofs_.

    Suppose someone required you to prove [sort_sorted'], and never
    mentioned the [sorted] predicate to you.  Instead of proving
    [sort_sorted'] directly, it would be much easier to design a new
    predicate ([sorted]), and then prove [sort_sorted] and
    [sorted_sorted']. *)

(* 2021-09-28 15:37 *)
