Require Export DMFP.Day06_sorting.

(* ################################################################# *)
(** * Binary trees *)

(** Recall the definition of binary trees [bt] from Day04_structures:

Inductive bt (X : Type) : Type :=
| empty
| node (l : bt X) (v : X) (r : bt X).

*)

Check empty.
Check @empty nat.
Check (node empty true empty). (* leaf node *)
Check (node empty 5 empty). (* leaf node *)
Check (node empty G (node empty C empty)).
Check (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty)).

Compute (size (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty))).

(** We defined some terminology already: a _leaf_ is a node where both
    children are [empty].

    The _root_ of a tree is the topmost node. *)

Definition root {X : Type} (t : bt X) : option X :=
  match t with
  | empty => None
  | node _ v _ => Some v
  end.

Compute (root (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty))).
(* ===> Some 25 *)

(** It's common enough to want to make a leaf that we'll define a
    function to do it for us. *)
Definition leaf {X : Type} (v : X) : bt X := node empty v empty.

Compute (root (node (leaf 12) 25 (node (leaf 5) 5 empty))).
(* ===> Some 25 *)

(* ################################################################# *)
(** * What are trees for? *)

(** Trees are a useful and general structure. Computer scientists use
    trees:

    - In interpreters, compilers, and program analyses to represent
      and manipulate programs.

    - In machine learning's so-called "decision trees".

    - In game AI to represent strategies.

    - In operating systems to store filesystem information.

    - In databases to quickly manipulate stored values.

    But it's not just CS! Biological systematists use trees to model
    evolutionary relationships. Linguists use trees to model syntactic
    structure. Genealogists use trees to model familial relationships.

    Trees are a Big Deal. Here's a very contrived tree model of
    declarative English sentences. *)

Inductive proper_noun : Type :=
  | Prof_Greenberg
  | Opie_the_dog
  | Prof_Osborn
  | Dr_Dave.

Inductive article : Type :=
  | the
  | a.

Inductive noun : Type :=
  | program
  | frisbee
  | lasagna
  | unicycle.

Inductive noun_phrase : Type :=
  | np_proper (pn : proper_noun)
  | np_compound (a : article) (n : noun).

Inductive verb_intransitive : Type :=
  | laughed
  | danced
  | barked.

Inductive verb_transitive : Type :=
  | bit
  | wrote
  | baked
  | rode.

Inductive preposition : Type :=
  | under
  | around
  | in_front_of.

Inductive adverb : Type :=
  | goofily
  | well
  | sarcastically.

Inductive modifier : Type :=
  | m_prep (p : preposition) (np : noun_phrase)
  | m_adverb (a : adverb).

Inductive verb_phrase : Type :=
  | vp_intransitive (v : verb_intransitive)
  | vp_transitive (v : verb_transitive) (o : noun_phrase)
  | vp_modifier (vp : verb_phrase) (m : modifier).

Inductive sentence : Type :=
  | s (np : noun_phrase) (vp : verb_phrase).

(** **** Exercise: 1 star, standard (sentences)

    Write a tree that models a sentence where Prof. Greenberg danced in front of Opie. *)
Definition goofball : sentence :=
  s (np_proper Prof_Greenberg)(vp_modifier (vp_intransitive danced)(m_prep in_front_of (np_proper Opie_the_dog))).


(** Write a tree that models a sentence where Opie bakes a lasagna
    well. Good boy! *)
Definition good_dog : sentence :=
  s (np_proper Opie_the_dog)(vp_modifier (vp_transitive baked (np_compound a lasagna))(m_adverb well)).

(** Translate the following tree to an English sentence. *)
Definition so_talented : sentence :=
  s (np_proper Dr_Dave)
    (vp_modifier
       (vp_modifier
          (vp_transitive rode (np_compound the unicycle))
          (m_adverb goofily))
       (m_prep around (np_compound the frisbee))).
(* Dr. Dave rode the unicycle goofily around the frisbee. *)

(* Do not modify the following line: *)
Definition manual_grade_for_sentences : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Traversals *)

(** A tree is a useful data structure in a program, but it isn't
    always what people want to see---people often do better with
    lists.

    Any function that looks at every node of a tree is called a
    _traversal_. The word 'traversal' often refers particularly to the
    process of converting a tree to a list.

    There are three common notions of traversal, named for what they
    do with the value at a given node:

    - A _pre-order_ traversal puts the value first, then traverses the
      left child, then the right child.

    - An _in-order_ traversal first traverses the left child, then the
      value of the node, then the right child.

    - A _post-order_ traversal first traverses the left child, then
      the right child, then the value of the node.

    You'll notice that all three of these go left-to-right. That's a
    convention---you could look at the right children, then the left
    children, then the node. Which traversal you use in practice
    depends on *)

(** Here's an in-order traversal. *)
Fixpoint inorder {X : Type} (t : bt X) : list X :=
  match t with
  | empty => []
  | node l v r => inorder l ++ [v] ++ inorder r
  end.

Compute (inorder (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty))).

(** **** Exercise: 2 stars, standard (traversals)

    Define traversal functions [preorder] and [postorder] that
    implement those respective traversals. *)
Fixpoint preorder {X : Type} (t : bt X) : list X :=
  match t with
  | empty => []
  | node l v r => [v] ++ preorder l ++ preorder r
  end.

Compute (preorder (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty))).

Fixpoint postorder {X : Type} (t : bt X) : list X :=
  match t with
  | empty => []
  | node l v r => postorder l  ++ postorder r ++ [v]
  end.

Compute (postorder (node (node empty 12 empty) 25 (node (node empty 5 empty) 5 empty))).

(** Write a tree that produces different output from all three
    traversals. (Note the type!) It should have at least three
    nodes. *)
Definition different_all_three : bt base :=
  node(node empty T empty) C  (node empty A empty).

Compute (inorder different_all_three).
Compute (preorder different_all_three).
Compute (postorder different_all_three). 

(** Write a tree that produces the same output from pre- and in-order
    traversals (but not post-order). It should have at least three
    nodes. *)
Definition same_pre_in : bt base :=
  node(node empty T empty) T  (node empty A empty).

Compute (inorder same_pre_in).
Compute (preorder same_pre_in).
Compute (postorder same_pre_in).

(** Write a tree that produces the same output from in- and post-order
    traversals (but not pre-order). It should have at least three
    nodes. *)
Definition same_post_in : bt base :=
  node(node empty T empty) C  (node empty C empty).

Compute (inorder same_post_in).
Compute (preorder same_post_in).
Compute (postorder same_post_in). 

(* Do not modify the following line: *)
Definition manual_grade_for_traversals : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Binary search trees (BSTs) *)

(** Binary search trees are pervasive and powerful data
    structures. They are used to implement sets and associative maps,
    two of the most commonly used data structures.

    BSTs _refine_ binary trees with an _invariant_ called the 'search
    property'. A binary tree [t] is said to have the _search property_
    when for a given ordering (i.e., a notion of 'less than' and
    'greater than'):

    - [t] is [empty], or

    - [t] is [node l v r] where:

      + [l] and [r] have the search property

      + every value in [l] is less than [v]

      + every value in [r] is greater than [v]

    The search property is very useful. Suppose you have a binary
    search tree, and you wonder if a value [n] is in it. First, you
    check the root: if that's it, great. If not, then ask: is [n] less
    than or greater than the root? You only have to keep looking in
    one side of the tree! If your tree is well balanced, you'll do
    very little traversal at all.  If you kept a list rather than a
    BST, you'd have to search the whole list to be sure. Nice... what
    a savings!

    It turns out other operations on BSTs---adding and deleting
    elements---are also very efficient. We'll implement a few.

    (Sometimes people want BSTs were values in [l] are less than _or
    equal to_ [v]. It depends; for sets and maps, you want _less
    than_, because it guarantees there are no duplicates.)
*)

(** **** Exercise: 1 star, standard (search_property)

    Write two trees of naturals that have the search property and two
    trees that do not. All of your trees should have at least two
    nodes. *)

Definition bst1 : bt nat := node(node empty 5 empty) 10 (node empty 24 empty).
Definition bst2 : bt nat := node(node empty 35 empty) 48 (node empty 55 empty).
Definition non_bst1 : bt nat := node(node empty 20 empty) 10 (node empty 30 empty).
Definition non_bst2 : bt nat := node(node empty 45 empty) 69 (node empty 58 empty).
(* Do not modify the following line: *)
Definition manual_grade_for_search_property : option (nat*string) := None.
(** [] *)

(** We've already defined [eqb] and [leb], so we could just use
    those. But it's common to use a [compare] operation that gives us
    'complete' comparison information. It saves comparisons and is
    less error prone. What's not to like? *)
Inductive ordering : Type :=
  | LT
  | EQ
  | GT.

Fixpoint compare (n m : nat) : ordering :=
  match n, m with
  | O, O => EQ
  | S _, O => GT
  | O, S _ => LT
  | S n', S m' => compare n' m'
  end.

Compute (compare 0 0).       (* ===> EQ *)
Compute (compare 0 10).      (* ===> LT *)
Compute (compare 7 4).       (* ===> GT *)
Compute (compare 1000 1000). (* ===> EQ *)

(** Here's a function that uses the search property to rapidly
    determine whether or not a value is in a BST already. *)
Fixpoint lookup (n : nat) (t : bt nat) : bool :=
  match t with
  | empty => false
  | node l v r =>
    match compare n v with
    | LT => lookup n l
    | EQ => true
    | GT => lookup n r
    end
  end.

(** **** Exercise: 3 stars, standard (insert)

    Write a function that inserts a number [n] into a binary search
    tree [t]. To get full credit, you should use the binary search
    property!

    What should your function do when [n] is already in the tree?  *)
Fixpoint insert (n : nat) (t : bt nat) : bt nat :=
  match t with
  | empty => node empty n empty
  | node l v r => match compare n v with
                   | LT => node ( insert n l) v r
                   | EQ => t
                   | GT => node l v ( insert n r)
                   end
  end.

Compute (insert 5 (node (node empty 3 empty)4 (node empty 6 empty))).
Compute (insert 8 (node (node empty 7 empty) 9 (node empty 10 empty))).
Compute (insert 11 (node (node empty 11 empty) 12 (node empty 13 empty))).
Compute (insert 4 (node (node(node empty  1 empty) 2 (node empty 3 empty)) 5 (node empty 6 empty))).

(** [] *)

(** **** Exercise: 2 stars, standard (remove_min)

    Write a function that tries to remove the smallest element from a
    binary search tree. You'll need to return not just the smallest
    element, but also what's left of the tree.

    Your function should return [None] only when [t] is [empty]. Use
    the search property! *)
Fixpoint remove_min (t : bt nat) : option (nat * bt nat) :=
  match t with
  |empty  => None
  | node l v r => match l with 
                  | empty => Some (v , r)
                  | node empty l' empty => Some (l' , node empty v r)
                  | node l' v' r' =>  match remove_min l with
                                      | None => None
                                      | Some (nat, empty )=> Some ( nat , node empty v r)
                                      | Some ( nat , node l' v' r' ) => Some ( nat , node (node l' v' r' ) v r)
                                      end
                  end
 end. 

Compute (remove_min (node (node  empty 1 (node empty 2 empty) ) 3 (node (node empty 4 empty) 5 empty))).
Compute (remove_min empty ).
Compute (remove_min (node empty 6 empty)).
Compute (remove_min (node empty 7 (node (node empty 8 empty) 9 (node empty 10 empty)))).

(** [] *)

(** **** Exercise: 4 stars, standard (remove)

    Write a function that removes a number [n] from a binary search
    tree.  If [n] isn't in the tree, you should return the tree
    unchanged.

    It turns out this is a hard function to write! Here's a general
    plan:

    - Handling [empty] should be simple.

    - To remove [n] from [node l v r], look at [compare n v].

      + The [LT] and [GT] cases should be simple.

      + The [EQ] case is tricky! Use [remove_min] to find a new root
        element from [r] if you can. What does it mean if [remove_min
        r = None]?
 *)
Fixpoint remove (n : nat) (t : bt nat) : bt nat :=
  match t with
  | empty => t
  | node l v r => match compare n v with
                  | LT => node (remove n l) v r
                  | EQ => match remove_min r with
                          | None => l
                          | Some (nat , empty) => node l nat empty
                          | Some (nat, node l' v' r')=> node l nat (node l' v' r')
                          end
                  | GT => node l v (remove n r)
                  end
  end.


Compute (remove 3 (node (node  empty 1 (node empty 2 empty) ) 3 (node (node empty 4 empty) 5 empty))).
Compute (remove 5  empty ).
Compute (remove 6 (node empty 6 empty)).
Compute (remove 7 (node empty 7 (node (node empty 8 empty) 9 (node empty 10 empty)))).
         
(** [] *)

(** **** Exercise: 4 stars, standard, optional (is_bst)

    Write a function [is_bst] that takes [t : bt nat] and returns
    [true] if [t] has the search property.

    There are different ways to go here. A few hints:

    - You'll need at least one helper function. How can you check the
      "every value" parts of the search property?

    - Don't think about efficiency---you're just making things hard
      for yourself. Get it to work first, and then make it efficient
      if that'll make you happy.

    We'd like you to write the signature yourself. If you can't finish
    writing the function, that's fine---but make sure you use
    [Definition] and [Admitted] to leave something behind for the
    grader. Talk to the TAs if you're stuck.  *)

(* Do not modify the following line: *)
Definition manual_grade_for_is_bst : option (nat*string) := None.
(** [] *)

(* 2021-09-13 09:44 *)
