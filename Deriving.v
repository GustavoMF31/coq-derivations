Require Import PeanoNat.
Import Nat.

Require Import Derive. (* For the "Derive" extension *)
Require Import Setoid. (* For more powerful rewriting *)

(* A few simple lemmas about equivalences of propositions
  that turn out to be useful *)
Lemma iff_true : forall P, P <-> (P <-> True).
Proof. intuition. Qed.

Lemma prov_imp_iff_true : forall {P:Prop}, P -> (P <-> True).
Proof. intuition. Qed.

Lemma true_neutral : forall P, P /\ True <-> P.
Proof. intuition. Qed.

Lemma true_absorb : forall P, P \/ True <-> True.
Proof. intuition. Qed.

Lemma false_neutral : forall P, P \/ False <-> P.
Proof. intuition. Qed.

Lemma false_absorb : forall P, P /\ False <-> False.
Proof. intuition. Qed.

Lemma and_or_distr : forall P Q R,
  P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
Proof. intuition. Qed.

Lemma or_and_distr : forall P Q R,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. intuition. Qed.

Lemma in_and : forall (P Q R : Prop),
  (P -> (Q <-> R)) -> (P /\ Q <-> P /\ R).
Proof. intuition. Qed.

Lemma float_exists : forall {X} (P : X -> Prop) Q,
  (Q /\ exists x, P x) <-> exists x, Q /\ P x.
Proof. split.
  - intros [q [x p]]. exists x. easy.
  - intros [x [q p]]. split. easy. exists x. easy.
Qed.

(* Principle of indirect equality *)
Lemma indir_eq : forall a b, (forall c, a <= c <-> b <= c) <-> a = b.
Proof. intros a b. split. 
  - intro H. apply le_antisymm.
    + apply H. apply le_n.
    + symmetry in H. apply H. apply le_n.
  - intro. subst. easy.
Qed.

Ltac rewr_to_true P := rewrite (prov_imp_iff_true P).
Ltac rewr_from_true P := rewrite <- (prov_imp_iff_true P).

Tactic Notation "rewrite" "true"      constr(P) := rewr_to_true P.
Tactic Notation "rewrite" "->" "true" constr(P) := rewr_to_true P.
Tactic Notation "rewrite" "<-" "true" constr(P) := rewr_from_true P.

Tactic Notation "rewrite" "subst" constr(x) :=
  match goal with
  | [ |- context[x = ?y /\ ?e] ] => erewrite (in_and (x = y) e _);
        [> | intro; symmetry; instantiate (1 := ltac:(clear x)); subst x; reflexivity]
  end.

(* TODO: Generalize the pattern "generalize dependent x; rewrite indir_eq x" to a custom tactic that
   works for an arbitrary partial order *)

(* To showcase the derivational style, as well as the "Derive" extension,
   we demonstrate that S : nat -> nat has a left adjoint *)
Derive pred SuchThat (forall a b, pred a <= b <-> a <= S b)
  As pred_galois.
Proof. intros a b. destruct a.
  - rewrite true (le_0_n (S b)).
    rewrite <- true (le_0_n b).
    generalize dependent b.  rewrite indir_eq.
    instantiate (1 := ltac:(intro n; case n)) in (value of pred).
    simpl. reflexivity.
  - rewrite <- succ_le_mono.
    generalize dependent b. rewrite indir_eq.
    simpl. instantiate (1 := id).
    reflexivity.
Qed.

(* The derived function is then available in the global context,
as well as its specification *)
Compute (pred 0).
Compute (pred 5).
Check pred_galois.

(* Now, for a more complex example, we derive the recursive
   function take : forall X, nat -> list X -> list X *)

Require Import List.
Import ListNotations.

(* First we define inductively what it means for a list to be
   a prefix of another
*)
Inductive pref {X : Type} : list X -> list X -> Prop :=
  | pref_nil : forall xs, pref [] xs
  | pref_cons : forall x xs ys, pref xs ys -> pref (x::xs) (x::ys).

(* We will need a couple lemmas *)
Lemma len_le_zero_nil : forall {X} (xs: list X),
  length xs <= 0 <-> xs = [].
Proof. intros. split.
  - intro ev. inversion ev as [|H]. destruct xs; try discriminate.
    reflexivity.
  - intro. subst. reflexivity.
Qed.

Lemma pref_nil_nil : forall {X} (xs : list X), pref xs [] <-> xs = [].
Proof. intros. split.
  - intro ev. inversion ev. reflexivity.
  - intro. subst. constructor.
Qed.

Lemma pref_cons_iff : forall {X} xs y ys,
  pref xs (y::ys) <->
    xs = [] \/ exists (xs' : list X), xs = y :: xs' /\ pref xs' ys.
Proof. split.
  - intro h. inversion h; subst.
    + left. reflexivity.
    + right. exists xs0. split; easy. 
  - intros [nil | [xs' [cons pr]]].
    + subst xs. constructor.
    + subst xs. constructor. assumption.
Qed.

Lemma pref_antisymm : forall {X} (xs ys : list X),
  pref xs ys -> pref ys xs -> xs = ys.
Proof. intros. induction H.
  - rewrite pref_nil_nil in H0. symmetry. assumption.
  - f_equal. apply IHpref. inversion H0. subst. assumption.
Qed.

Lemma pref_refl : forall {X} (xs : list X), pref xs xs.
Proof. induction xs.
  - constructor. 
  - constructor. assumption.
Qed.

Lemma indir_eq_pref : forall {X} (a b : list X),
  (forall c, pref c a <-> pref c b) <-> a = b.
Proof. intros a b. split. 
  - intro H. apply pref_antisymm.
    + apply H. apply pref_refl.
    + symmetry in H. apply H. apply pref_refl.
  - intro. subst. easy.
Qed.

(* We are now ready for the derivation of take *)
Derive take SuchThat
  (forall {X} n (xs ys : list X), length xs <= n /\ pref xs ys
  <-> pref xs (take _ n ys))
  As take_galois.
Proof.
  intros X n. induction n; intros xs ys.
  - rewrite len_le_zero_nil.
    rewrite subst xs.
    rewrite true (pref_nil ys).
    rewrite true_neutral.
    rewrite <- pref_nil_nil.
    generalize dependent xs.  rewrite indir_eq_pref.
    instantiate (1 := fun X => fix rec (n : nat) (xs : list X) := _)
      in (value of take).
     instantiate (1 := ltac:(case n)) in (value of take).
     instantiate (1 := fun n' => let r := rec n' in _)
      in (value of take). (* technical hack *)
     simpl. reflexivity.
  - destruct ys.
    + rewrite pref_nil_nil.
      rewrite and_comm.
      rewrite subst xs.
      rewrite true (le_0_n (S n)). rewrite true_neutral.
      rewrite <- pref_nil_nil.
      generalize dependent xs. rewrite indir_eq_pref.
      simpl. instantiate (1 := ltac:(case xs)).
      simpl. reflexivity.
    + rewrite pref_cons_iff.
      rewrite and_or_distr. rewrite and_comm.
      rewrite subst xs.
      rewrite true (le_0_n (S n)). rewrite true_neutral.
      rewrite float_exists.
      setoid_rewrite <- and_assoc.
      setoid_rewrite (and_comm (length _ <= _) _).
      (* TODO: Improve rewrite subst to handle the case below *)
      (* rewrite subst xs. *)
      setoid_rewrite (fun x0 =>
        in_and (xs = x :: x0) (length xs <= S n) (S (length x0) <= S n)).
        2: intro; subst; reflexivity.
      setoid_rewrite <- succ_le_mono.
      setoid_rewrite and_assoc.
      setoid_rewrite IHn.
      rewrite <- pref_cons_iff.
      generalize dependent xs. rewrite indir_eq_pref.
      simpl. instantiate (1 := fun x ys => x :: r ys).
      reflexivity.
Qed.

Arguments take {x}.
Compute (take 5 [1; 3; 4; 1; 89; 18]).

(* Another interesting example is the function
   take_while : forall X, (X -> Bool) -> list X -> list X
 *)

Fixpoint All {X : Type} (P : X -> Prop) (xs : list X) : Prop :=
  match xs with
  | [] => True
  | x::xs => P x /\ All P xs
  end.

Derive take_while SuchThat
  (forall (X:Type) xs ys (p : X -> bool),
    All (fun x => p x = true) xs /\ pref xs ys
    <-> pref xs (take_while X p ys))
  As take_while_galois.
Proof.
  intros X xs ys p. generalize dependent xs. induction ys; intro xs.
  - rewrite pref_nil_nil.
    rewrite and_comm.
    rewrite subst xs.
    rewrite true I. rewrite true_neutral.
    rewrite <- pref_nil_nil.
    generalize dependent xs. rewrite indir_eq_pref.
    instantiate (1 := fun X p => fix rec (xs : list X) := _)
      in (value of take_while).
    instantiate (1 := ltac:(case xs)) in (value of take_while).
    simpl. reflexivity.
  - rewrite pref_cons_iff.
    rewrite and_or_distr.
    rewrite and_comm.
    rewrite subst xs.
    rewrite true I.
    rewrite true_neutral.
    rewrite float_exists.
    setoid_rewrite <- and_assoc.
    setoid_rewrite (and_comm (All _ xs) (xs = a :: _)).
    (* TODO: Improve rewrite subst to handle the case below *)
    setoid_rewrite (fun x => in_and (xs = a :: x) (All _ xs)
      (All (fun x0 => p x0 = true) (a :: x))).
      2: intro; subst; reflexivity.
    simpl. setoid_rewrite <- and_assoc.
    setoid_rewrite (and_comm (xs = _) (p a = true)).
    do 2 setoid_rewrite and_assoc.
    rewrite <- float_exists.
    setoid_rewrite IHys.
    rewrite or_and_distr.
    rewrite <- pref_cons_iff.
    destruct (p a) eqn:E.
    + rewrite true (ltac:(reflexivity) : true = true).
      rewrite true_absorb.
      rewrite and_comm. rewrite true_neutral.
      generalize dependent xs. rewrite indir_eq_pref.
      instantiate (1 := ltac:(intro a; case (p a))).
      simpl. rewrite E.
      instantiate (1 := fun ys => a :: rec ys).
      reflexivity.
    + simpl. rewrite E.
      assert (ne : false = true <-> False) by easy.
      rewrite ne. rewrite false_neutral.
      rewrite subst xs.
      rewrite true (pref_nil (a :: take_while X p ys)).
      rewrite true_neutral.
      rewrite <- pref_nil_nil.
      generalize dependent xs. rewrite indir_eq_pref.
      instantiate (1 := fun ys => _). reflexivity.
Qed.

Arguments take_while {x}.
Compute (take_while even [2; 4; 6; 8; 7; 4]).
Check take_while_galois.
