Require Import Arith.
Require Import Lia.
Require Import Bool.
Import Nat Peano.

Ltac bdestr X H :=
  let e := fresh "e" in
   evar (e : Prop);
   assert (H : reflect e X); subst e;
    [ eauto with bdestruct
    | destruct H as [H | H];
       [ | try first [apply nlt_ge in H | apply nle_gt in H]]].

Tactic Notation "bdestruct" constr(X) := let H := fresh in bdestr X H.

Tactic Notation "bdestruct" constr(X) "as" ident(H) := bdestr X H.

(* Шагов М., Власов М.
   Проект № 3.
   Определить, встречается ли число в двумерном массиве. *)

Section ArraySearch.

(* Одномерный массив *)
Variable array: nat -> nat.

(* Функция search1
   Возвращает true, если среди первых n+1 элементов массива array присутствует
   значение target, в противном случае возвращает false *)
Fixpoint search1 (n target: nat) : bool :=
  match n with
  (* eqb : nat -> nat -> bool
     Выводится в true, если значения равны, иначе false *)
  | 0 => eqb (array 0) target
  | S k => if eqb (array n) target then true else search1 k target
  end.

(* Спецификация search1_spec для search1 
   Доказывает, что search1 возвращает true для заданных n и target тогда и только
   тогда, когда среди первых n+1 элементов массива array присутствует target *)
Theorem search1_spec : forall (n target : nat),
  search1 n target = true <-> exists i, i <= n /\ array i = target.
Proof.
  induction n as [|n' IH]; intros target.
  - split.
    + intros H.
      exists 0.
      split.
      * lia.
      (* eqb_eq : forall n m : nat, (n =? m) = true <-> n = m *)
      * apply eqb_eq.
        assumption.
    + intros [i [Hi Hval]].
      assert (i = 0) by lia.
      subst. 
      apply eqb_eq.
      reflexivity.
  - split.
    + intros H.
      simpl in H.
      (* Следующая тактика destruct разделяет if с указанным условием
         на две цели, для одной из которых условие полагается равным
         true, а для другой - false, в посылку Heqb *)
      destruct (eqb (array (S n')) target) eqn:Heqb.
      * exists (S n').
        split.
        -- lia.
        -- apply eqb_eq.
           assumption.
      (* eqb_neq : forall x y : nat, (x =? y) = false <-> x <> y *)
      * apply eqb_neq in Heqb.
        apply IH in H.
        destruct H as [i [Hi Hval]].
        exists i.
        split.
        -- lia.
        -- assumption.
    + intros [i [Hi Hval]].
      simpl.
      destruct (eqb (array (S n')) target) eqn:Heqb.
      * reflexivity.
      * apply eqb_neq in Heqb.
        apply IH.
        exists i.
        (* Следующая тактика assert производит две цели в соответствии
           с указанными дизъюнктами в посылку Hi' *)
        assert (i <= n' \/ i = S n') as [Hi' | Hi'] by lia.
        -- split; assumption.
        -- split.
          ++ subst i.
             contradiction.
          ++ assumption.
Qed.

End ArraySearch.

Section ArraySearch2D.

Variable array : nat -> nat.

(* Двумерный массив *)
Variable array2D : nat -> nat -> nat.

(* Функция search2
   Возвращает true, если среди элементов первых rows+1 строк и cols+1 столбцов
   массива array2D присутствует значение target
   В противном случае возвращает false *)
Fixpoint search2 (rows cols target: nat) : bool :=
match rows with
| 0 => search1 (array2D 0) cols target
| S r => if search1 (array2D rows) cols target then true else search2 r cols target
end.

(* Лемма diffIndices2D
   Доказывает, что из неравенства значений по индексам (i0, j) и (i1, j) в массиве
   array2D следует неравенство индексов i0 и i1 *)
Lemma diffIndices2D : forall (i0 i1 j : nat),
  array2D i0 j <> array2D i1 j -> i0 <> i1.
Proof.
  intros.
  unfold not.
  intros.
  subst.
  contradiction.
Qed.

(* Лемма search1in2DFalse
   Доказывает, что если значение target отсутствует среди значений первых i+1
   строк и j+1 столбцов, то значение в i+1-й строке и j+1-м столбце не может
   совпадать с target *)
Lemma search1in2DFalse : forall (i j target : nat),
  search1 (array2D i) j target = false -> (array2D i) j <> target.
Proof.
  intros i j target H.
  destruct j.
  - simpl in H.
    apply eqb_neq in H.
    assumption.
  - simpl in H.
    destruct ((array2D i (S j)) =? target) eqn:H2.
    + lia.
    + apply eqb_neq in H2.
      assumption.
Qed.

(* Лемма search1in2DtrueIfKnown
   Доказывает, что если известно положение значения target в массиве, то поиск
   target по индексам вплоть до индексов target вернет true *)
Lemma search1in2DtrueIfKnown: forall (i j target: nat),
  array2D i j = target -> search1 (array2D i) j target = true.
Proof.
  intros.
  induction j.
  - simpl.
    rewrite H.
    apply eqb_eq.
    lia.
  - simpl.
    rewrite H.
    destruct (eqb_spec (array2D i (S j)) target).
    + destruct (target =? target) eqn:Heqb.
      * lia.
      (* EqNat.beq_nat_false_stt
         forall n m : nat, (n =? m) = false -> n <> m *)
      * apply EqNat.beq_nat_false_stt in Heqb.
        lia.
    + lia.
Qed.

(* Лемма search1in2DfalseInPart
   Доказывает, что если значение target не было найдено среди первых j2+1
   столбцов массива array2D, то оно не может быть найдено среди меньшего числа
   столбцов в этом массиве при неизменном количестве строк *)
Lemma search1in2DfalseInPart: forall (i j1 j2 target: nat),
  j1 <= j2 /\ search1 (array2D i) j2 target = false -> search1 (array2D i) j1 target = false.
Proof.
  intros i j1 j2 target [Hle Hsearch2].
  revert j1 Hle.
  induction j2 as [| j2' IH].
  - intros j1 Hle.
    inversion Hle.
    + subst.
      * auto.
  - intros j1 Hle.
    simpl in Hsearch2.
    destruct (eqb (array2D i j2') target) eqn:Heq.
    + destruct ((array2D i (S j2')) =? target) eqn:Heqb.
      * lia.
      * apply search1in2DFalse in Hsearch2.
        apply eqb_eq in Heq.
        lia.
    + destruct ((array2D i (S j2')) =? target) eqn:Heqb.
      * lia.
      * assert (j1 = S j2' \/ j1 <= j2') as [Hi | Hi] by lia.
        -- subst j1.
           simpl.
           destruct ((array2D i (S j2')) =? target) eqn:Heqb2.
           ++ lia.
           ++ assumption.
        -- apply IH.
           ** assumption.
           ** assumption.
Qed.

(* Спецификация search2_spec для search2
   Доказывает, что search2 возвращает true для заданных rows, cols и target
   тогда и только тогда, когда среди значений первых rows+1 строк и cols+1
   столбцов массива array2D присутствует target *)
Theorem search2_spec : forall (rows cols target : nat),
  search2 rows cols target = true <-> exists i j, i <= rows /\ j <= cols /\ array2D i j = target.
Proof.
  induction rows as [|r IH]; intros cols target.
  - split.
    + intros H.
      apply search1_spec in H.
      destruct H as [j [Hj Hval]].
      exists 0, j.
      split; [lia | split; assumption].
    + intros [i [j [Hi [Hj Hval]]]].
      assert (i = 0) by lia.
      subst i.
      apply search1_spec.
      exists j.
      split; assumption.
  - split.
    + intros H.
      simpl in H.
      destruct (search1 (array2D (S r)) cols target) eqn:Heqb.
      * apply search1_spec in Heqb.
        destruct Heqb as [j [Hj Hval]].
        exists (S r), j.
        split; [lia | split; assumption].
      * apply IH in H.
        destruct H as [i [j [Hi [Hj Hval]]]].
        exists i, j.
        split; [lia | split; assumption].
    + intros [i [j [Hi [Hj Hval]]]].
      assert (i = S r \/ i <= r) as [Hi' | Hi'] by lia.
      * subst i.
        simpl.
        destruct (search1 (array2D (S r)) cols target) eqn:Heqb.
        -- lia.
        -- apply search1in2DtrueIfKnown in Hval.
           assert (j <= cols /\ search1 (array2D (S r)) cols target = false).
           split; assumption.
           apply search1in2DfalseInPart in H.
           rewrite Hval in H.
           lia.
      * simpl.
        destruct (search1 (array2D (S r)) cols target) eqn:Heqb.
        -- lia.
        -- apply IH.
           exists i, j.
           split.
           ++ assumption.
           ++ split; assumption.
Qed.

End ArraySearch2D.

Section Test.

Variable undef : nat.

(* Протестируем функцию search1 для одномерного массива array1 *)

Definition array1 (n : nat) : nat :=
match n with
| 0 => 5
| 1 => 7
| 2 => 2
| 3 => 1
| 4 => 0
| 5 => 2
| _ => undef
end.

Compute search1 array1 5 2.
Compute search1 array1 5 5.
Compute search1 array1 3 0.

(* Протестируем функцию search2 для двумерного массива array2 *)

Definition array2 (i j : nat) : nat :=
match i, j with
| 0, 0 => 5
| 0, 1 => 7
| 0, 2 => 2
| 1, 0 => 1
| 1, 1 => 0
| 1, 2 => 2
| _, _ => undef
end.

Compute search2 array2 1 2 2.
Compute search2 array2 1 2 5.
Compute search2 array2 0 2 0.

End Test.
