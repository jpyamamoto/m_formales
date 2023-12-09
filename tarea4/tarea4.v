(* Nueva táctica pues repito mucho el siguiente patrón. *)
Ltac casi_trivial := simpl; reflexivity.

(* Algunos lemas auxiliares que utilizo a lo largo de los ejercicios. *)
Section auxiliares.
  Lemma neutro_suma: forall n: nat, n + 0 = n.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.

  Lemma abre_suma: forall n m: nat, S (n + m) = n + S m.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.

  Lemma abre_suma_l : forall (n m : nat), S (n + m) = S n + m.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.

  Lemma suma_asocia: forall n m p: nat, n+(m+p)=(n+m)+p.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite IHn.
      trivial.
  Qed.

  Lemma min_cero : forall (m : nat), min m 0 = 0.
  Proof.
    intro.
    destruct m.
    all: casi_trivial.
  Qed.
End auxiliares.

(* Lemas del Ejercicio 1 *)
Section ejercicio1.

  Variables P Q R S : Prop.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros.
    apply H0.
    apply H.
    trivial.
  Qed.

  Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
  Proof.
    intros.
    destruct H0.
    destruct H.
    split.
    - apply H.
      trivial.
    - apply H2.
      trivial.
  Qed.

  Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
  Proof.
    intros.
    destruct H.
    destruct H.
    - contradict(H).
      trivial.
    - trivial.
  Qed.

End ejercicio1.

(* Lemas del Ejercicio 2 *)
Section ejercicio2.

  Variable a : Prop. (* Ana arresta a Juan. *)
  Variable c : Prop. (* Juan se casa con Benita. *)
  Variable b : Prop. (* Juan besa a Benita. *)
  Variable f : Prop. (* Ana fusila a Juan. *)

  Lemma vivira_juan : (a -> (* Si Ana arresta a Juan: *)
                        c (* Juan se casa con Benita *)
                        /\ b (* y la besa, *)
                        /\ (~c -> f) (* y si no se casa con Benita, Ana lo fusila. *)
                      )
                      -> (b -> ~f) (* Si Juan besa a Benita entonces Ana no lo fusila. *)
                      -> (a -> ~f). (* Por lo tanto si Ana arresta a Juan entonces no lo fusila *)
  Proof.
    intros.
    apply H0.
    destruct H.
    - trivial.
    - destruct H2.
      trivial.
  Qed.

End ejercicio2.

(* Lemas del Ejercicio 3 *)
Section ejercicio3.

  Lemma S1S: forall n:nat, n + 1 = S n.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite <- IHn.
      trivial.
  Qed.

  Lemma ConmSuma: forall n m: nat, n + m = m + n.
  Proof.
    intros.
    induction n.
    - simpl.
      rewrite neutro_suma.
      trivial.
    - simpl.
      rewrite IHn.
      rewrite abre_suma.
      trivial.
  Qed.

  Lemma MDistr: forall n m p: nat, n*(m+p)=n*m + n*p.
  Proof.
    intros.
    induction n.
    - casi_trivial.
    - simpl.
      rewrite IHn.
      rewrite (suma_asocia (m + n * m)).
      rewrite <- (suma_asocia m (n * m)).
      rewrite (ConmSuma (n * m) p).
      rewrite (suma_asocia m).
      rewrite suma_asocia.
      trivial.
  Qed.

End ejercicio3.

(* Definiciones y Lemas del Ejercicio 4 *)
Section ejercicio4.

  Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

  Fixpoint app {A : Type} (l m : list A) : list A :=
    match l with
      | (nil _)       => m
      | (cons _ a l1) => cons A a (app l1 m)
    end.

  Infix "++" := app (right associativity, at level 60).

  Fixpoint take {A : Type} (n : nat) (xs : list A) : list A :=
    match n, xs with
    | 0    , _            => nil A
    | _    , (nil _)      => nil A
    | S n' , (cons _ h t) => cons A h (take n' t)
    end.

  Fixpoint drop {A : Type} (n : nat) (xs : list A) : list A :=
    match n, xs with
    | 0   , _            => xs
    | _   , (nil _)      => nil A
    | S n', (cons _ _ t) => drop n' t
    end.

  Lemma drop_take_n {A : Type} : forall (xs : list A) (n : nat), drop n (take n xs) = nil A.
  Proof.
    intro xs.
    induction xs.
    - intros.
      destruct n.
      all: casi_trivial.
    - destruct n.
      + casi_trivial.
      + simpl. apply IHxs.
  Qed.

  Lemma take_nil {A : Type} : forall (n : nat), take n (nil A) = nil A.
  Proof.
    destruct n.
    all: casi_trivial.
  Qed.

  Lemma tdn {A : Type} : forall (xs : list A) (n : nat), xs = take n xs ++ drop n xs.
    induction xs.
    - destruct n.
      all: casi_trivial.
    - destruct n.
      + casi_trivial.
      + simpl.
        (* f_equal reduce la prueba a verificar que los elementos entrada a entrada del constructor sean iguales. *)
        (* Fuente: https://coq.inria.fr/refman/proofs/writing-proofs/equality.html#coq:tacn.f_equal *)
        f_equal.
        apply IHxs.
  Qed.

  Lemma ts {A : Type} : forall (xs : list A) (n m : nat), take m (drop n xs) = drop n (take (m+n) xs).
  Proof.
    induction xs.
    intros.
    - destruct n.
      all: destruct m; casi_trivial.
    - destruct n.
      + simpl.
        destruct m.
        * casi_trivial.
        * simpl. rewrite neutro_suma. trivial.
      + destruct m.
        * simpl.
          rewrite drop_take_n.
          trivial.
        * simpl.
          rewrite <- abre_suma.
          rewrite abre_suma_l.
          rewrite <- IHxs with n (S m).
          casi_trivial.
  Qed.

  Lemma min {A : Type} : forall (xs : list A) (n m : nat), take m (take n xs) = take (min m n) xs.
  Proof.
    induction xs.
    - intros.
      repeat rewrite take_nil.
      trivial.
    - destruct n, m.
      all: (casi_trivial || simpl; rewrite IHxs; reflexivity ).
  Qed.
End ejercicio4.
