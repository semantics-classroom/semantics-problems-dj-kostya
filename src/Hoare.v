Require Import List.
Import ListNotations.
Require Import Lia.

From hahn Require Import HahnBase.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr Stmt.

Definition assertion := state Z -> Prop.

Definition get_state (c : conf) : state Z :=
  match c with
  | (st, _, _) => st
  end.

Definition hoare_triple
           (P : assertion) (s : stmt) (Q : assertion) : Prop :=
  forall c c' (EXEC : c == s ==> c') (PP : P (get_state c)),
    Q (get_state c').

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition assn_sub x e P : assertion :=
  fun (st : state Z) =>
  exists v,
    << SVAL : [| e |] st => v >> /\
    << PP : P (st [ x <- v ]) >>.

Notation "P 'h[' x '<-' e ']'" := (assn_sub x e P)
  (at level 10, x at next level).

Lemma hoare_skip Q :
  {{ Q }} SKIP {{ Q }}.
  Proof. admit. Admitted.

Lemma hoare_assign Q x e:
  {{ Q h[x <- e] }} x ::= e {{ Q }}.
  Proof. admit. Admitted.

Definition assn_sub_example_P x st : Prop :=
  exists v,
    << XVAL : st / x => v >> /\
    << XLT  : Z.lt v (Z.of_nat 5) >>.

Example assn_sub_example x :
  {{ (assn_sub_example_P x) h[x <- (Var x) [+] (Nat 1)]}}
  x ::= ((Var x) [+] (Nat 1))
  {{ assn_sub_example_P x }}.
  Proof. admit. Admitted.

Lemma hoare_consequence_pre (P P' Q : assertion) s
      (HC : {{P'}} s {{Q}})
      (CONS : forall st (PP : P st), P' st) :
  {{P}} s {{Q}}.
  Proof. admit. Admitted.

Lemma hoare_consequence_post (P Q Q' : assertion) s
      (HC : {{P}} s {{Q'}}) (CONS : forall st (QQ : Q' st), Q st) :
  {{P}} s {{Q}}.
  Proof. admit. Admitted.

Lemma hoare_consequence (P P' Q Q' : assertion) s
      (HC : {{P'}} s {{Q'}})
      (PCONS : forall st (PP : P  st), P' st)
      (QCONS : forall st (QQ : Q' st), Q  st) :
  {{P}} s {{Q}}.
  Proof. admit. Admitted.

Lemma hoare_seq (P Q R : assertion) s s'
      (PQ : {{P}} s  {{Q}})
      (QR : {{Q}} s' {{R}}) :
  {{P}} s;;s' {{R}}.
  Proof. admit. Admitted.

Lemma hoare_if (P Q : assertion) e s s'
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s  {{Q}})
      (EL : {{fun st => P st /\ [| e |] st => 0 }} s' {{Q}}) :
  {{P}} COND e THEN s ELSE s' END {{Q}}.
  Proof. admit. Admitted.

Lemma hoare_while (P : assertion) e s
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s {{P}}) :
  {{P}} WHILE e DO s END {{fun st => P st /\ [| e |] st => 0 }}.
  Proof. admit. Admitted.

(* Coq is inconsistent with this axiom :) *)
Axiom state_extensionality :
  forall st st'
         (EXT : forall x, equivalent_states st st' x),
    st = st'.

Lemma hoare_assign_fwd x m e P :
  {{ fun st =>
       << PST   : P st >> /\
       << XVAL : st / x => m >> }}
    x ::= e
  {{ fun st =>
       exists v,
         << PST'  : P h[x <- (Nat m)] st >> /\
         << EVAL : [| e |] (st [x <- m]) => v  >> /\
         << VST  : st / x => v >> }}.
  Proof. admit. Admitted.

Module MultEx.
  Definition m := 0.
  Definition n := 1.
  Definition p := 2.
  Definition c := 3.
  Definition M := Var m.
  Definition N := Var n.
  Definition P := Var p.
  Definition C := Var c.

  Definition body :=
    (p ::= (P [+] M)) ;;
    (c ::= (C [+] (Nat 1))).

  Definition loop :=
    WHILE (C [<] N) DO
          body
    END.
  
  Lemma multSpec mv nv :
    {{ fun st =>
         << PINIT : st / p => 0%Z >> /\
         << CINIT : st / c => 0%Z >> /\
         << MINIT : st / m => mv >> /\
         << NINIT : st / n => nv >> /\
         << NPOS  : (nv >= 0)%Z >>
    }} loop {{
       fun st' =>
         << PVAL : st' / p => (mv * nv)%Z >>
    }}.
  Proof. admit. Admitted.
End MultEx.

Module FactorialEx.
  Definition x := 0.
  Definition y := 1.
  Definition X := Var x.
  Definition Y := Var y.

  Definition body :=
    (y ::= (X [*] Y)) ;;
    (x ::= (X [-] (Nat 1))).

  Definition loop :=
    WHILE (X [>] (Nat 0)) DO
          body
    END.
  
  Lemma factorialSpec n :
    {{ fun st =>
         << YINIT : st / y => (Z.of_nat 1) >> /\
         << XINIT : st / x => (Z.of_nat n) >>
    }} loop {{
       fun st' =>
         << YVAL : st' / y => (Z.of_nat (fact n)) >>
    }}.
  Proof. admit. Admitted.
End FactorialEx.

Module FastPowEx.
  Definition x := 0.
  Definition y := 1.
  Definition z := 2.
  Definition X := Var x.
  Definition Y := Var y.
  Definition Z := Var z.

  Definition body :=
    WHILE ((Y [%] (Nat 2)) [==] (Nat 0)) DO
          (x ::= (X [*] X)) ;;
          (y ::= (Y [/] (Nat 2)))
    END ;;
    (z ::= (Z [*] X)) ;;
    (y ::= (Y [-] (Nat 1))).

  Definition loop :=
    WHILE (Y [/=] (Nat 0)) DO
          body
    END.
  
  Lemma powerSpec m n :
    {{ fun st =>
         << XINIT : st / x => m >> /\
         << YINIT : st / y => n >> /\
         << ZINIT : st / z => 1%Z >>
    }} loop {{
       fun st' =>
         << ZVAL : st' / z => (m^n)%Z >>
    }}.
  Proof. admit. Admitted.
End FastPowEx.
  
