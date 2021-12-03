Require Import List.
Import ListNotations.

Require Import BinInt ZArith_dec.
Require Export Id State Expr.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf),
    c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
    (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
    c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.one)
                     (STEP : (s, i, o) == s1 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.zero)
                     (STEP : (s, i, o) == s2 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
    (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
    (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Lemma  bs_equivalent_refl (s1 s2: stmt) :
    s1 ~~~ s2 <-> s2 ~~~ s1
.
Proof.
  split; intros; split; intros;apply H; eauto.
Qed.


Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    red. split; intros; seq_inversion; seq_inversion; seq_apply STEP1.
  Qed.

  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. red. split; intros.
    {
      (* inv H; constructor; eauto; try seq_apply. *)
      inv H.
      { 
        constructor; eauto. seq_apply.
      }
      inv H. 
      eapply eval_deterministic with (z1:= Z.zero) in CVAL0.
      2: { apply CVAL. }
      { inv CVAL0. }
      apply bs_If_False; eauto.
      constructor.      
    }
    inv H.
    {
     seq_inversion.
    eapply bs_While_True; eauto.
    }
    inv STEP.
    eapply bs_While_False; eauto.
  Qed.

  
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END ).
    remember ((st, i, o)).
    generalize dependent e.
    generalize dependent st.
    induction EXE; intros; try by (inv Heqs0; eauto).
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.  red. split; intros.
    { 
      remember(WHILE Nat 1 DO SKIP END).
      induction H; eauto; inv Heqs; try by inv CVAL.
      inv H; apply IHbs_int2; eauto.
    }
    remember(COND Nat 3 THEN SKIP ELSE SKIP END).
    induction H; eauto; inv Heqs; inv CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    red. intros. split; intros.
    {
      remember (WHILE e DO s1 END). 
    induction H; try by inv Heqs; red in EQ.
    all : inv Heqs;econstructor; eauto; eapply EQ; eauto.
    }
    remember (WHILE e DO s2 END). 
    induction H; try by inv Heqs; red in EQ.
    all : inv Heqs;econstructor; eauto; eapply EQ; eauto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    red. intros.
    remember (WHILE Nat 1 DO s END ).
    induction H; eauto; inv Heqs0.
    inv CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. split; intros; inv H; apply EQ in STEP2; seq_apply.
Qed.
  


Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. split; intros; inv H; apply EQ in STEP1; seq_apply.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. split; intros; inv H; try by (apply bs_If_True; eauto).
  all : apply bs_If_False; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. split; intros; inv H; try by (apply bs_If_False; eauto).
  all : apply bs_If_True; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. split; intros;  try by (inv H; apply bs_While_False; eauto).
  {
    remember (WHILE e DO s1 END).
    generalize dependent e.
    induction H; intros; inv Heqs0.
    {
      apply EQ in H.  eapply bs_While_True with (c' := c'); eauto.
    }
    eapply bs_While_False; eauto.
  }
  remember (WHILE e DO s2 END);  generalize dependent e.
  induction H; intros; inv Heqs0.
    {
      apply EQ in H.  eapply bs_While_True with (c' := c'); eauto.
    }
    eapply bs_While_False; eauto.
Qed.
  

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof. split.
  { apply eq_congruence_seq_r; eauto. }
  split.  apply eq_congruence_seq_l; eauto.
  split. apply eq_congruence_cond_else; eauto.
  split. apply eq_congruence_cond_then; eauto.
  apply eq_congruence_while; eauto.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  remember s.
  generalize dependent s.
  generalize dependent c.
  generalize dependent c1.
  generalize dependent c2.
  (* induction s; intros.  *)

  induction s0; intros.
  all: try by (inv EXEC1; inv EXEC2; try reflexivity; try by_eval_deterministic).

  all: try by (inv EXEC1; inv EXEC2;
    eapply IHs0_1 with (c1:= c'0) (s:= s0_1) in STEP1; eauto; subst;
    eapply IHs0_2 with (c1:= c2) (s:= s0_2) in STEP2; eauto; subst).
  
  {
    inv EXEC1; inv EXEC2. 
    eapply IHs0_1 with (c:= (s0, i, o)) (c1:=c2) in STEP; eauto; subst.
    all: try eval_zero_not_one.
    eapply IHs0_2 with (c:= (s0, i, o)) (c1:=c2) in STEP; eauto; subst.
  }

  
  remember (WHILE e DO s0 END).
  generalize dependent e.
  generalize dependent s0.
  induction EXEC1; intros; eauto; inv Heqs1; inv EXEC2;  try by eval_zero_not_one.
  eapply IHEXEC1_2.
  eapply IHs0 with (c1:= c') in STEP; subst; eauto.
  reflexivity.
  apply IHs0.
  apply Heqs1.
Qed.


(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~~~ (C <~ s2).
Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2)
                            (at level 42, no associativity).



(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof. split; intros.
  {
    
    split; intros.
    {
      generalize dependent c.
      generalize dependent c'.
      generalize dependent s1.
      generalize dependent s2.
      induction C; intros; simpls.
      all: try by (eapply H; auto).
      all: try by (seq_inversion;
      try eapply IHC in STEP1;
      try eapply IHC in STEP2; eauto;
      seq_apply).
      1: eapply eq_congruence_cond_then; eauto.
      2: eapply eq_congruence_cond_else; eauto.
      3: eapply eq_congruence_while; eauto.
      all: 
        split; intros ;
          eapply IHC in H1; eauto;
          apply bs_equivalent_refl; eauto.
    }
    generalize dependent c.
    generalize dependent c'.
    generalize dependent s1.
    generalize dependent s2.
    induction C; intros; simpls.
    all: try by (eapply H; auto).
    all: try by (seq_inversion;
    try eapply IHC in STEP1;
    try eapply IHC in STEP2; eauto;
    seq_apply).
    1: eapply eq_congruence_cond_then; eauto.
    2: eapply eq_congruence_cond_else; eauto.
    3: eapply eq_congruence_while; eauto.
    all: 
      split; intros ;
        eapply IHC in H1; eauto;
        apply bs_equivalent_refl; eauto.
  }
  red. split; intros; red in H; apply (H Hole );
  simpl; eauto.
Qed.

