Require Import Arith Arith.EqNat.
Require Import Lia.

Definition id := nat.

(* Lemma zero_lt_s_nat:
forall i: nat, 0 < S i. 
Proof.
  intros.
  induction i.
  { auto. }
  {
    auto.
  }
  
Qed. *)
Locate lt_dec.
(* https://github.com/coq/coq/blob/v8.12/theories/Arith/Compare_dec.v *)
Lemma lt_eq_lt_id_dec (id1 id2 : id) :
  {id1 < id2} + {id1 = id2} + {id2 < id1}.
Proof. 
  generalize dependent id2.
  induction id1.
    { destruct id2; auto. repeat left. apply Nat.lt_0_succ. }
  intros id2.
  destruct id2.
  {right. apply Nat.lt_0_succ. }
  destruct (IHid1 id2) as [[AA|AA] | AA]; [repeat left | left; right | right ]; lia.
Qed.
  


Lemma gt_eq_gt_id_dec (id1 id2 : id):
  {id1 > id2} + {id1 = id2} + {id2 > id1}.
Proof. 
  destruct(lt_eq_lt_id_dec id1 id2 ) as [[AA|AA] | AA]; auto.
Qed.



Lemma le_gt_id_dec (id1 id2 : id): {id1 <= id2} + {id1 > id2}.
Proof. 
  destruct(lt_eq_lt_id_dec id1 id2 ) as [[AA|AA] | AA]; 
    auto; [apply Nat.lt_le_incl in AA | apply Nat.eq_le_incl in AA];auto.
Qed.

Lemma id_eq_dec (id1 id2 : id): {id1 = id2} + {id1 <> id2}.
Proof.
  destruct(lt_eq_lt_id_dec id1 id2 ) as [[AA|AA] | AA]; auto; right; apply Nat.le_neq in AA; inversion AA; auto.
Qed.

Lemma eq_id {T} x (p q:T):
  (if id_eq_dec x x then p else q) = p.
Proof. 
  destruct (id_eq_dec ); auto; contradiction.
Qed.

Lemma neq_id {T} x y (p q:T) (NEQ: x <> y):
  (if id_eq_dec x y then p else q) = q.
Proof. 
  destruct (id_eq_dec ); auto; contradiction.
Qed.

Lemma lt_gt_id_false (id1 id2 : id)
      (GT : id1 > id2) (GT': id2 > id1):
  False.
Proof. 
  destruct(lt_eq_lt_id_dec id1 id2 ) as [[AA|AA] | AA]; eapply gt_asym; eauto.
Qed.

Lemma le_gt_id_false (id1 id2 : id)
      (LE : id2 <= id1) (GT : id2 > id1) :
  False.
Proof. 
  destruct(le_gt_id_dec id1 id2) as [AA|AA]; eapply gt_asym; eauto; lia.
Qed.

Lemma le_lt_eq_id_dec (id1 id2 : id) (LE : id1 <= id2):
  {id1 = id2} + {id2 > id1}.
Proof. 
  destruct(lt_eq_lt_id_dec id1 id2)as [[AA|AA] | AA]; auto.
  apply Nat.lt_nge in AA. contradiction.  
Qed.

Lemma neq_lt_gt_id_dec (id1 id2 : id) (NEQ : id1 <> id2):
    {id1 > id2} + {id2 > id1}.
Proof. 
  destruct(gt_eq_gt_id_dec id1 id2) as [[AA|AA] | AA]; auto.
  contradiction.
Qed.
    
Lemma eq_gt_id_false (id1 id2 : id)
      (EQ : id1 = id2) (GT : id1 > id2) :
  False.
Proof. lia. Qed.
  

Lemma ne_symm (id1 id2 : id) (NEQ : id1 <> id2) : id2 <> id1.
Proof. lia. Qed.
