Require Import Utf8.
Require Import Bool.
Require Import Nat.
Require Import Arith.

(* ==================== Values ==================== *)

Inductive Value : Type :=
| V_Int (n:nat)
| V_Pair (l:Value) (r:Value)
.

Notation "{ x , y }" := (V_Pair x y).
Notation "x '" := (V_Int x)
                    (at level 30).

(* ==================== Types ==================== *)

Inductive SemType : Type :=
| T_Int
| T_Pair (l:SemType) (r:SemType)
.

Notation "x × y" := (T_Pair x y)
                      (at level 40).

(* ==================== Semantics ==================== *)

Fixpoint bmember_of (v:Value) (t:SemType) : bool :=
  match (v,t) with
  | (V_Int _,T_Int) => true
  | ( { vl, vr }, tl×tr) =>
      (bmember_of vl tl) && (bmember_of vr tr)
  | (_,_) => false
  end.

Definition member_of (v:Value) (t:SemType) : Prop :=
  (bmember_of v t) = true.

Notation "x ∈ y" := (member_of x y)
                       (at level 50).

Notation "x ∉ y" := (¬(member_of x y))
                      (at level 50).

Example zero_t_int: 0' ∈ T_Int.
Proof.
  reflexivity.
Qed.

Example zero_t_nint: 0' ∉ (T_Int×T_Int).
Proof.
  discriminate.
Qed.

Example zero_t_pair: {0', 1'} ∈ T_Int×T_Int.
Proof.
  reflexivity.
Qed.

Lemma memberof_int : forall (n:nat) (t1:SemType),
    (V_Int(n) ∈ t1) -> (t1 = T_Int).
Proof.
  intros n t1 eq.
  destruct t1.
  -- reflexivity.
  -- discriminate.
Qed.

Lemma memberof_pair : forall (v1:Value) (v2:Value) (t3:SemType),
    ({v1,v2} ∈ t3) -> exists (t1:SemType) (t2:SemType), (t3 = t1×t2 /\ v1 ∈ t1 /\ v2 ∈ t2).
Proof.
  intros v1 v2 t3 I1.
  destruct t3.
  - discriminate.
  - eexists.
    eexists.
    split.
    -- reflexivity.
    -- unfold member_of in I1.
       unfold bmember_of in I1.
       fold bmember_of in I1.
       unfold member_of.
       apply andb_true_iff in I1.
       apply I1.
Qed.
       
(* ==================== Subtyping ==================== *)

Fixpoint bsubtype_of (t1:SemType) (t2:SemType) : bool :=
  match (t1,t2) with
  | (T_Int, T_Int) => true
  | (t11×t12, t21×t22) => (bsubtype_of t11 t21) && (bsubtype_of t12 t22)
  | (_,_) => false
  end.

Definition subtype_of (t1:SemType) (t2:SemType) : Prop :=
  (bsubtype_of t1 t2) = true.

Notation "x <: y" := (subtype_of x y)
                       (at level 50).

(* Subtyping an int implies an int (for now) *)
Lemma subtypeof_int : forall (t2:SemType),
    (T_Int <: t2) -> (t2 = T_Int).
Proof.
  intros t1 S1.
  unfold subtype_of in S1.
  unfold bsubtype_of in S1.
  destruct t1.
  -- reflexivity.
  -- discriminate.
Qed.

(* Subtyping of pairs implies subtyping of their elements *)
Lemma subtypeof_pair1 : forall (t1:SemType) (t2:SemType) (t3:SemType) (t4:SemType),
    (t1×t2 <: t3×t4) -> (t1 <: t3) /\ (t2 <: t4).
Proof.
  intros t1 t2 t3 t4 S1.
  unfold subtype_of in S1.
  unfold bsubtype_of in S1.
  fold bsubtype_of in S1.  
  apply andb_true_iff in S1.
  destruct S1 as [S2 S3].
  split.
  - apply S2.
  - apply S3.
Qed.
  
(* Subtyping a pair requires a pair *)
Lemma subtypeof_pair2 : forall (t1:SemType) (t2:SemType) (t3:SemType),
    (t1×t2 <:t3) -> exists (t4:SemType) (t5:SemType), t3 = t4×t5.
Proof.
  intros t1 t2 t3 S1.
  unfold subtype_of in S1.
  unfold bsubtype_of in S1.
  fold bsubtype_of in S1.
  destruct t3.
  - discriminate.
  - eexists.
    eexists.
    reflexivity.
Qed.

(* ==================== Soundness ==================== *)

Lemma subtype_soundness : forall (t1:SemType) (t2:SemType) (v1:Value),
    (t1 <: t2) -> (v1 ∈ t1) -> (v1 ∈ t2).
Proof.
  intros t1 t2 v1 S1 I1.
  destruct v1.
  -- apply memberof_int in I1.
     rewrite -> I1 in S1.
     apply subtypeof_int in S1.
     rewrite -> S1.
     unfold member_of.
     unfold bmember_of.
     reflexivity.
  -- admit.
Admitted.
  
(* ==================== Completeness ==================== *)

Lemma subtype_completeness : forall (t1:SemType) (t2:SemType) (v1:Value),
    (v1 ∈ t1) -> (v1 ∈ t2) -> (t1 <: t2).
Proof.
Admitted.





  
  
                        


