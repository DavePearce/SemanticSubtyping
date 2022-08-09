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

(* ==================== Soundness ==================== *)

Lemma subtype_soundness : forall (t1:SemType) (t2:SemType) (v1:Value),
    (t1 <: t2) -> (v1 ∈ t1) -> (v1 ∈ t2).
Proof.
Admitted.





  
  
                        


