
(* This file contains Coq-HoTT code formulating the notion 

                 "cohesive infinity-topos"

   in the internal language of an infinity-topos.

   For background on cohesion see

     http://ncatlab.org/nlab/show/cohesive-(infinity,1)-topos

   For general background on Coq and homotopy type theory see
   
     http://ncatlabl.org/nlab/show/Coq
     http://ncatlabl.org/nlab/show/homotopy+type+theory

*)

(* ================================================================= *)
(* We speak in the internal language of an ambient infinity-topos H. *)
  Require Import Homotopy.
(* ================================================================= *)


(* ================================================================= *)
(* ==== Definition ================================================= *)
(* ================================================================= *)


(* A cohesive structure on an infinity-topos is a choice of full 
   subcategory that is embedded reflectively in two different, but 
   compatible ways. The first pieces of the following code are 
   therefore taken from

     ReflectiveSubcategory.v .

*)

(* There is a full subcategory of discrete objects... *)

  Parameter is_discrete : Type -> Type.

  Axiom is_discrete_is_prop : forall X, is_prop (is_discrete X).

  Axiom discrete_sum_of_discrete_is_discrete : forall X (P : X -> Type),
    is_discrete X -> (forall x, is_discrete (P x)) -> is_discrete (sigT P).

(* ...and one of codiscrete objects. *)

  Parameter is_codiscrete : Type -> Type.

  Axiom is_codiscrete_is_prop : forall X, is_prop (is_codiscrete X).

  Axiom codiscrete_sum_of_codiscrete_is_codiscrete : forall X (P : X -> Type),
    is_discrete X -> (forall x, is_discrete (P x)) -> is_discrete (sigT P).

(* The discrete objects objects are internally reflective... *)

  Parameter pi : Type -> Type.

  Parameter map_to_pi : forall X, X -> pi X.

  Axiom pi_is_discrete : forall X, is_discrete (pi X).

  Axiom pi_is_reflection : forall X Y, is_discrete Y -> 
    is_equiv (fun f: pi X -> Y => f o (map_to_pi X)).

(* ... as are the codiscrete objects. *)

  Parameter sharp : Type -> Type.

  Parameter map_to_sharp : forall X, X -> sharp X.

  Axiom sharp_is_codiscrete : forall X, is_codiscrete (sharp X).

  Axiom sharp_is_reflection : forall X Y, is_codiscrete Y -> 
    is_equiv (fun f: sharp X -> Y => f o (map_to_sharp X)).


(* With the two reflective subcategories defined, the remaining
   axiom to impose is that sharp exhibits an equivalence between them. *)

(* Name the two subcategories. *)

  Definition DiscType : Type := 
    sigT is_discrete.

  Definition coDiscType : Type := 
    sigT is_codiscrete.

(* Restrict sharp to a map between the two. *)

  Definition sharp_on_discrete : DiscType -> coDiscType :=
    (fun f =>  
      existT
       is_codiscrete
       ( sharp (projT1 f) )  
       ( sharp_is_codiscrete ( (projT1 f) ) ) 
    ).

(* This map is to exhibit an equivalence between the two *)

  Axiom discrete_is_equivalent_to_codiscrete :
    is_equiv sharp_on_discrete.

  

