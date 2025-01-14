Require Export Paths Fibrations Contractible.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** An equivalence is a map whose homotopy fibers are contractible. *)

Definition is_equiv {A B} (f : A -> B) := forall y : B, is_contr (hfiber f y).

(** [equiv A B] is the space of equivalences from [A] to [B]. *)

Definition equiv A B := { w : A -> B & is_equiv w }.

Notation "A <~> B" := (equiv A B) (at level 55).

(** printing <~> $\overset{\sim}{\longrightarrow}$ *)

(** Strictly speaking, an element [w] of [A <~> B] is a _pair_
   consisting of a map [projT1 w] and the proof [projT2 w] that it is
   an equivalence. Thus, in order to apply [w] to [x] we must write
   [projT1 w x]. Coq is able to do this automatically if we declare
   that [projT1] is a _coercion_ from [equiv A B] to [A -> B]. *)

Definition equiv_coerce_to_function A B (w : A <~> B) : (A -> B)
  := projT1 w.

Coercion equiv_coerce_to_function : equiv >-> Funclass.

(** Here is a tactic which helps us prove that a homotopy fiber is
   contractible.  This will be useful for showing that maps are
   equivalences. *)

Ltac contract_hfiber y p :=
  match goal with
    | [ |- is_contr (@hfiber _ _ ?f ?x) ] =>
      eexists (existT (fun z => f z == x) y p);
        let z := fresh "z" in
        let q := fresh "q" in
          intros [z q]
  end.

(** Let us explain the tactic. It accepts two arguments [y] and [p]
   and attempts to contract a homotopy fiber to [existT _ y p]. It
   first looks for a goal of the form [is_contr (hfiber f x)], where
   the question marks in [?f] and [?x] are pattern variables that Coq
   should match against the actual values. If the goal is found, then
   we use [eexists] to specify that the center of retraction is at the
   element [existT _ y p] of hfiber provided by the user. After that
   we generate some fresh names and perfrom intros. *)

(** The identity map is an equivalence. *)

Definition idequiv A : A <~> A.
Proof.
  intro A.
  exists (idmap A).
  intros x.
  contract_hfiber x (idpath x).
  apply total_path with (p := q).
  simpl.
  compute in q.
  path_induction.
Defined.

(** From an equivalence from [U] to [V] we can extract a map in the
   inverse direction. *)

Definition inverse {U V} (w : U <~> V) : (V -> U) :=
  fun y => pr1 (pr1 ((pr2 w) y)).

Notation "w ^-1" := (inverse w) (at level 40).

(** printing ^-1 $^{-1}$ *)

(** The extracted map in the inverse direction is actually an inverse
   (up to homotopy, of course). *)

Definition inverse_is_section {U V} (w : U <~> V) y : w (w^-1 y) == y :=
  pr2 (pr1 ((pr2 w) y)).

Definition inverse_is_retraction {U V} (w : U <~> V) x : (w^-1 (w x)) == x :=
  !base_path (pr2 ((pr2 w) (w x)) (x ; idpath (w x))).

(** Here are some tactics to use for canceling inverses, and for
   introducing them. *)

Ltac cancel_inverses_in s :=
  match s with
    | context cxt [ equiv_coerce_to_function _ _ ?w (?w ^-1 ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_section
    | context cxt [ ?w ^-1 (equiv_coerce_to_function _ _ ?w ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_retraction
  end.

Ltac cancel_inverses :=
  repeat progress (
    match goal with
      | |- ?s == ?t => first [ cancel_inverses_in s | cancel_inverses_in t ]
    end
  ).

Ltac expand_inverse_src w x :=
  match goal with
    | |- ?s == ?t =>
      match s with
        | context cxt [ x ] =>
          first [
            let mid := context cxt [ w (w^-1 x) ] in
              path_via' mid;
              [ path_simplify' inverse_is_section | ]
            |
            let mid := context cxt [ w^-1 (w x) ] in
              path_via' mid;
              [ path_simplify' inverse_is_retraction | ]
          ]
      end
  end.

Ltac expand_inverse_trg w x :=
  match goal with
    | |- ?s == ?t =>
      match t with
        | context cxt [ x ] =>
          first [
            let mid := context cxt [ w (w^-1 x) ] in
              path_via' mid;
              [ | path_simplify' inverse_is_section ]
            |
            let mid := context cxt [ w^-1 (w x) ] in
              path_via' mid;
              [ | path_simplify' inverse_is_retraction ]
          ]
      end
  end.

(** These tactics change between goals of the form [w x == y] and the
   form [x == w^-1 y], and dually. *)

Ltac equiv_moveright :=
  match goal with
    | |- equiv_coerce_to_function _ _ ?w ?a == ?b =>
      apply @concat with (y := w (w^-1 b));
        [ apply map | apply inverse_is_section ]
    | |- (?w ^-1) ?a == ?b =>
      apply @concat with (y := w^-1 (w b));
        [ apply map | apply inverse_is_retraction ]
  end.

Ltac equiv_moveleft :=
  match goal with
    | |- ?a == equiv_coerce_to_function _ _ ?w ?b =>
      apply @concat with (y := w (w^-1 a));
        [ apply opposite, inverse_is_section | apply map ]
    | |- ?a == (?w ^-1) ?b =>
      apply @concat with (y := w^-1 (w a));
        [ apply opposite, inverse_is_retraction | apply map ]
  end.

(** This is one of the "triangle identities" for the preceeding two
   homotopies.  (It doesn't look like a triangle since we've inverted
   one of the homotopies.) *)

Definition inverse_triangle {A B} (w : A <~> B) x :
  (map w (inverse_is_retraction w x)) == (inverse_is_section w (w x)).
Proof.
  intros.
  unfold inverse_is_retraction.
  do_opposite_map.
  apply (concat (!idpath_right_unit _ _ _ _)).
  moveright_onleft.
  apply opposite.
  exact (hfiber_triangle (pr2 (pr2 w (w x)) (x ; idpath _))).
Defined.


(** Equivalences are "injective on paths". *)

Lemma equiv_injective U V (w : U <~> V) x y : (w x == w y) -> (x == y).
Proof.
  intros U V w x y.
  intro p.
  expand_inverse_src w x.
  equiv_moveright.
  assumption.
Defined.

(** Anything contractible is equivalent to the unit type. *)

Lemma contr_equiv_unit (A : Type) :
  is_contr A -> (A <~> unit).
Proof.
  intros A H.
  exists (fun x => tt).
  intro y. destruct y.
  contract_hfiber (pr1 H) (idpath tt).
  apply @total_path with (p := pr2 H z).
  apply contr_path2.
  auto.
Defined.

(** And conversely, anything equivalent to a contractible type is
   contractible. *)

Lemma contr_equiv_contr (A B : Type) :
  A <~> B -> is_contr A -> is_contr B.
Proof.
  intros A B f Acontr.
  destruct Acontr.
  exists (f x).
  intro y.
  equiv_moveleft.
  apply p.
Defined.

(** The free path space of a type is equivalent to the type itself. *)

Definition free_path_space A := {xy : A * A & fst xy == snd xy}.

Definition free_path_source A : free_path_space A <~> A.
Proof.
  intro A.
  exists (fun p => fst (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x,x) (idpath x)) _).
  intros [[[u v] p] q].
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

Definition free_path_target A : free_path_space A <~> A.
Proof.
  intro A.
  exists (fun p => snd (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x,x) (idpath x)) _).
  intros [[[u v] p] q].
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

(** We have proven that every equivalence has an inverse up to
    homotopy.  In fact, having an inverse up to homotopy is also
    enough to characterize a map as being an equivalence.  However,
    the data of an inverse up to homotopy is not equivalent to the
    data in [is_equiv] unless we add one more piece of coherence data.
    This is a homotopy version of the category-theoretic notion of
    "adjoint equivalence". *)

Definition is_adjoint_equiv {A B} (f : A -> B) :=
  { g : B -> A &
    { is_section : forall y, (f (g y)) == y &
      { is_retraction : forall x, (g (f x)) == x &
        forall x, (map f (is_retraction x)) == (is_section (f x))
          }}}.

Definition is_equiv_to_adjoint {A B} (f: A -> B) (E : is_equiv f) : is_adjoint_equiv f :=
  let w := (f ; E) in
    (w^-1 ; (inverse_is_section w; (inverse_is_retraction w ; inverse_triangle w))).

Definition adjoint_equiv (A B : Type) := { f: A -> B  &  is_adjoint_equiv f }.

Theorem is_adjoint_to_equiv {A B} (f: A -> B) : is_adjoint_equiv f -> is_equiv f.
Proof.
  intros A B f [g [is_section [is_retraction triangle]]].
  intro y.
  contract_hfiber (g y) (is_section y).
  apply (total_path _
    (fun x => f x == y)
    (existT _ z q)
    (existT _ (g y) (is_section y))
    (!is_retraction z @ (map g q))).
  simpl.
  path_via (!(map f (!is_retraction z @ map g q)) @ q).
  apply transport_hfiber.
  do_concat_map.
  do_opposite_map.
  undo_opposite_concat.
  (** Here is where we use triangle. *)
  path_via (!map f (map g q) @ is_section (f z) @ q).
  (** Now it's just naturality of 'is_section'. *)
  associate_right.
  moveright_onleft.
  undo_compose_map.
  apply opposite, homotopy_naturality_toid with (f := f o g).
Defined.

(** Probably equiv_to_adjoint and adjoint_to_equiv are actually
   inverse equivalences, at least if we assume function
   extensionality. *)

Lemma equiv_pointwise_idmap A (f : A -> A) (p : forall x, f x == x) : is_equiv f.
Proof.
  intros.
  apply is_adjoint_to_equiv.
  exists (idmap A).
  exists p.
  exists p.
  apply htoid_well_pointed.
Defined.

(** A central fact about adjoint equivalences is that any "incoherent"
   equivalence can be improved to an adjoint equivalence by changing
   one of the natural isomorphisms.  We now prove a corresponding
   result in homotopy type theory.  The proof is exactly the same as
   the usual proof for adjoint equivalences in 2-category theory.  *)

Definition adjointify {A B} (f : A -> B) (g : B -> A) :
  (forall y, f (g y) == y) -> (forall x, g (f x) == x ) ->
  is_adjoint_equiv f.
Proof.
  intros A B f g is_section is_retraction.
  (* We have to redefine one of the two homotopies. *)
  set (is_retraction' := fun x =>
    ( map g (map f (!is_retraction x)))
    @ (map g (is_section (f x)))
    @ (is_retraction x)).
  exists g.
  exists is_section.
  exists is_retraction'.
  intro x.
  (** Now we just play with naturality until things cancel. *)
  unfold is_retraction'.
  do_concat_map.
  undo_compose_map.
  moveleft_onleft.
  associate_left.
  path_via ((!is_section (f x)  @  map (f o g) (map f (!is_retraction x))
    @  map (f o g) (is_section (f x)))  @  map f (is_retraction x)).
  unwhisker.
  do_compose_map; auto.
  path_via (map f (!is_retraction x)  @  (!is_section (f (g (f x))))
    @  map (f o g) (is_section (f x))  @  map f (is_retraction x)).
  unwhisker.
  apply opposite, (homotopy_naturality_fromid B _ (fun y => !is_section y)).
  path_via (map f (!is_retraction x)  @  (is_section (f x) @ (!is_section (f x)))
    @  map f (is_retraction x)).
  unwhisker.
  apply opposite, (homotopy_naturality_fromid B _ (fun y => !is_section y)).
  do_opposite_map.
  cancel_right_opposite_of (is_section (f x)).
Defined.

(** Therefore, "any homotopy equivalence is an equivalence." *)

Definition hequiv_is_equiv {A B} (f : A -> B) (g : B -> A)
  (is_section : forall y, f (g y) == y) (is_retraction : forall x, g (f x) == x) :
  is_equiv f := is_adjoint_to_equiv f (adjointify f g is_section is_retraction).

(** All sorts of nice things follow from this theorem. *)

(** The inverse of an equivalence is an equivalence. *)

Lemma equiv_inverse {A B} (f : A <~> B) : B <~> A.
Proof.
  intros.
  destruct (is_equiv_to_adjoint f (pr2 f)) as [g [is_section [is_retraction triangle]]].
  exists g.
  exact (hequiv_is_equiv g f is_retraction is_section).
Defined.

(** Anything homotopic to an equivalence is an equivalence. *)

Lemma equiv_homotopic {A B} (f g : A -> B) :
  (forall x, f x == g x) -> is_equiv g -> is_equiv f.
Proof.
  intros A B f g' p geq.
  set (g := existT is_equiv g' geq : A <~> B).
  apply @hequiv_is_equiv with (g := g^-1).
  intro y.
  expand_inverse_trg g y; auto.
  intro x.
  equiv_moveright; auto.
Defined.

(** And the 2-out-of-3 property for equivalences. *)

Definition equiv_compose {A B C} (f : A <~> B) (g : B <~> C) : (A <~> C).
Proof.
  intros.
  exists (g o f).
  apply @hequiv_is_equiv with (g := (f^-1) o (g^-1)).
  intro y.
  expand_inverse_trg g y.
  expand_inverse_trg f (g^-1 y).
  apply idpath.
  intro x.
  expand_inverse_trg f x.
  expand_inverse_trg g (f x).
  apply idpath.
Defined.

Definition equiv_cancel_right {A B C} (f : A <~> B) (g : B -> C) :
  is_equiv (g o f) -> is_equiv g.
Proof.
  intros A B C f g H.
  set (gof := (existT _ (g o f) H) : A <~> C).
  apply @hequiv_is_equiv with (g := f o (gof^-1)).
  intro y.
  expand_inverse_trg gof y.
  apply idpath.
  intro x.
  change (f (gof^-1 (g x)) == x).
  equiv_moveright; equiv_moveright.
  change (g x == g (f (f^-1 x))).
  cancel_inverses.
Defined.

Definition equiv_cancel_left {A B C} (f : A -> B) (g : B <~> C) :
  is_equiv (g o f) -> is_equiv f.
Proof.
  intros A B C f g H.
  set (gof := existT _ (g o f) H : A <~> C).
  apply @hequiv_is_equiv with (g := gof^-1 o g).
  intros y.
  expand_inverse_trg g y.
  expand_inverse_src g (f (((gof ^-1) o g) y)).
  apply map.
  path_via (gof ((gof^-1 (g y)))).
  apply inverse_is_section.
  intros x.
  path_via (gof^-1 (gof x)).
  apply inverse_is_retraction.
Defined.

(* It follows that any two contractible types are equivalent. *)

Definition contr_contr_equiv {A B} (f : A -> B) :
  is_contr A -> is_contr B -> is_equiv f.
Proof.
  intros A B f Acontr Bcontr.
  apply @equiv_cancel_left with
    (g := contr_equiv_unit B Bcontr).
  exact (pr2 (contr_equiv_unit A Acontr)).
Defined.

(** The action of an equivalence on paths is an equivalence. *)

Theorem equiv_map_inv {A B} {x y : A} (f : A <~> B) :
  (f x == f y) -> (x == y).
Proof.
  intros A B x y f p.
  path_via (f^-1 (f x)).
  apply opposite, inverse_is_retraction.
  path_via' (f^-1 (f y)).
  apply map. assumption.
  apply inverse_is_retraction.
Defined.

Theorem equiv_map_is_equiv {A B} {x y : A} (f : A <~> B) :
  is_equiv (@map A B x y f).
Proof.
  intros A B x y f.
  apply @hequiv_is_equiv with (g := equiv_map_inv f).
  intro p.
  unfold equiv_map_inv.
  do_concat_map.
  do_opposite_map.
  moveright_onleft.
  undo_compose_map.
  path_via (map (f o (f ^-1)) p @ inverse_is_section f (f y)).
  apply inverse_triangle.
  path_via (inverse_is_section f (f x) @ p).
  apply homotopy_naturality_toid with (f := f o (f^-1)).
  apply opposite, inverse_triangle.
  intro p.
  unfold equiv_map_inv.
  moveright_onleft.
  undo_compose_map.
  apply homotopy_naturality_toid with (f := (f^-1) o f).
Defined.

Definition equiv_map_equiv {A B} {x y : A} (f : A <~> B) :
  (x == y) <~> (f x == f y) :=
  (@map A B x y f ; equiv_map_is_equiv f).

(** Path-concatenation is an equivalence. *)

Lemma concat_is_equiv_left {A} (x y z : A) (p : x == y) :
  is_equiv (fun q: y == z => p @ q).
Proof.
  intros A x y z p.
  apply @hequiv_is_equiv with (g := @concat A y x z (!p)).
  intro q.
  associate_left.
  intro q.
  associate_left.
Defined.

Definition concat_equiv_left {A} (x y z : A) (p : x == y) :
  (y == z) <~> (x == z) :=
  (fun q: y == z => p @ q  ;  concat_is_equiv_left x y z p).

Lemma concat_is_equiv_right {A} (x y z : A) (p : y == z) :
  is_equiv (fun q : x == y => q @ p).
Proof.
  intros A x y z p.
  apply @hequiv_is_equiv with (g := fun r : x == z => r @ !p).
  intro q.
  associate_right.
  intro q.
  associate_right.
Defined.

Definition concat_equiv_right {A} (x y z : A) (p : y == z) :
  (x == y) <~> (x == z) :=
  (fun q: x == y => q @ p  ;  concat_is_equiv_right x y z p).

(** And we can characterize the path types of the total space of a
   fibration, up to equivalence. *)

Theorem total_paths_equiv (A : Type) (P : A -> Type) (x y : sigT P) :
  (x == y) <~> { p : pr1 x == pr1 y & transport p (pr2 x) == pr2 y }.
Proof.
  intros A P x y.
  exists (fun r => existT (fun p => transport p (pr2 x) == pr2 y) (base_path r) (fiber_path r)).
  eapply @hequiv_is_equiv.
  instantiate (1 := fun pq => let (p,q) := pq in total_path A P x y p q).
  intros [p q].
  eapply total_path.
  instantiate (1 := base_total_path A P x y p q).
  simpl.
  apply fiber_total_path.
  intro r.
  simpl.
  apply total_path_reconstruction.
Defined.

(** The homotopy fiber of a fibration is equivalent to the actual fiber. *)

Section hfiber_fibration.

  Hypothesis X:Type.
  Hypothesis P : X -> Type.

  Let hfiber_fibration_map (x : X) : { z : sigT P & pr1 z == x } -> P x.
  Proof.
    intros x [z p].
    apply (transport p).
    exact (pr2 z).
  Defined.

  Let hfiber_fibration_map_path (x : X) (z : sigT P) (p : pr1 z == x) :
    (x ; hfiber_fibration_map x (z ; p)) == z.
  Proof.
    intros x z p.
    apply total_path with (p := !p).
    destruct z as [x' y']. simpl.
    path_via (transport (p @ !p) y').
    apply opposite, trans_concat.
    path_via (transport (idpath _) y').
    apply map with (f := fun q => transport q y').
    cancel_opposites.
  Defined.

  Definition hfiber_fibration (x : X) :
    equiv (P x) { z : sigT P & pr1 z == x }.
  Proof.
    intros x.
    exists (fun y: P x => (((x ; y) ; idpath _)
      : {z : sigT P & pr1 z == x})).
    apply hequiv_is_equiv with (g := hfiber_fibration_map x).
    intros [z p].
    apply total_path with (p := hfiber_fibration_map_path x z p). simpl.
    path_via (transport (P := fun x' => x' == x)
      (map pr1 (hfiber_fibration_map_path x z p))
      (idpath x)).
    apply @map_trans with (P := fun x' => x' == x).
    unfold hfiber_fibration_map_path.
    path_via (transport (P := fun x' => x' == x) (!p) (idpath x)).
    apply map with (f := fun r => transport (P := fun x' => x' == x) r (idpath x)).
    apply @base_total_path with
      (x := (x ; hfiber_fibration_map x (z ; p))).
    path_via ((!!p) @ idpath x).
    apply trans_is_concat_opp.
    cancel_units.
    intros y.
    unfold hfiber_fibration_map. simpl. auto.
  Defined.

End hfiber_fibration.

  (* Replacement of a map by an equivalent fibration. *)
Section FibrationReplacement.

  Hypothesis A B : Type.
  Hypothesis f : A -> B.
  
  Definition fibration_replacement (x:A) : {y:B & {x:A & f x == y}} :=
    (f x ; (x ; idpath (f x))).

  Definition fibration_replacement_equiv : equiv A {y:B & {x:A & f x == y}}.
  Proof.
    exists fibration_replacement.
    apply hequiv_is_equiv with
      (g := fun yxp => match yxp with
                         existT y (existT x p) => x
                       end).
    intros [y [x p]].
    unfold fibration_replacement.
    apply total_path with (p := p). simpl.
    path_via (existT (fun x' => f x' == y) x (idpath (f x) @ p)).
    path_via (existT (fun x' => f x' == y) x (transport p (idpath (f x)))).
    apply opposite.
    apply @trans_map with
      (P := fun y' => f x == y')
      (Q := fun y' => {x':A & f x' == y'})
      (f := fun y' q => existT (fun x' => f x' == y') x q).
    apply trans_is_concat.
    intros x. auto.
  Defined.

  Definition fibration_replacement_factors (x:A) :
    pr1 (fibration_replacement_equiv x) == f x.
  Proof.
    auto.
  Defined.

End FibrationReplacement.

(** The construction of total spaces of fibrations is "associative". *)

Definition total_assoc A (P : A -> Type) (Q : sigT P -> Type) :
  equiv { x:A & { p:P x & Q (existT _ x p)}} (sigT Q).
Proof.
  intros A P Q.
  exists (fun H: {x : A & {p : P x & Q (existT _ x p)}} =>
    let (x,pq) := H in let (p,q):= pq in (existT _ (existT _ x p) q)).
  apply hequiv_is_equiv with
    (g := fun H: sigT Q =>
      let (xp,q) := H in
        (let (x,p)
          as s return (Q s -> {x0 : A & {p : P x0 & Q (existT _ x0 p)}})
            := xp in fun q' =>
              (existT _ x (existT (fun p0 => Q (existT P x p0)) p q'))) q).
  intros [[x p] q]. auto.
  intros [x [p q]]. auto.
Defined.

(** The fiber of a map between fibers (the "unstable octahedral axiom"). *)

Section FiberFibers.

  Hypothesis X Y Z : Type.
  Hypothesis f : X -> Y.
  Hypothesis g : Y -> Z.

  Hypothesis z : Z.

  Definition composite_fiber_map : {x:X & (g o f) x == z} -> {y:Y & g y == z}.
  Proof.
    intros [x p].
    exists (f x).
    exact p.
  Defined.

  Hypothesis yq : {y:Y & g y == z}.

  Let fibfib := {xp : {x:X & (g o f) x == z } & composite_fiber_map xp == yq }.

  Let fibf := {x:X & f x == pr1 yq}.

  Let fib1 : fibfib -> fibf.
  Proof.
    intros [[x p] r].
    exists x.
    exact (base_path r).
  Defined.

  Let fib2 : fibf -> fibfib.
  Proof.
    intros [x r].
    exists (existT (fun x => g (f x) == z) x (map g r @ pr2 yq)).
    simpl.
    apply total_path with (p := r).
    simpl.
    path_via (transport (P := fun z' => z' == z) (map g r) (map g r @ pr2 yq)).
    apply map_trans with (P := fun z' => z' == z).
    path_via (!(map g r) @ (map g r @ pr2 yq)).
    apply trans_is_concat_opp.
    cancel_opposites.
  Defined.

  Definition fiber_of_fiber : equiv fibfib fibf.
  Proof.
    exists fib1.
    apply @hequiv_is_equiv with (g := fib2).
    intros [x p].
    apply total_path with (p := idpath x).
    simpl.
    destruct yq as [y q]. simpl.
    simpl in p.
  Admitted.
  
End FiberFibers.

(** André Joyal suggested the following definition of equivalences,
   and to call it "h-isomorphism". *)

Definition is_hiso {A B} (f : A -> B) :=
  ( { g : B->A  &  forall x, g (f x) == x } *
    { h : B->A  &  forall y, f (h y) == y } )%type.

Theorem equiv_to_hiso {A B} (f : equiv A B) : is_hiso f.
Proof.
  intros A B f.
  split.
  exists (f^-1).
  apply inverse_is_retraction.
  exists (f^-1).
  apply inverse_is_section.
Defined.

Theorem hiso_to_equiv {A B} (f : A -> B) : is_hiso f -> is_equiv f.
Proof.
  intros A B f H.
  destruct H as ((g, is_retraction), (h, is_section)).
  eapply hequiv_is_equiv.
  instantiate (1 := g).
  intro y.
  path_via (f (h y)).
  path_via (g (f (h (y)))).
  assumption.
Defined.

(** Of course, the harder part is showing that is_hiso is a proposition. *)
