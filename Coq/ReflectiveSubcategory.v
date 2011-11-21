
(* Coq-HoTT code formulating the notion "internal reflective subcategory". 

   Externally this is the notion 
   "reflective subcategory such that the reflector preserves products". 
   For background and more discussion see

 http://ncatlab.org/nlab/show/internal+reflective+sub-(infinity,1)-category

   The following code is due to Mike Shulman, taken from 

 https://github.com/mikeshulman/HoTT/blob/master/Coq/ReflectiveSubcategory.v

   Comments at the beginning added by Urs Schreiber.

*)


  (* We speak in the internal language of an ambient infinity-topos H. *)

  Require Import Homotopy.


(* ======================================================================== *)
Section ReflectiveSubcategory.
(* ======================================================================== *)


(* == Definition ========================================================== *)

  (* This section forumlates internally the notion of a 
     reflective sub-infinity-category rsc in H. *)

  (* We proceed in three steps *)

  (* Step A *)
  (* A reflective sub-infinity-category is in particular a full
     sub-infinity-category, hence specified by the (equivalence classes of)
     the objects contained in it. The following proposition asserts that
     an object is in the sub-category rsc. *)

  Hypothesis in_rsc : Type -> Type.

  Hypothesis in_rsc_prop : forall X, is_prop (in_rsc X).

  (* Step B *)
  (* Externally, a full subcategory is reflective iff every object 
     comes with a reflector: a universal morphism to an object in the
     subcategory. The following states the existence of a reflector
     in the internal language.*)

  Hypothesis reflect : Type -> Type.

  Hypothesis reflect_in_rsc : forall X, in_rsc (reflect X).

  Hypothesis map_to_reflect : forall X, X -> reflect X.

  Hypothesis reflect_is_reflection : forall X Y, in_rsc Y ->
    is_equiv (fun f: reflect X -> Y => f o map_to_reflect X).

  (* Step C *)
  (* However, a reflector in the internal language encodes not just 
     a reflective subcategory, but a pullback-stable system of 
     reflective subcategories rsc^x of all slices H/x of H. The subcategory 
     rsc = R^* in the slice H/* over the unit object is the reflective subcategory 
     to be axiomatized, the subcategories of the other slices have to be 
     constrained not to contain additional information

     This is implied already if for all fibrations whose base space and all
     whose fibers are in the subcategory also the total space is. This is asserted
     by the following hypothesis.
  *)

  Hypothesis sum_in_rsc : forall X (P : X -> Type),
    in_rsc X -> (forall x, in_rsc (P x)) -> in_rsc (sigT P).


(* == Properties ========================================================== *)


  (* We now deduce some basic properties of internal reflective subcategories.
  *)

  Hint Resolve sum_in_rsc.

  Hint Resolve reflect_in_rsc.

  (* Package up the equivalence characterizing the universality
     of the reflector as an 'equiv' object. *)
  Definition reflection_equiv : forall X Y, in_rsc Y ->
    equiv (reflect X -> Y) (X -> Y).
  Proof.
    intros X Y P.
    apply existT with (fun f: reflect X -> Y => f o map_to_reflect X).
    apply reflect_is_reflection.
    assumption.
  Defined.

  (* A name for its inverse, which does factorization of maps through
     the unit of the reflection. *)
  Definition reflect_factor {X Y} (Yr : in_rsc Y) : (X -> Y) -> (reflect X -> Y) :=
    inverse (reflection_equiv X Y Yr).

  Definition reflect_factor_factors {X Y} (Yr : in_rsc Y) (f : X -> Y) (x : X) :
    reflect_factor Yr f (map_to_reflect X x) == f x.
  Proof.
    unfold reflect_factor.
    path_via ((reflection_equiv X Y Yr
      (inverse (reflection_equiv X Y Yr) f)) x).
    apply happly.
    cancel_inverses.
  Defined.

  Definition reflect_factor_unfactors {X Y} (Yr : in_rsc Y)
    (f : reflect X -> Y) (rx : reflect X) :
    reflect_factor Yr (f o map_to_reflect X) rx == f rx.
  Proof.
    path_via ((inverse (reflection_equiv X Y Yr)
      (reflection_equiv X Y Yr f)) rx).
    apply happly.
    cancel_inverses.
  Defined.

  Definition reflect_factor_constant {X Y} (Yr : in_rsc Y) (y : Y) (rx : reflect X) :
    reflect_factor Yr (fun _ => y) rx == y.
  Proof.
    unfold reflect_factor.
    apply @happly with (g := fun _ => y).
    equiv_moveright.
    apply funext. intros x. auto.
  Defined.

  (* The reflector is a functor. *)
  Definition reflect_functor {X Y} : (X -> Y) -> (reflect X -> reflect Y).
  Proof.
    intros f.
    apply reflect_factor.
    auto.
    exact (compose (map_to_reflect _) f).
  Defined.

  Definition reflect_factoriality1 {X Y Z} (Yr : in_rsc Y) (Zr : in_rsc Z)
    (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    g (reflect_factor Yr f rx) == reflect_factor Zr (g o f) rx.
  Proof.
    unfold reflect_factor.
    path_via ((g o ((reflection_equiv X Y Yr ^-1) f)) rx).
    apply happly.
    apply equiv_injective with (w := reflection_equiv X Z Zr).
    cancel_inverses.
    path_via ((g o (reflection_equiv X Y Yr ^-1) f) o map_to_reflect X).
    path_via (g o ((reflection_equiv X Y Yr ^-1) f o map_to_reflect X)).
    path_via (reflection_equiv X Y Yr ((reflection_equiv X Y Yr ^-1) f)).
    cancel_inverses.
  Defined.

  Definition reflect_factoriality2 {X Y Z} (Zr : in_rsc Z)
    (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    reflect_factor Zr g (reflect_functor f rx) == reflect_factor Zr (g o f) rx.
  Proof.
    path_via ((reflection_equiv X Z Zr ^-1)
      (reflect_factor Zr g o (map_to_reflect Y o f)) rx).
    unfold reflect_functor, reflect_factor.
    apply reflect_factoriality1.
    apply happly.
    apply @map.
    path_via ((reflect_factor Zr g o map_to_reflect Y) o f).
    apply @map with (f := fun g' => g' o f).
    unfold reflect_factor.
    path_via (reflection_equiv Y Z Zr ((reflection_equiv Y Z Zr ^-1) g)).
    cancel_inverses.
  Defined.

  Definition reflect_functoriality {X Y Z} (g : Y -> Z) (f : X -> Y) (rx : reflect X) :
    reflect_functor g (reflect_functor f rx) == reflect_functor (g o f) rx.
  Proof.
    apply @reflect_factoriality2 with (Z := reflect Z) (Zr := reflect_in_rsc Z).
  Defined.

  Definition reflect_functoriality_id {X} (rx : reflect X) :
    reflect_functor (@id X) rx == rx.
  Proof.
    unfold reflect_functor.
    path_via (reflect_factor (reflect_in_rsc X) (@id (reflect X) o map_to_reflect X) rx).
    apply @reflect_factor_unfactors.
  Defined.

  (* The reflection is also a 2-functor. *)
  Definition reflect_functor2 {X Y} (f g : X -> Y) (p : forall x, f x == g x) :
    forall rx : reflect X, reflect_functor f rx == reflect_functor g rx.
  Proof.
    intros rx; apply happly.
    apply map.
    apply funext. assumption.
  Defined.

  (* The reflector preserves equivalences *)
  Definition reflect_preserves_equiv {X Y} (f : X -> Y) :
    is_equiv f -> is_equiv (reflect_functor f).
  Proof.
    intros H.
    set (feq := (f ; H) : equiv X Y).
    apply hequiv_is_equiv with (g := reflect_functor (inverse feq)).
    intros ry.
    path_via (reflect_functor (feq o inverse feq) ry).
    apply reflect_functoriality.
    path_via (reflect_functor (@id Y) ry).
    apply @map with (f := fun g => reflect_functor g ry).
    apply funext. intros x.
    apply inverse_is_section.
    apply reflect_functoriality_id.
    intros rx.
    path_via (reflect_functor (inverse feq o feq) rx).
    apply reflect_functoriality.
    path_via (reflect_functor (@id X) rx).
    apply @map with (f := fun g => reflect_functor g rx).
    apply funext. intros x. apply inverse_is_retraction.
    apply reflect_functoriality_id.
  Defined.

  Definition reflect_functor_equiv {X Y} (f : equiv X Y) :
    equiv (reflect X) (reflect Y).
  Proof.
    exists (reflect_functor f).
    apply reflect_preserves_equiv.
    apply (pr2 f).
  Defined.

  (* The unit of the reflection is a natural transformation. *)
  Definition reflect_naturality {X Y} (f : X -> Y) (x:X) :
    reflect_functor f (map_to_reflect X x) == map_to_reflect Y (f x).
  Proof.
    assert (p : reflect_functor f o map_to_reflect X == map_to_reflect Y o f).
    unfold reflect_functor, reflect_factor.
    apply inverse_is_section with
      (w := reflection_equiv X (reflect Y) (reflect_in_rsc Y))
      (y := (map_to_reflect Y o f)).
    apply (happly p).
  Defined.

  (* The reflector is a well-pointed endofunctor. *)
  Definition reflect_wellpointed {X} (rx : reflect X) :
    reflect_functor (map_to_reflect X) rx == map_to_reflect (reflect X) rx.
  Proof.
    apply happly.
    apply equiv_injective with
      (w := reflection_equiv X (reflect (reflect X)) (reflect_in_rsc (reflect X))).
    apply funext. intros x.
    apply @reflect_naturality with (f := map_to_reflect X) (x := x).
  Defined.
    
  (* If the unit at X is an equivalence, then X is in the subcategory. *)
  Lemma reflect_equiv_in_rsc X : is_equiv (map_to_reflect X) -> in_rsc X.
    intros H.
    set (eqvpath := equiv_to_path (map_to_reflect X ; H)).
    apply @transport with (P := in_rsc) (x := reflect X).
    exact (!eqvpath).
    apply reflect_in_rsc.
  Defined.

  (* In fact, it suffices for the unit at X merely to have a retraction. *)
  Lemma reflect_retract_in_rsc X (r : reflect X -> X) :
    (forall x, r (map_to_reflect X x) == x) -> in_rsc X.
  Proof.
    intros h.
    apply reflect_equiv_in_rsc.
    apply hequiv_is_equiv with (g := r).
    intros y.
    assert (p : map_to_reflect X o r == @id (reflect X)).
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_via (map_to_reflect X o (@id X)).
    path_via (map_to_reflect X o (r o map_to_reflect X)).
    apply funext.
    exact h.
    exact (happly p y).
    assumption.
  Defined.

  (* If X is in the subcategory, then the unit is an equivalence. *)
  Lemma in_rsc_reflect_equiv X : in_rsc X -> (equiv X (reflect X)).
  Proof.
    intros H.
    exists (map_to_reflect X).
    apply hequiv_is_equiv with (g := reflect_factor H (@id X)).
    intros y.
    unfold reflect_factor.
    assert (p : map_to_reflect X o ((reflection_equiv X X H ^-1) (@id X))
      == @id (reflect X)).
    apply equiv_injective with
      (w := reflection_equiv X (reflect X) (reflect_in_rsc X)).
    simpl.
    path_via (map_to_reflect X o (@id X)).
    path_via (map_to_reflect X o ((reflection_equiv X X H ^-1) (@id X) o map_to_reflect X)).
    exact (inverse_is_section (reflection_equiv X X H) (@id X)).
    exact (happly p y).
    intros x.
    exact (happly (inverse_is_section (reflection_equiv X X H) (@id X)) x).
  Defined.

  (* The unit is inverted by the reflector. *)
  Definition reflect_map_to_reflect_equiv {X} :
    is_equiv (reflect_functor (map_to_reflect X)).
  Proof.
    assert (p : reflect_functor (map_to_reflect X) == map_to_reflect (reflect X)).
    apply funext. intros x. apply reflect_wellpointed.
    apply (transport (!p)).
    apply (pr2 (in_rsc_reflect_equiv (reflect X) (reflect_in_rsc X))).
  Defined.

  (* The inverse of the unit, when it exists, is also natural. *)
  Definition reflect_inverse_naturality {X Y} (Xr : in_rsc X) (Yr : in_rsc Y)
    (f : X -> Y) (rx : reflect X) :
    f (inverse (in_rsc_reflect_equiv X Xr) rx) ==
    (inverse (in_rsc_reflect_equiv Y Yr) (reflect_functor f rx)).
  Proof.
    equiv_moveleft.
    path_via (reflect_functor f
      (in_rsc_reflect_equiv X Xr
        (inverse (in_rsc_reflect_equiv X Xr) rx))).
    apply opposite.
    apply @reflect_naturality.
    cancel_inverses.
  Defined.

  (* The terminal object is in the subcategory. *)
  Definition unit_in_rsc : in_rsc unit.
  Proof.
    apply reflect_retract_in_rsc with (r := fun x => tt).
    intros x; induction x; auto.
  Defined.

  (* The subcategory is closed under path spaces. *)
  Section PathSpaces.

    Hypothesis X:Type.
    Hypothesis X_in_rsc : in_rsc X.
    Hypotheses x0 x1:X.

    Lemma path_map_back : reflect (x0 == x1) -> (x0 == x1).
    Proof.
      intros rl.
      assert (p : (fun _:reflect (x0 == x1) => x0) == (fun _ => x1)).
      apply ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc))^-1).
      unfold reflection_equiv; simpl.
      apply funext; intro l.
      unfold compose.
      assumption.
      apply (happly p).
      assumption.
    Defined.

    Definition path_in_rsc : in_rsc (x0 == x1).
    Proof.
      apply reflect_retract_in_rsc with (r := path_map_back).
      intros x.
      unfold path_map_back.
      path_via
      (happly
        (map (fun f' => f' o (map_to_reflect _))
          ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc) ^-1)
            (@funext _ _
              ((fun _ => x0) o map_to_reflect _)
              ((fun _ => x1) o map_to_reflect _)
              (fun l : x0 == x1 => l)))) x).
      apply opposite, map_precompose.
      path_via
      (happly
        (equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc)
          ((equiv_map_equiv (reflection_equiv (x0 == x1) X X_in_rsc) ^-1)
            (@funext _ _
              ((fun _ => x0) o map_to_reflect _)
              ((fun _ => x1) o map_to_reflect _)
              (fun l : x0 == x1 => l)))) x).
    (* Apparently the cancel_inverses tactic is insufficiently smart. *)
      cancel_inverses.
      apply map with (f := fun g => happly g x).
      cancel_inverses.
      unfold funext.
      apply strong_funext_compute with
        (f := ((fun _ => x0) o map_to_reflect _))
        (g := ((fun _ => x1) o map_to_reflect _)).
    Defined.

  End PathSpaces.

  Hint Resolve path_in_rsc.

  (* The subcategory is closed under binary products. *)
  Section Products.

    Hypotheses X Y : Type.
    Hypothesis Xr : in_rsc X.
    Hypothesis Yr : in_rsc Y.

    Definition prod_map_back : reflect (X * Y) -> X * Y.
    Proof.
      intros rxy.
      split.
      apply (inverse (in_rsc_reflect_equiv X Xr)).
      generalize dependent rxy.
      apply reflect_functor, fst.
      apply (inverse (in_rsc_reflect_equiv Y Yr)).
      generalize dependent rxy.
      apply reflect_functor, snd.
    Defined.

    Definition prod_in_rsc : in_rsc (X * Y).
    Proof.
      apply reflect_retract_in_rsc with (r := prod_map_back).
      intros xy. destruct xy.
      unfold prod_map_back.
      apply prod_path.
      equiv_moveright.
      path_via (map_to_reflect X (fst (x,y))).
      apply reflect_naturality.
      equiv_moveright.
      path_via (map_to_reflect Y (snd (x,y))).
      apply reflect_naturality.
    Defined.

  End Products.

  (* The internal reflective subcategory is a local exponential ideal. *)
  (* ================================================================= *)
  Section ExponentialIdeal.
  (* ================================================================= *)

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).

    Lemma exp_map_back : reflect (forall x, P x) -> forall x, P x.
    Proof.
      intros rf x.
      apply (inverse (in_rsc_reflect_equiv (P x) (Pr x))).
      generalize dependent rf.
      apply reflect_functor.
      intros f.
      apply f.
    Defined.

    Definition exp_in_rsc : in_rsc (forall x, P x).
    Proof.
      apply reflect_retract_in_rsc with (r := exp_map_back).
      intros f.
      apply funext_dep. intros x.
      unfold exp_map_back.
      equiv_moveright.
      simpl.
      apply @reflect_naturality with (f := (fun g => g x)).
    Defined.

  End ExponentialIdeal.

  (* This allows us to extend functoriality to multiple variables. *)
  Definition reflect_functor_twovar {X Y Z}
    : (X -> Y -> Z) -> (reflect X -> reflect Y -> reflect Z).
  Proof.
    intros f rx.
    apply @reflect_factor with (X := X).
    apply exp_in_rsc. intros; apply reflect_in_rsc.
    intros x ry.
    apply @reflect_factor with (X := Y).
    apply reflect_in_rsc.
    intros y.
    apply map_to_reflect, f; auto. auto. auto.
  Defined.

  (* As a consequence of the foregoing, the reflector preserves finite
     products. *)
  Section PreservesProducts.
    
    Hypotheses X Y : Type.

    Definition reflect_prod_cmp (rxy : reflect (X * Y)) : reflect X * reflect Y
      := (reflect_functor (@fst X Y) rxy, reflect_functor (@snd X Y) rxy).

    Definition reflect_prod_map_back : reflect X * reflect Y -> reflect (X * Y).
    Proof.
      intros [rx ry].
      generalize dependent ry.
      apply @reflect_factor with (X := X).
      apply exp_in_rsc.
      intros; apply reflect_in_rsc.
      intros x ry.
      apply @reflect_factor with (X := Y).
      apply reflect_in_rsc.
      intros y.
      apply map_to_reflect.
      exact ((x,y)).
      assumption. assumption.
    Defined.

    Definition reflect_prod_pres : is_equiv reflect_prod_cmp.
    Proof.
      apply hequiv_is_equiv with (g := reflect_prod_map_back).
      intros [rx ry].
      unfold reflect_prod_cmp, reflect_prod_map_back.
      apply prod_path.
      (* To be completed... *)
    Admitted.
    
  End PreservesProducts.

End ReflectiveSubcategory.
