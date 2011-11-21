
  (* We speak in the internal language of an ambient infinity-topos H. *)
  Require Import Homotopy.

Section ReflectiveSubcategory.

  (* This section axiomatizes a reflective sub-infinity-category 
  rsc in H. *)

  (* A reflective sub-infinity-category is in particular a full
  sub-infinity-category, specified by the (equivalence classes of)
  the objects contained in it. The following proposition asserts that
  an object is in the sub-category rsc. *)

  Hypothesis in_rsc : Type -> Type.

  Hypothesis in_rsc_prop : forall X, is_prop (in_rsc X).

  (* Externally, a full subcategory is reflective iff every object 
  comes with a reflector: a universal morphism to an object in the
  subcategory. The following states the existence of a reflector
  in the internal language.*)

  Hypothesis reflect : Type -> Type.

  Hypothesis reflect_in_rsc : forall X, in_rsc (reflect X).

  Hypothesis map_to_reflect : forall X, X -> reflect X.

  Hypothesis reflect_is_reflection : forall X Y, in_rsc Y ->
    is_equiv (fun f: reflect X -> Y => f o map_to_reflect X).

  (* However, a reflector in the internal language encodes not just 
  a reflective subcategory, but a pullback-stable system of subcategories 
  of all slices. The genuine reflective subcategories correspond to those 
  such systems that consist of bundles which are fiberwise in the 
  subcategory. This property is enforced by the following two axioms.
  *)



  (* The following axiom ensures that the factorization system is determined
     by the underlying reflective subcategory, i.e. that it is a
     "reflective factorization system". *)

  Hypothesis rsc_reflective_fs : forall X Y (f : X -> Y) (y : Y),
    is_contr (reflect X) -> is_contr (reflect Y) -> is_contr (reflect {x:X & f x == y}).

  (* A map is in E if all its homotopy fibers become contractible upon
     reflection into the subcategory. *)

  Definition in_E {X Y} (f : X -> Y) : Type
    := forall y, is_contr (reflect {x:X & f x == y}).

  Definition E_three_for_two {X Y Z} (f : X -> Y) (g : Y -> Z) :
    in_E g -> in_E (g o f) -> in_E f.
  Proof. Admitted.


  (* We now deduce some basic properties of the reflective subcategory rsc.
  *)

  Hint Resolve reflect_in_rsc.

  (* Package up that equivalence as an 'equiv' object. *)
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

  (* The subcategory is a local exponential ideal. This is a little
     surprising, since in general not every reflective subcategory has
     this property, but it follows because our reflective subcategory
     is "internally" so. *)
  Section ExponentialIdeal.

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

  (* Semantically, so far what we have is a "reflective subfibration"
     of the codomain fibration of the (oo,1)-category of types. In
     other words, each slice category H/x has a reflective subcategory
     R^x, and the pullback functors preserve the R's and commute with
     the reflectors.

     We want all of this data to be entirely determined by an ordinary
     reflective subcategory of H itself. We first impose an axiom
     which is equivalent to saying that if M is the class of morphisms
     that are the objects of the categories R^x, then M is the right
     class of a factorization system.
     *)

  Hypothesis sum_in_rsc : forall X (P : X -> Type),
    in_rsc X -> (forall x, in_rsc (P x)) -> in_rsc (sigT P).

  Hint Resolve sum_in_rsc.

  (* This allows us to generalize the factorization and functoriality
     properties to the dependent context. *)

  Section DependentFactor.

    Hypothesis X : Type.
    Hypothesis P : reflect X -> Type.
    Hypothesis Pr : forall x, in_rsc (P x).
    Hypothesis f : forall x, P (map_to_reflect X x).

    Let rfdepmap : reflect X -> sigT P.
    Proof.
      intros x.
      apply (inverse (in_rsc_reflect_equiv (sigT P)
        (sum_in_rsc _ P (reflect_in_rsc X) Pr))).
      generalize dependent x.
      apply reflect_functor.
      intros x. exists (map_to_reflect X x). exact (f x).
    Defined.

    Definition reflect_factor_dep : (forall rx, P rx).
    Proof.
      intros rx.
      assert (p : pr1 (rfdepmap rx) == rx).
      unfold rfdepmap.
      path_via (inverse (in_rsc_reflect_equiv (reflect X) (reflect_in_rsc X))
        (reflect_functor pr1
          (reflect_functor (fun x : X => (map_to_reflect X x ; f x)) rx))).
      apply reflect_inverse_naturality.
      equiv_moveright.
      path_via (reflect_functor
        (pr1 o (fun x : X => (map_to_reflect X x ; f x))) rx).
      apply reflect_functoriality.
      path_via (reflect_functor (map_to_reflect X) rx).
      apply @reflect_wellpointed with (X := X).
      apply (transport p).
      exact (pr2 (rfdepmap rx)).
    Defined.

  End DependentFactor.
  
  Definition reflect_functor_dep {X} {P : reflect X -> Type}
    : (forall x, P (map_to_reflect X x)) -> (forall rx, reflect (P rx)).
  Proof.
    intros f.
    apply reflect_factor_dep with (X := X).
    intros rx; apply reflect_in_rsc.
    intros x; apply map_to_reflect; auto.
  Defined.

  (* Over a base object that is in the subcategory, the "fiberwise
     reflection" is equivalent to reflecting the total space. *)
  Section ReflectFiberwise.

    Hypothesis X : Type.
    Hypothesis P : X -> Type.
    Hypothesis Xr : in_rsc X.

    Let rf1 : {x:X & reflect (P x)} -> (reflect (sigT P)).
    Proof.
      intros [x rp].
      generalize dependent rp.
      apply reflect_functor.
      intros p; exists x; exact p.
    Defined.

    Let rf2 : (reflect (sigT P)) -> {x:X & reflect (P x)}.
    Proof.
      apply reflect_factor.
      apply sum_in_rsc; [assumption | auto].
      intros [x p]; exists x; apply map_to_reflect; assumption.
    Defined.

    (* This proof is far too messy. *)
    Definition reflect_functor_fiberwise :
      equiv {x:X & reflect (P x)} (reflect (sigT P)).
    Proof.
      exists rf1.
      apply hequiv_is_equiv with (g := rf2).
      intros rx.
      apply reflect_factor_dep with
        (X := sigT P) (P := fun rx => rf1 (rf2 rx) == rx).
      auto.
      intros [x p].
      unfold rf1, rf2, reflect_functor, reflect_factor.
      assert (H : (reflection_equiv (sigT P) {x0 : X & reflect (P x0)}
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0))) ^-1)
      (fun X0 : sigT P =>
        let (x0, p0) := X0 in
          (existT (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p0)))
      (map_to_reflect (sigT P) (x ; p))
      ==
      (fun X0 : sigT P =>
        let (x0, p0) := X0 in
          (existT (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p0)))
      (x ; p)).
      path_via (((reflection_equiv (sigT P) {x0 : X & reflect (P x0)}
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0))) ^-1)
      (fun X0 : sigT P =>
        let (x0, p0) := X0 in (existT
          (fun x' => reflect (P x'))
          x0 (map_to_reflect (P x0) p0))) o
      (map_to_reflect (sigT P))) (x ; p)).
      apply @happly with
        (g := fun xp => (existT
          (fun x' => reflect (P x'))
          (pr1 xp) (map_to_reflect (P (pr1 xp)) (pr2 xp)))).
      path_via (reflection_equiv (sigT P) {x0 : X & reflect (P x0)}
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
        ((reflection_equiv (sigT P) {x0 : X & reflect (P x0)}
          (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
            (fun x0 : X => reflect_in_rsc (P x0))) ^-1)
        (fun X0 : sigT P =>
          let (x0, p0) := X0 in (existT
            (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p0))))).
      path_via (fun X0 : sigT P =>
        let (x0, p0) := X0 in (existT
          (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p0))).
      apply inverse_is_section.
      apply funext. intros [x' p']. simpl. auto.
      simpl in H.
      apply @transport with
        (P := fun h:sigT (fun x' => reflect (P x')) => (let (x0, rp) := h in
          (reflection_equiv (P x0)
            (reflect (sigT P)) (reflect_in_rsc (sigT P)) ^-1)
          (map_to_reflect (sigT P) o (fun p0 : P x0 => (x0 ; p0))) rp) ==
        map_to_reflect (sigT P) (x ; p))
        (x := (existT
          (fun x' => reflect (P x')) x (map_to_reflect (P x) p)))
        (y := (reflection_equiv (sigT P) {x0 : X & reflect (P x0)}
          (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
            (fun x0 : X => reflect_in_rsc (P x0))) ^-1)
        (fun X0 : sigT P =>
          let (x0, p0) := X0 in (existT
            (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p0)))
        (map_to_reflect (sigT P) (x ; p))).
      apply opposite, H.
      path_via
      (reflection_equiv (P x) (reflect (sigT P)) (reflect_in_rsc (sigT P))
        ((reflection_equiv (P x) (reflect (sigT P)) (reflect_in_rsc (sigT P)) ^-1)
          (map_to_reflect (sigT P) o (fun p0 : P x => (x ; p0)))) p).
      path_via ((map_to_reflect (sigT P) o (fun p0 : P x => (x ; p0))) p).
      apply happly.
      cancel_inverses.

      intros [x rp].
      unfold rf1, rf2.
      path_via (reflect_factor
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
        ((fun X0 : sigT P => let (x0, p) := X0 in
          (existT (fun x' => reflect (P x')) x0 (map_to_reflect (P x0) p)))
        o (fun p : P x => (x ; p))) rp).
      apply reflect_factoriality2.
      path_via (reflect_factor
        (sum_in_rsc X (fun x0 : X => reflect (P x0)) Xr
          (fun x0 : X => reflect_in_rsc (P x0)))
        (fun p : P x =>
          (existT (fun x' => reflect (P x')) x (map_to_reflect (P x) p))) rp).
      apply reflect_factor_unfactors.
    Defined.
    
  End ReflectFiberwise.

  (* Here are the definitions of the two classes in the factorization system. *)

  (* A map is in M if all its homotopy fibers are in the subcategory. *)
  Definition in_M {X Y} (f : X -> Y) : Type
    := forall y, in_rsc {x:X & f x == y}.


  (* Definition of in_E removed here*)

  Definition Mmap X Y := { f : X -> Y & in_M f }.
  Definition Mmap_coerce_to_function X Y (f : Mmap X Y) : (X -> Y) := projT1 f.
  Coercion Mmap_coerce_to_function : Mmap >-> Funclass.

  Definition Emap X Y := { f : X -> Y & in_E f }.
  Definition Emap_coerce_to_function X Y (f : Emap X Y) : (X -> Y) := projT1 f.
  Coercion Emap_coerce_to_function : Emap >-> Funclass.

(* Remove the bit that gives universe inconsistency.

  (* A map that is inverted by the reflector, and whose codomain is in
     the subcategory, belongs to E. *)
  Section InvertedInE.

    Hypothesis X Y : Type.
    Hypothesis Yr : in_rsc Y.
    Hypothesis f : X -> Y.
    Hypothesis rfeq : is_equiv (reflect_factor Yr f).

    Let Pf := {y:Y & {x:X & f x == y}}.
    Let XtoPf := fibration_replacement_equiv X Y f : equiv X Pf.
    Let PftoY := pr1 : Pf -> Y.

    Let PftoYeq : is_equiv (reflect_factor Yr PftoY).
    Proof.
      apply @equiv_cancel_right with
        (A := reflect X)
        (f := reflect_functor_equiv XtoPf).
      assert (cf : PftoY o XtoPf == f).
      apply funext. unfold PftoY, XtoPf. intros x.
      apply fibration_replacement_factors.
      assert (rcf : reflect_factor Yr PftoY o reflect_functor_equiv XtoPf
        == reflect_factor Yr f).
      path_via (reflect_factor Yr (PftoY o XtoPf)).
      apply funext. intros rx.
      path_via (reflect_factor Yr PftoY (reflect_functor XtoPf rx)).
      apply reflect_factoriality2.
      apply (transport (!rcf)).
      assumption.
    Defined.

    Let Qf := {y:Y & reflect {x:X & f x == y}}.

    Let QftoYeq : equiv Qf Y.
    Proof.
      apply @equiv_compose with (B := reflect Pf).
      apply reflect_functor_fiberwise. auto. 
      exists (reflect_factor Yr PftoY). auto.
    Defined.

    Let QftoYispr1 (z : Qf) : QftoYeq z == pr1 z.
    Proof.
      destruct z as [y rxp].
      unfold QftoYeq. simpl.
      path_via (reflect_factor Yr PftoY
    ((fun X0 : {x : Y & reflect {x0 : X & f x0 == x}} =>
       let (x, rp) return (reflect {y':Y & {x':X & f x' == y'}}) := X0 in
       reflect_functor (fun p : {x0 : X & f x0 == x} => (x ; p)) rp)
     (existT (fun y' => reflect {x:X & f x == y'}) y rxp))).
      path_via (reflect_factor Yr (PftoY o
        (fun p : {x0 : X & f x0 == y} => (y ; p))) rxp).
      apply reflect_factoriality2.
      unfold PftoY.
      path_via (reflect_factor Yr (fun _ => y) rxp).
      apply reflect_factor_constant.
    Defined.
    
    Definition inverted_to_rsc_in_E : in_E f.
    Proof.
      set (hfcontr := pr2 QftoYeq).
      unfold in_E.
      intros y.
      assert (fibeq : reflect {x : X & f x == y} == hfiber (pr1 QftoYeq) y).
      unfold hfiber.
      path_via ({x : Qf & pr1 x == y}).
      apply equiv_to_path.
      unfold Qf, QftoYeq.
      apply hfiber_fibration with
        (P := fun y' => reflect { x:X & f x == y' })
        (x := y).
      apply funext. intros q.
      apply @map with (f := (fun r => r == y)).
      apply opposite, QftoYispr1.
      apply (transport (!fibeq)).
      apply hfcontr.
      (* Oh noes! Universe inconsistency! *)
    Defined.

  End InvertedInE.

  (* In particular, the unit of the reflector is always in E. *)
  Definition map_to_reflect_in_E X : in_E (map_to_reflect X).
  Proof.
    apply inverted_to_rsc_in_E with
      (Y := reflect X)
      (Yr := reflect_in_rsc X).
    assert (p : @id (reflect X) == reflect_factor (reflect_in_rsc X) (map_to_reflect X)).
    path_via (reflect_factor (reflect_in_rsc X) ((@id (reflect X) o map_to_reflect X))).
    apply opposite. apply funext. intros x. apply reflect_factor_unfactors.
    apply funext; intros x; auto.
    apply (transport p).
    apply (pr2 (idequiv _)).
  Defined.

*)

  (* E and M are homotopy orthogonal to each other. *)
  Section EMOrth.

    (* A commutative square with an E on the left and an M on the right. *)
    Hypotheses X Y Z W : Type.
    Hypothesis e : Emap X Y.
    Hypothesis m : Mmap Z W.
    Hypothesis f : X -> Z.
    Hypothesis g : Y -> W.
    Hypothesis s : forall x, m (f x) == g (e x).

    (* We construct a lift simultaneously with a homotopy in the lower
       triangle. *)

    Definition EMlift_tot (y:Y) : {z:Z & m z == g y} :=
      reflect_factor (pr2 m (g y))
        (fun X0 : {x : X & e x == y} =>
          let (x,p) := X0 in (f x ; s x @ map g p)) (pr1 (pr2 e y)).

    Definition EMlift (y:Y) : Z :=
      pr1 (EMlift_tot y).

    Definition EMlift_lowertri (y:Y) : m (EMlift y) == g y :=
      pr2 (EMlift_tot y).
    
    (* Then we extract the upper triangle simultaneously with a proof
       that the two triangles compose to the given square. *)

    Definition EMlift_uppertri_plus (x : X) :
      EMlift_tot (e x) == (f x ; s x).
    Proof.
      unfold EMlift_tot.
      path_via (reflect_factor (pr2 m (g (e x)))
          (fun X0 : {x0 : X & e x0 == e x} =>
            let (x0, p) := X0 in (f x0 ; s x0 @ map g p))
          (map_to_reflect _ (x ; idpath (e x)))).
      apply opposite, (pr2 (pr2 e (e x))).
      unfold reflect_factor.
      path_via (reflection_equiv {x0 : X & e x0 == e x}
       {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x)))
      ((reflection_equiv {x0 : X & e x0 == e x}
         {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x))) ^-1)
        (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p)))
        (x ; idpath (e x))).
      path_via (existT (fun z => m z == g (e x))
        (f x) (s x @ map g (idpath (e x)))).
      assert (H : reflection_equiv {x0 : X & e x0 == e x}
       {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x)))
      ((reflection_equiv {x0 : X & e x0 == e x}
         {x0 : Z & pr1 m x0 == g (e x)} (pr2 m (g (e x))) ^-1)
        (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p)))
      == (fun X0 : {x0 : X & e x0 == e x} =>
         let (x0, p) := X0 in (f x0 ; s x0 @ map g p))).
      apply inverse_is_section.
      apply (happly H).
    Defined.

    Definition EMlift_uppertri (x:X) : EMlift (e x) == f x :=
      base_path (EMlift_uppertri_plus x).

    Definition EMlift_square (x:X) :
      !map m (EMlift_uppertri x) @ EMlift_lowertri (e x) == s x.
    Proof.
      path_via (transport
        (base_path (EMlift_uppertri_plus x))
        (pr2 (EMlift_tot (e x)))).
      path_via (transport
        (P := fun w => w == g (e x))
        (x := m (pr1 (EMlift_tot (e x))))
        (y := m (pr1 (f x ; s x)))
        (map m (base_path (EMlift_uppertri_plus x)))
        (pr2 (EMlift_tot (e x)))).
      apply opposite, trans_is_concat_opp.
      apply opposite.
      apply @map_trans with (P := fun w => w == g (e x)).
      exact (fiber_path (EMlift_uppertri_plus x)).
    Defined.

    (* So far we have just shown that a lift exists. We should prove
       that it is unique, and in fact homotopy unique (i.e. the space
       of such lifts is contractible). *)

  End EMOrth.

  (* Every morphism factors as an E followed by an M. *)
  Section EMFactor.

    Hypothesis X Y : Type.
    Hypothesis f : X -> Y.

    (* The intermediate object we factor through. *)
    Let Z := {y:Y & reflect {x:X & f x == y}}.

    (* The E part *)
    Let e (x:X) : Z :=
      existT (fun y => reflect {x:X & f x == y}) (f x)
      (map_to_reflect _ (x ; idpath _)).

    (* The M part *)
    Let m : Z -> Y := pr1.

    (* We can now identify the fiber of e as something more manageable.
       Probably univalence is not necessary for this proof, but it
       makes it much easier. *)
    Definition efiber_ident (z : Z) : {x : X & e x == z} ==
      { hf : {x:X & f x == pr1 z} & map_to_reflect _ hf == pr2 z }.
    Proof.
      destruct z as [y rxp].
      path_via ({x:X & {p : f x == y &
        (transport (P := fun y' => reflect {x':X & f x' == y'}) p
          (map_to_reflect _ (existT (fun x' => f x' == f x) x (idpath (f x))))
          == rxp)}}).
      apply funext. intros x.
      apply equiv_to_path, total_paths_equiv.
      path_via ({x:X & {p : f x == y &
        (map_to_reflect _ (existT (fun x' => f x' == y) x p)) == rxp}}).
      apply funext. intros x.
      apply map.
      apply funext. intros p.
      apply @map with (f := fun t => t == rxp).
      apply opposite.
      path_via (map_to_reflect {x' : X & f x' == y}
        (x ; (transport (P := fun y => f x == y) p (idpath (f x))))).
      apply opposite.
      path_via (idpath (f x) @ p).
      apply @trans_is_concat.
      apply @trans_map with
        (P := fun (y:Y) => f x == y)
        (Q := fun (y:Y) => reflect {x0:X & f x0 == y})
        (f := fun (y:Y) (r:f x == y) =>
          map_to_reflect {x0:X & f x0 == y} (x ; r)).
      apply equiv_to_path.
      apply total_assoc with
        (P := fun x => f x == y)
        (Q := fun xp => map_to_reflect {x' : X & f x' == y} xp == rxp).
    Defined.

    (* The factorization. *)
    Definition EM_factor :
      {Z:Type & {e : Emap X Z & {m : Mmap Z Y & m o e == f}}}.
    Proof.
      exists Z.
      assert (einE : in_E e).
      unfold in_E. intros z.
      apply (transport (P := fun T => is_contr (reflect T)) (!efiber_ident z)).
      destruct z as [y rxp]. simpl.
      apply map_to_reflect_in_E.
      exists (e ; einE).
      assert (minM: in_M m).
      unfold in_M, m.
      intros y.
      set (q := equiv_to_path
        (hfiber_fibration _ (fun y => reflect {x:X & f x == y}) y)).
      apply (transport (P := in_rsc) q). auto.
      exists (m ; minM).
      apply funext. intros x. unfold m, e; simpl. auto.
    Defined.

  End EMFactor.


End ReflectiveSubcategory.

