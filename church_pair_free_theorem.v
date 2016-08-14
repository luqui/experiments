Section bmo.

Set Implicit Arguments.
Require ClassicalFacts.
Require FunctionalExtensionality.

Variable ax_prop_extensionality : ClassicalFacts.provable_prop_extensionality.


Lemma trans : forall (X Y : Type), X = Y -> X -> Y.
 intros X Y p.
 destruct p.
 auto.
Defined.


Variable f : forall A : Type, A -> A -> A.
Hypothesis freef : forall (A B : Type) (x y : A) (g : A -> B), 
                   g (f x y) = f (g x) (g y).

Lemma true_preserve : f True True = True.
  exact (eq_sym (freef True True (fun a => True))).
Defined.

Lemma f_prop_preserve_inh : forall A B : Prop, A -> B -> f A B.
 intros A B a b.
 rewrite (ax_prop_extensionality a).
 rewrite (ax_prop_extensionality b).
 rewrite true_preserve.
 trivial.
Qed.

Section monomorphic.

Variable A : Type.
Variable x y : A.

Definition g := fun a => a = x \/ a = y.

Lemma outer : f (g x) (g y).
 apply f_prop_preserve_inh ; unfold g ; auto.
Qed.

Theorem monomorphic : f x y = x \/ f x y = y.
 fold (g (f x y)).
 rewrite <- (eq_sym (freef x y g)).
 exact outer.
Qed.

End monomorphic.



(* Next challenge:

   Prove that either (f = fun A x y => x) or (f = fun A x y = y)
*)

Section polymorphic.

Definition fType := forall A : Type, A -> A -> A.
Definition proj1 : fType := fun A x y => x.
Definition proj2 : fType := fun A x y => y.

Lemma abstract1 : forall (ff : fType), (forall (A : Type) (x y : A), ff A x y = x) -> ff = proj1.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 unfold proj1.
 apply H.
Qed.

Lemma abstract2 : forall (ff : fType), (forall (A : Type) (x y : A), ff A x y = y) -> ff = proj2.
 intros.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 apply FunctionalExtensionality.functional_extensionality_dep ; intro.
 unfold proj1.
 apply H.
Qed.

Lemma known1 : f true false = true -> forall (A : Type) (x y : A), f x y = x.
 intros.
 rewrite <- (freef true false (fun i => if i then x else y)).
 rewrite H.
 trivial.
Qed.

Lemma known2 : f true false = false -> forall (A : Type) (x y : A), f x y = y.
 intros.
 rewrite <- (freef true false (fun i => if i then x else y)).
 rewrite H.
 trivial.
Qed.

Lemma polymorphic_helper : forall b, f true false = b -> f = proj1 \/ f = proj2.
 intros ; destruct b.
 left.
 apply abstract1.
 apply known1.
 assumption.

 right.
 apply abstract2.
 apply known2.
 assumption.
Qed.

Theorem polymorphic : f = proj1 \/ f = proj2.
 exact (polymorphic_helper eq_refl).
Qed.

End polymorphic.

End bmo.
