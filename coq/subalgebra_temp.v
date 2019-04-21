


  
  Definition par2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) ||
      if (g_in != g_out :> G1) && (g_in != g_out :> G2)
      then [set x; y] \in [set [set inl g_in; inr g_in]; [set inl g_out; inr g_out]]
      else [set x; y] \subset [set inl g_in; inl g_out; inr g_in; inr g_out].

  Definition par2_eqv_refl : reflexive par2_eqv.
  Proof. by move=> ?; rewrite /par2_eqv eqxx. Qed.

  Lemma par2_eqv_sym : symmetric par2_eqv.
  Proof. move=> x y. by rewrite /par2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition par2_eqv_trans : transitive par2_eqv.
  Proof using.
    move=> y x z. rewrite /par2_eqv.
    case/altP: (x =P y) => [<-//|xNy/=]. case/altP: (y =P z) => [<-->//|yNz/=].
    case/boolP: ((g_in != g_out :> G1) && (g_in != g_out :> G2)).
    - rewrite !inE -(implyNb (x == z)).
      case/andP=> /negbTE iNo1 /negbTE iNo2 Hxy Hyz. apply/implyP=> xNz.
      move: Hxy xNy. rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      case/orP => /andP[]/andP[] /orP[]/eqP ? /orP[]/eqP ? _; subst=> // _.
      all: move: Hyz xNz yNz; rewrite 2!eqEcard 2!subUset 4!sub1set !inE.
      all: rewrite ?eqxx ?sum_eqE ?[g_out == g_in]eq_sym ?iNo1 ?iNo2 ?orbT ?orbF /=.
      all: case/andP => /orP[]/eqP-> _; by rewrite !eqxx.
    - rewrite -implyNb => _ Hxy Hyz. apply/implyP=> xNz.
      rewrite subUset !sub1set. apply/andP; split.
      + apply: (subsetP Hxy). by rewrite !inE eqxx.
      + apply: (subsetP Hyz). by rewrite !inE eqxx.
  Qed.

  Canonical par2_eqv_equivalence :=
    EquivRel par2_eqv par2_eqv_refl par2_eqv_sym par2_eqv_trans.

  Lemma par2_eqv_io :
    (par2_eqv (inl g_in) (inr g_in)) * (par2_eqv (inl g_out) (inr g_out)).
  Proof.
    rewrite /par2_eqv/=. case: ifP => _.
    - by rewrite !inE !eqxx.
    - by rewrite !subUset !sub1set !inE !eqxx.
  Qed.

  Definition par2_eq (x y : union G1 G2) :=
    match x,y with
    | inl x, inr y => (x == g_in) && (y == g_in) || (x == g_out) && (y == g_out)
    | _,_ => false
    end.

  Lemma set2_in_sym (T : finType) (x y a b : T) (e : rel T) :  
    x != y -> symmetric e -> e a b -> [set x;y] == [set a;b] -> e x y.
  Proof.
    move => xDy sym_e e_ab E. move: E xDy. rewrite eqEsubset !subUset !sub1set -andbA.
    case/and3P => /set2P[->|->] /set2P[->|->] _; by rewrite ?eqxx // sym_e.
  Qed.

  Lemma equiv_of_sub (T : finType) (e1 e2 : rel T) :
    subrel e1 e2 -> reflexive e2 -> symmetric e2 -> transitive e2 -> subrel (equiv_of e1) e2.
  Proof. 
    move => sub2 refl2 sym2 trans2 x y. case/connectP => p. 
    elim: p x => [x _ -> //|a p IHp x] /= /andP [/orP H] pth lst.
    apply: trans2 _ (IHp _ pth lst). case: H; last rewrite sym2; exact: sub2.
  Qed.

  Hint Resolve equiv_of_sym.
  Ltac sub := apply: sub_equiv_of => /=; by rewrite !eqxx.

  Lemma par2_equiv_of : par2_eqv =2 equiv_of par2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - rewrite /par2_eqv. case/altP: (x =P y) => [<- _|xNy]/=; first exact: equiv_of_refl.
      case: ifP => [_|/negbT].
      + rewrite !inE. case/orP; apply: set2_in_sym => //; sub.
      + rewrite negb_and 2!negbK. case/orP=> [/eqP Eio1|/eqP Eio2].
        * rewrite -Eio1 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inr g_out) (inr g_in). 
          { apply: (@equiv_of_trans _ _ (inl g_in)); first rewrite equiv_of_sym Eio1; sub. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ _ (inl _)]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio1 !eqxx].
          by rewrite equiv_of_sym.
        * rewrite -setUA -Eio2 setUid => Exy.
          have Rio2 : equiv_of par2_eq (inl g_out) (inl g_in).
          { apply: (@equiv_of_trans _ _ (inr g_out)); last rewrite equiv_of_sym -Eio2;
            by apply: sub_equiv_of; rewrite /par2_eq !eqxx. }
          move: Exy xNy; rewrite subUset 2!sub1set !inE -2!orbA.
          case/andP=> /or3P[]/eqP-> /or3P[]/eqP->.
          all: rewrite ?eqxx // ?[equiv_of _ (inr _) _]equiv_of_sym => _.
          all: try solve [apply: (@sub_equiv_of _ _ (inl _));
                          by rewrite /par2_eq -?Eio2 !eqxx].
          by rewrite equiv_of_sym.
    - apply: equiv_of_sub; auto using par2_eqv_refl,par2_eqv_sym,par2_eqv_trans.
      move => {x y} [x|x] [y|y] => //=. 
      by case/orP; case/andP => /eqP-> /eqP->; rewrite par2_eqv_io.
  Qed.

  Lemma par2_eqv_ii x y : 
    x = g_in :> G1 -> y = g_in :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.
  
  Lemma par2_eqv_oo x y : 
    x = g_out :> G1 -> y = g_out :> G2 ->
    par2_eqv (inl x) (inr y).
  Proof.
    move => -> ->. rewrite par2_equiv_of. apply: sub_equiv_of.
      by rewrite /par2_eq !eqxx. 
  Qed.

  Definition par2 := 
    {| graph_of := merge (union G1 G2) par2_eqv ;
       g_in := \pi_{eq_quot par2_eqv} (inl g_in);
       g_out := \pi_{eq_quot par2_eqv} (inl g_out) |}.



  Definition seq2_eqv : rel (union G1 G2) :=
    fun x y => (x == y) || ([set x; y] == [set inl g_out; inr g_in]).

  Definition seq2_eqv_refl : reflexive seq2_eqv.
  Proof. by move=> ?; rewrite /seq2_eqv eqxx. Qed.

  Lemma seq2_eqv_sym : symmetric seq2_eqv.
  Proof. move=> x y. by rewrite /seq2_eqv [[set y; x]]setUC [y == x]eq_sym. Qed.

  Definition seq2_eqv_trans : transitive seq2_eqv.
  Proof using.
    move=> y x z. rewrite /seq2_eqv.
    case/altP: (x =P y) => [<-//|/= xNy Exy].
    case/altP: (y =P z) => [<-|/= yNz Eyz]; first by rewrite Exy.
    case/altP: (x =P z) => //= xNz.
    have := eq_refl #|[set inl (@g_out G1); inr (@g_in G2)]|.
    rewrite -{1}(setUid [set _; _]) -{1}(eqP Exy) -{1}(eqP Eyz).
    rewrite set2C -setUUr (cardsU1 y) !cards2 !inE.
    by rewrite (eq_sym y x) negb_or xNy yNz xNz.
  Qed.

  Canonical seq2_eqv_equivalence :=
    EquivRel seq2_eqv seq2_eqv_refl seq2_eqv_sym seq2_eqv_trans.

  Lemma seq2_eqv_io : seq2_eqv (inl g_out) (inr g_in).
  Proof. by rewrite /seq2_eqv/=. Qed.

  Definition seq2_eq : simpl_rel (union G1 G2) :=
    [rel a b | (a == inl g_out) && (b == inr g_in)].

  Lemma seq2_equiv_of : seq2_eqv =2 equiv_of seq2_eq.
  Proof using.
    move=> x y. apply/idP/idP.
    - rewrite/seq2_eqv. case/altP: (x =P y) => [<- _|xNy]; first exact: equiv_of_refl.
      apply: set2_in_sym => //. sub.
    - apply: equiv_of_sub; auto using seq2_eqv_refl,seq2_eqv_sym,seq2_eqv_trans.
      move => {x y} [x|x] [y|y] //=; case/andP => /eqP -> /eqP ->; by rewrite seq2_eqv_io.
  Qed.

  Definition seq2 :=
    {| graph_of := merge (union G1 G2) seq2_eqv ;
       g_in := \pi_{eq_quot seq2_eqv} (inl g_in);
       g_out := \pi_{eq_quot seq2_eqv} (inr g_out) |}.
