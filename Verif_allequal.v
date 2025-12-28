(** Here is a little C program, [allequal.c]:

    #include <stddef.h>

    unsigned allequal(unsigned a[], int n) {
        int i; unsigned s;
        i = 0;
        if (n <= 0)
            return 0;

        s = a[0];
        while (i < n) {
            if (a[i] != s)
                return 1;
            i++;
        }
        return 0;
    }

    unsigned four[4] = {1,2,3,4};

    int main(void) {
        unsigned int s;
        s = allequal(four,4);
        return (int)s;
    }
*)

(** Этот файл, [Verif_allequal.v], содержит спецификацию
    корректности программы [allequal.c], и дополняется доказательством
    что программ соответствует этой спецификаци.

    Для больших программ, мы разделяем описания по древовидной структуре:
    - Функциональная модель (Обычно в форме Coq функции)
    - API спецификация
    - Доказательство корректности отдельных функций(функция на файл)
*)

(** *** Standard boilerplate *)

Require Import VST.floyd.proofauto. (* Verifiable C and its Floyd proof-automation library *)
Require Import allequal. (* AST *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** *** Functional model *)

From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint all_equal_with_Z (s : Z) (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | x :: rest =>
      if Z.eqb x s then all_equal_with_Z s rest else 1
  end.

Definition all_equal (contents : list Z) : Z :=
  match contents with
  | [] => 0
  | s :: rest => all_equal_with_Z s rest
  end.

Check Z.eqb_refl.
Lemma all_equal_with_Z_Forall_eq :
  forall s xs,
    Forall (fun x => x = s) xs ->
    all_equal_with_Z s xs = 0.
Proof.
  intros s xs Hf.
  induction Hf; simpl.
  - reflexivity.
  - rewrite <- H.
    pose proof (Z.eqb_refl x) as Zeqb_eq.
    rewrite -> Zeqb_eq.
    rewrite -> H.
    exact IHHf.
Qed.

Check Znth_0_cons.
Check Znth_pos_cons.
Lemma all_equal_with_Z_mismatch :
  forall s xs j,
    0 <= j < Zlength xs ->
    Znth j xs <> s ->
    all_equal_with_Z s xs = 1.
Proof.
  intros s xs; revert s.
  induction xs as [|x xs IH]; intros s j Hj Hneq; simpl in *.
  - rewrite Zlength_nil in Hj; lia.
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + (* j = 0 *)
      rewrite Znth_0_cons in Hneq.
      destruct (Z.eqb x s) eqn:Hx.
      * apply Z.eqb_eq in Hx; subst; contradiction.
      * reflexivity.
    + (* j > 0 *)
      assert (0 < j) by lia.
      rewrite Znth_pos_cons in Hneq by lia.
      destruct (Z.eqb x s) eqn:Hx.
      * apply Z.eqb_eq in Hx; subst.
        apply IH with (j := j - 1); [ | exact Hneq ].
        rewrite Zlength_cons in Hj; lia.
      * reflexivity.
Qed.

Check Zlength_cons.
Check Znth_0_cons.
Check Znth_pos_cons.
Check Zlength_nil.
Lemma all_equal_mismatch :
  forall l i,
    0 < Zlength l ->
    0 <= i < Zlength l ->
    Znth i l <> Znth 0 l ->
    all_equal l = 1.
Proof.
  intros l i Hlen Hi Hneq.
  destruct l as [|s xs].
  - rewrite Zlength_nil in Hlen; lia.
  - simpl in *.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + (* i = 0 -> противоречие, т.к. Znth 0 l = Znth 0 l *)
      exfalso; apply Hneq; reflexivity.
    + (* i > 0: переносим индекс в хвост *)
      assert (0 < i) by lia.
      (* all_equal (s::xs) = all_equal_with_Z s xs *)
      apply all_equal_with_Z_mismatch with (j := i - 1).
      * (* границы для i-1 *)
        rewrite Zlength_cons in Hi; lia.
      * (* несовпадение переносится в xs *)
        rewrite Znth_0_cons in Hneq.
        rewrite Znth_pos_cons in Hneq by lia.
        exact Hneq.
Qed.

(** ** API spec *)

Definition allequal_spec : ident * funspec :=
DECLARE _allequal
 WITH a : val, sh : share, contents : list Z, size : Z
 PRE [ tptr tuint, tint ]
  PROP  (readable_share sh; 0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
  PARAMS (a; Vint (Int.repr size))
  SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
 POST [ tuint ]
  PROP ()
  RETURN (Vint (Int.repr (all_equal contents)))
  SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

Print Vprog.
(* Пары : (имя, C-type) *)
(* [(_four, tarray tuint 4)] *)
Print varspecs.

(** ** Packaging the specs *)

Definition Gprog := [allequal_spec].

(** ** Proof of allequal *)

Check Zlength_nil_inv.
Lemma body_allequal : semax_body Vprog Gprog f_allequal allequal_spec.
Proof.
  start_function.
  forward. (* i = 0 *)
  forward_if.
  - forward.
    entailer!.
    (* hint. *)
    autorewrite with sublist in *|-.
    assert (Hzlen : Zlength contents = 0) by lia.
    assert (contents = []) as Hnil.
    + apply Zlength_nil_inv in Hzlen.
      exact Hzlen.
    + rewrite Hnil.
      unfold all_equal.
      reflexivity.
  (* Proof (0 <= 0 < Zlength (map Int.repr contents)) *)
  - Fail forward.
    assert_PROP (Zlength contents = size).
    + entailer!.
      rewrite Zlength_map.
      rewrite Zlength_map.
      reflexivity.
    + forward.
      forward_while
      (EX i: Z,
      PROP  (0 <= i <= size;
            (* Тут я усилил инвариант иначе не смогу последнюю ветку доказать *)
            Forall (fun x => x = Znth 0 contents) (sublist 0 i contents))
      LOCAL (temp _a a;
        temp _i (Vint (Int.repr i));
        temp _n (Vint (Int.repr size));
        temp _s (Vint (Int.repr (Znth 0 contents))))
      SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
      (* Precond удовлетворяет loop invariant *)
      * Exists 0.
        entailer!.
      (* Доказательство того что while body не крашнется *)
      * entailer!.
      (* Доказательство того что loop body сохраняет loop invar *)
      (* Тут нам надо пройти через loop body с док-вом *)
      * forward.
        forward_if.
        **  forward.
            entailer!.
            (* hint. *)
            autorewrite with sublist in *|-.
            (* hint. *)
            assert (HneqZ : Znth i contents <> Znth 0 contents).
            *** intro Heq.
                apply H5.
                rewrite Heq.
                reflexivity.
            *** assert (Hall : all_equal contents = 1).
                **** eapply all_equal_mismatch with (i := i); try lia.
                **** rewrite Hall. reflexivity.
        ** forward.
           entailer!.
           autorewrite with sublist in *|-.
           Exists (i + 1).
           (* hint. *)
           entailer!.
           assert (Hi' : 0 <= i < Zlength contents) by lia.
           
           assert (Hrange0 : 0 <= Znth 0 contents <= Int.max_unsigned).
           { eapply Forall_Znth; eauto; lia. }

           assert (Hrangei : 0 <= Znth i contents <= Int.max_unsigned).
           { eapply Forall_Znth; eauto; lia. }

           assert (HeqZ : Znth i contents = Znth 0 contents).
           { eapply repr_inj_unsigned; try eassumption; lia. }

           rewrite (sublist_split 0 i (i+1) contents) by lia.
           apply Forall_app; split.
           *** exact H4.
           *** rewrite sublist_len_1 by lia.
               constructor.
               **** exact HeqZ.
               **** constructor.
    (* precondition is the conjunction of the loop invariant and the negation of the loop test. *)
    * forward.
      entailer!.
      autorewrite with sublist in *|-.
      assert (Hall0 : all_equal contents = 0).
      ** destruct contents as [|s xs].
        *** simpl in H1. rewrite Zlength_nil in H1. lia.
        *** simpl.
            assert (Hxs : Forall (fun x : Z => x = s) xs).
            **** replace (Znth 0 (s :: xs)) with s in H4 by (simpl; reflexivity).
                 inversion H4; subst; assumption.
            **** apply all_equal_with_Z_Forall_eq in Hxs.
                 exact Hxs.
      ** rewrite Hall0; reflexivity.
Qed.
