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

Definition all_equal (contents : list Z) : Prop.
Admitted.

(** ** API spec *)

Definition allequal_spec : ident * funspec :=
DECLARE _allequal
 WITH a: val, sh : share, contents : list Z, size: Z
 PRE [ tptr tuint, tint ]
   PROP (readable_share sh;
         0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
   PARAMS (a; Vint (Int.repr size))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
 POST [ tuint ]
   EX r: Z,
   PROP (r = 0 \/ r = 1;
         (r = 0 -> all_equal contents);
         (r = 1 -> exists j, 0 <= j < Zlength contents /\
                            Znth j contents <> Znth 0 contents))
   RETURN (Vint (Int.repr r))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(** *** main() spec *)

Definition four_contents : list Z := [1; 2; 3; 4].

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     PROP()
     RETURN (Vint (Int.repr 1))
     SEP(TT).

(** ** Packaging the specs *)

Definition Gprog := [allequal_spec; main_spec].

(** ** Proof of allequal *)

Lemma body_allequal : semax_body Vprog Gprog f_allequal allequal_spec.
Proof.
  
Admitted.

(** ** Global variables and main() *)

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.

Admitted.

(** ** Tying all the functions together *)

#[export] Existing Instance NullExtension.Espec.

Lemma prog_correct : semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.

  semax_func_cons body_allequal.
  semax_func_cons body_main.
Qed.