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

Require Import VST.floyd.proofauto.
Require Import allequal.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.