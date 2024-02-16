Require Import compcert.lib.Integers.

Module hacspec_ints (WS : WORDSIZE).
  Module IntWS := Make(WS).
  Definition int := IntWS.int.
End hacspec_ints.

Inductive MyWORDSIZE :=
| WORDSIZE8
| WORDSIZE16
| WORDSIZE32
| WORDSIZE64
| WORDSIZE128
| WORDSIZE_usize.

Variable (WS : MyWORDSIZE).

Module WORD : WORDSIZE.
  Definition wordsize :=
    match WS with
    | WORDSIZE8 => 8
    | WORDSIZE16 => 16
    | WORDSIZE32 => 32
    | WORDSIZE64 => 64
    | WORDSIZE128 => 128
    | WORDSIZE_usize => 32
    end.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize ; destruct WS ; congruence. Qed.
End WORD.

Module MyInt := Make(WORD).
