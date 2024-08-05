From CertiCoq.Plugin Require Import CertiCoq.

Require Import PrimInt63 NArith Ascii String.

Require Import Vim.Program Vim.Foreign.

CertiCoq Compile -unsafe-erasure -file "main" main.
CertiCoq Generate Glue -file "glue" [ nat, N, ascii, list, C.MI, exit_status ].
