From CertiCoq.Plugin Require Import CertiCoq.

Require Import PrimInt63 NArith Ascii String.

Require Import Vim.Errors 
               Vim.Program
               Vim.Foreign.

CertiCoq Compile -unsafe-erasure -file "main" main.
CertiCoq Generate Glue -file "glue"
  [ ascii
  , C.MI
  , color
  , error
  , exit_status
  , list
  , nat
  , N
  , option
  , sum
  ].
