# vim-in-coq
A rudimentary Vim clone in Coq, compiled with CertiCoq and using ncurses via the C FFI.

## Build

```
$ git submodule init recursive
$ make
```

## Run

You can then run it on any file:

```
./edit README.md
```

Keep in mind that non-ASCII characters will not appear correctly.
