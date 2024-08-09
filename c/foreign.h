value runM(struct thread_info *, value);

value signed_int_ltb(value, value);
value signed_int_leb(value, value);

value n_of_int(struct thread_info *, value);
value int_of_n(value);
value z_of_int(struct thread_info *, value);
value int_of_z(value);
value coq_argv_of_c_argv(struct thread_info *, int argc, char *argv[]);
