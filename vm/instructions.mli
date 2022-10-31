type long 
type ptr
type value 

val val_long : long -> value

val long_val : value -> long

val val_ptr : ptr -> value

val ptr_val : value -> ptr

val is_ptr : value -> bool

val free : ptr -> unit

val data_top : int ref 

val data : value array

val from_space : value array

val to_space : value array 

val heap_top : int ref

val sp : int ref

val stack : value array 

val acc : value ref

val env : value ref

val get : ptr -> value

val set : ptr -> value -> value

val size_val : value -> long

val tag_val : value -> long

val get_global : value -> value

val set_global : value -> value -> unit

val make_header : value -> int -> value

val get_field : value -> int -> value

val set_field : value -> int -> value -> value

val get_bytes  : value -> int -> value

val set_bytes : value -> int -> value -> value

val add_long : value -> value 

val alloc : value -> value -> value

val set_data : value -> value -> value



