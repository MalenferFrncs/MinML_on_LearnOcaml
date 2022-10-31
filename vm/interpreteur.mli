type rapport
val interp :  int Array.t -> unit -> rapport 
val equal_rapport : ?pc:bool -> ?env:bool -> ?sp:bool -> ?acc:bool -> ?extra_args:bool -> ?nb_instr:int -> ?stack:bool -> ?heap:bool -> rapport -> rapport -> bool
val id : 'a->'a