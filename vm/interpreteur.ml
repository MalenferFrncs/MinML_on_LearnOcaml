open Instructions
     
     
type  rapport  = (int * int * int * int * int * int * value array * value array)
 ;;            
let array_cpy (from : value array) (idx : int ): value array =
  Array.init idx (Array.get from) 
;;
let nb_instr = ref 0;;
;;

let complet (pc : int)(env : value)(sp : int)(acc : value)(extra_args : long) (nb_instr : int)(*(stack : value array) (from_space : value array)*):rapport=
  (pc, (long_val env), sp,(long_val acc),extra_args,nb_instr,(array_cpy stack sp),(array_cpy !from_space !heap_top))

;;

let reset ?(reset_heap = true)() =
sp := 0;
stack = Array.make stack_size (val_long 0);

if reset_heap then
heap_top := 0;
from_space := Array.make !heap_size (val_long 0);
;;

let equal_rapport  ?(pc = false) ?(env = false) ?(sp = false) ?(acc = true) ?(extra_args = false) ?(nb_instr = 0) ?(stack = false) ?(heap = false)(r1 : rapport) (r2 : rapport): bool =
   match r1 with 
  (pc1,env1,sp1,acc1,extra_args1,nb_instr1,stack1,heap1)->
    match r2 with (pc2,env2,sp2,acc2,ectra_args2,nb_instr2,stack2,heap2) -> if acc1=acc2 then true 
                                                                              else failwith ("le resultat attendu dans acc est : "^(string_of_int acc2)^"\n vous retournez "^(string_of_int acc1)) 
      |_-> false
  |_-> false 

let id x = x ;;
                
let interp (code: int Array.t) (u : unit) : rapport = 
  
  nb_instr := 0;
  sp := 0;
  let indice_flash = ((Array.length code)-1) in 
  begin
    while !pc < Array.length code do
     if debug_opcode then (
      print_newline () ;
      print_string "opcode : " ; print_int code.(!pc)
      );
    
    debug_print_state ();
    
    (match code.(!pc) with
     | 0 (* ACC *) -> acc_n @@ take_argument code     
     | 1 (* PUSH *) -> push ()      
     | 2 (* PUSHACC *) -> push_acc_n @@ take_argument code
     | 3 (* POP *) -> pop_n @@ take_argument code
     | 4 (* ASSIGN *) -> assign @@ take_argument code      
     | 5 (* ENVACC *) -> env_acc_n @@ take_argument code      
     | 6 (* PUSHENVACC *) -> push_env_acc_n (take_argument code)
     | 7 (* PUSH-RETADDR *) -> let ofs = take_argument code in
         push_stack @@ val_long !extra_args;
         push_stack !env;
         push_stack @@ val_long ofs
     | 8 (* APPLY *) -> let args = take_argument code in
         extra_args := args - 1;
         pc := long_val (get_field !acc 0) - 1;
                          (* -1 annule l'incrémentation du pc en fin de boucle *)
         env := !acc
     |9  (*APPLYN *) -> 
         assert (is_ptr !acc);
         assert(let tag = tag_val !acc in 
                tag = closure_tag || 
                tag = infix_tag
               );
         let arg = pop_stack () in 
         push_stack @@ val_long !extra_args;
         push_stack !env;
         push_stack @@ val_long !pc;
         push_stack arg;
         pc := (long_val (get_field !acc 0) - 1);
         env := !acc;
         extra_args := 0

     | 10 (* APPTERM *) -> let nbargs = take_argument code in 
         let n = take_argument code in 
         appterm nbargs n
      
     | 11 (* RETURN *) -> let n = take_argument code in
         sp := !sp - n; 
         if !extra_args <= 0 
         then 
           begin
             pc := (long_val @@ pop_stack ())+1;
             env := pop_stack ();
             extra_args := long_val @@ pop_stack ()
           end
         else 
           begin
             decr extra_args;
             pc := (long_val @@
                    get_field !acc 0) - 1;
             env := !acc
           end
     | 12 (* RESTART *) -> let size = size (ptr_val !env) - 2 in
         for i = 0 to size - 1 do 
           push_stack @@ get_field !env (i+2)
         done;
         env := get_field !env 1;
         extra_args := !extra_args + size
     | 13 (* GRAB *) -> let n = take_argument code in
         if !extra_args >= n 
         then extra_args := !extra_args - n
         else 
           begin 
             acc := make_block
                 closure_tag
                 (!extra_args + 3);
             set_field !acc 0 (val_long (!pc - 2));
             set_field !acc 1 !env;
             for i = 0 to !extra_args do
               set_field !acc (i+2) (pop_stack ())
             done;
             pc := (long_val (pop_stack ())+1);
             env := pop_stack ();
             extra_args := long_val @@ pop_stack ()
           end
     | 14 (* CLOSURE *) -> let n = take_argument code in
         let addr = take_argument code in
         if n > 0 then push_stack !acc;
         acc := make_closure (!pc + addr) (n+1);
         for i = 1 to n do
           set_field !acc i (pop_stack ())
         done
     | 15 (* CLOSUREREC *) -> 
         let f = take_argument code in
         let v = take_argument code in
         let o = take_argument code in
         if v > 0 then push_stack !acc;
         let closure_size = (2 * f) - 1 + v in  
         acc := make_block closure_tag closure_size;  
         for i = 1 to f - 1 do 
           set_field !acc (2 * i - 1) (
             make_header infix_tag (2 * i)
           );
           set_field !acc (2 * i) (
             val_long @@ take_argument code
           )
         done;
         for i = 0 to v - 1 do 
           set_field !acc (i + 2 * f - 1) (pop_stack ())
         done;
         set_field !acc 0 (val_long o);
         push_stack !acc;
         for i = 1 to f - 1 do
           push_stack (val_ptr ((ptr_val !acc) + (2 * i)))
         done
      
     | 16 (* OFFSETCLOSURE *) -> offsetclosure_n @@ take_argument code
      
     | 17 (* PUSHOFFSETCLOSURE *) -> pushoffsetclosure_n @@ take_argument code
     | 18 (* GETGLOBAL *) -> let n = take_argument code in
         acc := get_global n
     | 19 (* PUSHGETGLOBAL *) -> push_stack !acc;
         let n = take_argument code in
         acc := get_global n
     | 20 (* GETGLOBALFIELD *) -> let n = take_argument code in
         let p = take_argument code in
         acc := get_field global.(n) p
     | 21 (* PUSHGETGLOBALFIELD *) -> push_stack !acc;
         let n = take_argument code in
         let p = take_argument code in
         acc := get_field global.(n) p
     | 22 (* SETGLOBAL *) -> let n = take_argument code in
         set_global n !acc;
         acc := unit      
     | 23 (* ATOM *) -> let tag = take_argument code in
         acc := make_block tag 0
     | 24 (* PUSHATOM *) -> push_stack !acc;
         let tag = take_argument code in
         acc := make_block tag 0
     | 25 (* MAKEBLOCK *) -> let sz = take_argument code in
         let tag = take_argument code in
         let blk = make_block tag sz in
         set_field blk 0 !acc;
         for i = 1 to sz - 1 do 
           set_field blk i (pop_stack ())
         done;
         acc := blk
        (*MAKEFLOATBLOCK *)
     | 26 (* GETFIELD *) -> get_field_n @@ take_argument code

      (* GETFLOATFIELD (opInput.code: 72) *)

     | 27 (* SETFIELD *) -> set_field_n @@ take_argument code

      (* 78 SETFLOATFIELD *)

     | 28 (* VECTLENGTH *) -> acc := val_long @@
           size (ptr_val !acc)
     | 29 (* GETVECTITEM *) -> let n = long_val @@ pop_stack () in
         acc := get_field !acc n
     | 30 (* SETVECTITEM *) -> let n = pop_stack () in
         let v = pop_stack () in
         set_bytes !acc (long_val n) v;
         acc := unit
     | 31 (* GETSTRINGCHAR *) -> let n = pop_stack () in
         acc := get_bytes
             !acc
             (long_val n)
     | 32 (* SETSTRINGCHAR *) -> let n = pop_stack () in
         let v = pop_stack () in
         set_bytes !acc (long_val n) (
           v
         );
         acc := unit
     | 33 (* BRANCH *) -> let n = take_argument code in 
         pc := (!pc + n) 
     | 34 (* BRANCHIF *) -> let n = take_argument code in 
         if not (is_ptr !acc) &&
            long_val !acc <> 0 
         then pc := (!pc + n) (* attention à l'adresse zéro *)
     | 35 (* BRANCHIFNOT *) -> let n = take_argument code in 
         if not (is_ptr !acc)
         && long_val !acc = 0 
         then pc := (!pc + n)  (* attention à l'adresse zéro *)
     | 36 (* SWITCH *) ->   
         (*let n = take_argument code in 
         if is_ptr !acc 
         then pc := let idx = tag (ptr_val !acc) in
                    let ofs = 2 * (n + idx) + 1 in
                    ofs - 1
         else pc := long_val !acc *)
         let n = take_argument code in
         if is_ptr !acc
         then pc := let idx = tag (ptr_val !acc) in
             !pc + code.(!pc  + idx) 
         else pc := (!pc + (code.(!pc + (long_val !acc) + 1)))
                    
     | 37 (* BOOLNOT *) ->
         acc := val_long @@ bnot (long_val !acc)
     | 38 (* PUSHTRAP *) ->
         let ofs = take_argument code in
         push_stack @@ val_long !extra_args;
         push_stack !env;
         push_stack @@ val_long !trap_sp;
         push_stack @@ val_long (!pc - 1 + ofs);
         trap_sp := !sp
     | 39 (* POPTRAP *) -> 
         pop_stack_ignore 1;
         trap_sp := long_val @@ pop_stack ();
         pop_stack_ignore 2
     | 40 (* RAISE *) -> 
         if !trap_sp = 0 then begin 
           print_string "Exception, acc = ";
           print_int @@ long_val !acc;
           print_newline () end
         else begin
           sp := !trap_sp;
           pc := long_val @@ pop_stack ();
           trap_sp := long_val @@ pop_stack ();
           env := pop_stack ();
           extra_args := long_val @@ pop_stack ()
         end
        
     | 41 (* CHECK-SIGNALS *) -> ()
     | 42 (* CONSTINT *) -> const_n @@ take_argument code
     | 43 (* PUSHCONSTINT *) -> pushconst_n @@ take_argument code
     | 44 (* NEGINT *) ->
         acc := val_long @@
           negint (long_val !acc)
     | 45 (* ADDINT *) ->
         acc := val_long @@
           addint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 46 (* SUBINT *) ->
         acc := val_long @@
           subint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 47 (* MULINT *) ->
         acc := val_long @@
           mulint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 48 (* DIVINT *) ->
         acc := val_long @@
           divint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 49 (* MODINT *) ->
         acc := val_long @@
           modint
             (long_val !acc)
             (long_val (pop_stack ()))  
     | 50 (* ANDINT *) ->
         acc := val_long @@
           andint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 51 (* ORINT  *) ->
         acc := val_long @@
           orint
             (long_val !acc)
             (long_val (pop_stack ()))  
     | 52 (* XORINT *) ->
         acc := val_long @@
           xorint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 53 (* LSLINT *) ->
         acc := val_long @@
           lslint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 54 (* LSRINT *) ->
         acc := val_long @@
           lsrint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 55 (* ASRINT *) ->
         acc := val_long @@
           asrint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 56 (* EQ *) ->
         acc := val_long @@
           eq
             (long_val !acc)
             (long_val (pop_stack ()))
     | 57 (* NEQ *) ->
         acc := val_long @@
           neq
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 58 (* LTINT *) ->
         acc := val_long @@
           ltint
             (long_val !acc)
             (long_val (pop_stack ()))  
     | 59 (* LEINT *) ->
         acc := val_long @@
           leint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 60 (* GTINT *) ->
         acc := val_long @@
           gtint
             (long_val !acc)
             (long_val (pop_stack ())) 
     | 61 (* GEINT *) ->
         acc := val_long @@
           geint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 62 (* OFFSETINT *) -> let ofs = take_argument code in 
         acc := val_long @@
           addint
             (long_val !acc)
             ofs
     | 63 (* OFFSETREF *) -> let ofs = take_argument code in
         let old = get_field !acc 0 in
         set_field !acc 0
           (val_long @@
            addint (long_val old) ofs);
         acc := unit
     | 64 (* ISINT *) -> acc := val_long @@
           isint !acc
     | 65 (* GETMETHOD *) -> (* todo *)
         let x = pop_stack () in 
         let y = get_field x 0 in
         acc := get_field y
             (long_val @@ !acc)
     | 66 (* BEQ *) -> 
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) = 0
         then pc := (!pc + ofs - 1)
     | 67 (* BNEQ *) -> 
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) <> 0
         then pc := (!pc + ofs - 1)
     | 68 (* BLTINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) < 0
         then pc := (!pc + ofs - 1)
     | 69 (* BLEINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) <= 0
         then pc := (!pc + ofs - 1)
     | 70 (* BGTINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) > 0
         then pc := (!pc + ofs - 1)
     | 71 (* BGEINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) >= 0
         then pc := (!pc + ofs - 1)
     | 72 (* ULTINT *) -> acc := val_long @@
           ultint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 73 (* UGEINT *) -> acc := val_long @@
           ugeint
             (long_val !acc)
             (long_val (pop_stack ()))
     | 74 (* BULTINT *) -> let v = take_argument code in 
         let ofs = take_argument code in
         if ultint v (long_val !acc) = 1
         then pc := (!pc + ofs - 1)

     | 75 (* BUGEINT *) -> let v = take_argument code in 
         let ofs = take_argument code in
         if ugeint v (long_val !acc) = 1
         then pc := (!pc + ofs - 1)
      (* GETPUBMET *)
      (* GETDYNMET *)

     | 76 (* STOP *) -> pc := Array.length code

      (* EVENT *)
      (* BREAK *)
      (*|77 (*CALL1*) -> *)

     | _ -> print_string "unknown opcode : ";
         print_int code.(!pc);
         print_newline ();
         exit 1; 
    );
    incr pc;
    incr nb_instr;
             
    done
  end;
  let res = (complet !pc !env !sp !acc !extra_args !nb_instr) in 
  reset () ; pc := 0 ; acc := val_long 0;
  res
;;