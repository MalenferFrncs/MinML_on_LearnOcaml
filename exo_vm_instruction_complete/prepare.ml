exception Undefined
let __ = (fun _ -> raise Undefined)

type value = Long of long | Ptr of ptr
and long = int
and ptr = int

(* transforme un entier en mlvalue *)
let val_long (n : long) : value = Long n

(* transforme un mlvalue en entier *)
let long_val (v : value) : long = 
  match v with
  | Long n -> n
  | Ptr n -> n (* cast *)

(* transforme un pointeur en mlvalue *)
let val_ptr (p : ptr) : value = Ptr p


(* transforme un mlvalue en pointeur *)
let ptr_val (v : value) : ptr =
  match v with
  | Long n -> n (* cast *)
  | Ptr p -> p

let is_ptr (v : value) : bool = 
  match v with
  | Long _ -> false
  | Ptr _ -> true


let free (ptr : 'a array) = () 

let data_size = 512
let global_size = 512
let heap_size = ref 25 (* par semi-space *)
let stack_size = 25

(* segment data *)
(* commence à l'adresse 0 *)
let data_top = ref 0
let data = Array.make data_size (val_long 0)

(* globales *)
let global_start = data_size
let global_top = ref 0
let global = Array.make global_size (val_long 0)

(* tas *)
let heap_start = global_start+global_size
let from_space = ref (Array.make !heap_size (val_long 0))
let to_space = ref (Array.make !heap_size (val_long 0))
let heap_top = ref 0

(* pile *)
let sp = ref 0
let stack = Array.make stack_size (val_long 0)

(* registres *)
let acc = ref (val_long 0)
let env = ref (val_long 0)

let bounds_ok i a =
  i >= 0 && i < Array.length a

let get ptr = 
  if ptr >= heap_start
  then let i = ptr - heap_start in 
    assert (bounds_ok i !from_space);
    (!from_space).(i) 
  else if ptr >= global_start
  then let i = ptr - global_start in 
    assert (bounds_ok i global);
    global.(i) 
  else let i = ptr in
    assert (bounds_ok i data);
    data.(i)

let set ptr v = 
  if ptr >= heap_start
  then let i = ptr - heap_start in 
    assert (bounds_ok i !from_space);
    (!from_space).(i) <- v
  else if ptr >= global_start
  then let i = ptr - global_start in 
    assert (bounds_ok i global);
    global.(i) <- v
  else let i = ptr in
    assert (bounds_ok i data);
    data.(i) <- v

let size ptr = 
  let hd = get ptr in 
  (long_val hd) / 256

(* a priori, problème si le bloc a taille >= 128 *)
let tag ptr = 
  (* a priori, problème si le bloc a taille >= 128 *)
  let hd = get ptr in 
  (long_val hd) land 255

let size_val v = size @@ ptr_val v
let tag_val v = tag @@ ptr_val v

let unit = val_long 0 

let get_global i =
  (global).(i)

let set_global i vx =
  (global).(i) <- vx

let make_header tag sz =
  val_long (tag + 256 * sz)

let get_field v i =
  get ((ptr_val v) + i +1 )

let set_field v i vx =
  set ((ptr_val v) + i +1) vx

let get_bytes v i = (* ici, on place un char par mot *)
  get_field v i

let set_bytes v i vx =  (* cf get_bytes. *)
  set_field v i vx

let no_scan_tag = 251
let string_tag = 252
let closure_tag = 247
let infix_tag = 249
let fwd_ptr_tag = 248

let add_long n =
  let p = !data_top in
  data.(p) <- val_long n;
  incr data_top;
  val_long p

let alloc tag sz =
  let p = !data_top in
  data.(p) <- make_header tag sz;
  data_top := p + sz + 1;
  p

let set_data addr i v =
  data.(addr+i+1) <- v

let add_string s =
  let z = String.length s in
  let p = alloc string_tag z in
  for i = 0 to z - 1 do
    set_data p i (val_long @@ int_of_char @@ String.get s i)
  done;
  val_ptr p

let add_unknown () = add_long 0

let push_global v = 
  global.(!global_top) <- v;
  incr global_top

let debug = false

(* ALLOC fonctions *)

let heap_can_alloc size =
  !heap_top + size < !heap_size


let next = ref 0 (* premiere position disponible dans to_space lors de la copie *)

(* libération des semi-spaces lors du redimensionnement  *) 
(* implantation en OCaml : la fonction free ne fait rien 
   (le gc se charge de libérer les objets) *)
(* implantation en mini-ml la fonction free libère le pointeur passé en argument *)
let free a = free a 

let resize_spaces size =
  (* on traite le redimensionnement des semi spaces si nécessaire *)
  let half = !heap_size / 2 in (* nombre d'éléments à la moitié d'un semi space *)
  let quarter = half / 2 in (* nombre d'élements au quart d'un semi space *)
  (* définition de la nouvelle taille *)
  let old_size = !heap_size in
  (* si il n'y a pas assez de place pour l'allocation
     on redimensionne en rajoutant a la taille la place de l'allocation
     puis multiplie le tout par deux *)
  if !heap_top + size >= !heap_size then
    heap_size := (!heap_size + size) * 2
  else 
    begin
      (* si taille + allocation < 25% de la taille de base, 
         on diminue la taille par deux *)
      if quarter > (!heap_top + size) then (* si remplis à moins de 25% *)
        heap_size := !heap_size / 2
    end;
  (* si la taille à changée *)
  if old_size <> !heap_size then
    begin
      if debug then
        begin
          print_string "resize spaces, old size : ";
          print_int old_size;
          print_string ", new size : ";
          print_int !heap_size;
          print_newline ()
        end;
      (* création du nouveau from_space à la bonne taille *)
      let new_from_space = Array.make !heap_size (val_long 0) in
      (* copie de l'ancien from_space dans le nouveau *)
      for i = 0 to !heap_top - 1 do
        new_from_space.(i) <- (!from_space).(i)
      done;
      free !from_space;
      from_space := new_from_space;
      free !to_space;
      to_space := Array.make !heap_size (val_long 0) 
    end

(* Traite le déplacement d'un bloc de to_space vers from_space si nécéssaire,   *)
(* sinon suit le fwd_ptr                                                        *)
(* value est le mlvalue pointeur vers le bloc,                                  *)
(* is_array dis si la source est un tableau ou pas : true si pile/tas , faux si env/acc *)
(* source_reg est le registre qui contient value si is_array est false (acc, env)  *)
(* source_arr est le tableau contenant value a la pos pos_arr si is_array est true (pile, tas) *)

let move_addr value is_array source_reg source_arr pos_arr =
  if is_ptr value then (* val pointe vers un bloc *)
    begin
      if ptr_val value < global_start
      || tag (ptr_val value) >= no_scan_tag 
      then () (* c'est une valeur dans le segment data, 
                 qui ne pointe vers aucune valeur allouée *)
      else if tag (ptr_val value) = fwd_ptr_tag
      then (* le bloc pointé est un fwd_ptr *)
        (* on fait pointer value sur la nouvelle destination *)
        begin
          if is_array then source_arr.(pos_arr) <- get_field value 0
          else source_reg := get_field value 0
        end
      else (* le bloc n'a pas été déplacé, on le copie *)
        begin
          let old = !next in (* sauvegarde de l'endroit où on va copier dans to_space *)
          (* on copie tout le bloc, header compris dans to_space *)
          (!to_space).(old) <- get_field value (-1); (* copie le header *)
          for j = 0 to (size (ptr_val value)) - 1 do
            (* copie tout les fields *)
            (!to_space).(old + j + 1) <- get_field value j
          done;
          next := !next + (size (ptr_val value)) + 1;
          (* prochaine pos dispo dans to_space *)
          (* on change le tag du bloc en fwd_ptr car il a été déplacé  *)
          set_field value (-1)
            (make_header fwd_ptr_tag (size (ptr_val value)));
          (* ajoute le fwd_ptr dans from_space vers la nouvelle position dans to_space *)
          set_field value 0 (val_ptr (old + heap_start)) ;
          (* on fait pointer value vers le nouveau bloc dans to_space *)
          if is_array then source_arr.(pos_arr) <- val_ptr (old + heap_start) 
          else source_reg := val_ptr (old + heap_start) 
        end
    end

(* lance le gc *)
let run_gc size =
  if debug then print_string "lancement gc\n";
  (* on parcours les éléments de la pile *)

  for i = 0 to !sp - 1 do
    let value = stack.(i) in
    move_addr value true (ref (val_long 0)) stack i
  done;

  (* on traite l'accu *)
  move_addr !acc false acc stack (-1);
  (* on traite l'env *)
  move_addr !env false env stack (-1);

  (* on parcours les variables globales *)
  for i = 0 to !global_top - 1 do
    let value = global.(i) in
    move_addr value true (ref (val_long 0)) global i
  done;

  (* maintenant on parcours les fields de tout les objets qu'on a bougé dans to_space *)
  let i = ref 0 in
  while !i < !next do (* parcours les headers *)
    let size = (long_val (!from_space).(!i)) / 256 in
    for j = !i + 1 to size do (* parcours les fields du bloc courant *)
      let value = (!from_space).(!i) in
      move_addr value true (ref (val_long 0)) !from_space !i
    done;
    i := !i + size + 1 (* passe au header du bloc suivant dans to_space *)
  done;

  (* on echange from_space et to_space *)
  let tmp = !to_space in
  to_space := !from_space;
  from_space := tmp;
  heap_top := !next;
  next := 0;
  (* on redimensionne les espaces si nécéssaire *)
  resize_spaces size;

  if debug then print_string "fin gc";
  print_newline ()


(* Alloue si possible, sinon lance le GC puis alloue *)
let alloc size = 
  if debug then
    begin
      print_newline ();
      print_string "try alloc ";
      print_int size;
      print_newline ()
    end;
  if heap_can_alloc size then
    begin
      if debug then (print_string "can alloc"; print_newline ());
      let ptr = !heap_top + heap_start in
      heap_top := !heap_top + size;
      ptr  
    end
  else 
    begin
      if debug then 
        begin
          print_string "cannot alloc";
          print_newline ()
        end;
      run_gc size;
      if heap_can_alloc size then 
        begin
          let ptr = !heap_top + heap_start  in
          heap_top := !heap_top + size;
          ptr  
        end
      else 
        begin
          if debug then 
            begin
              print_string "plus de mémoire";
              print_newline ()
            end; 
          exit 0
        end
    end
  
let isint v = 
  if is_ptr v then 0 else 1

(*** opérations arithmétiques ***)

let negint n = (-n)
let addint n1 n2 = n1 + n2 
let subint n1 n2 = n1 - n2
let mulint n1 n2 = (n1 * n2)

(*** division d'après la doc OCaml : (-x) / y = x / (-y) = -(x / y). ***)
(*** (/) 17 2       ~>  8  *)
(*** (/) 17 (-2)    ~> -8  *)
(*** (/) (-17) 2    ~> -8  *)
(*** (/) (-17) (-2) ~>  8  *)

let rec div_aux n1 n2 accu = 
  if n1 < n2 then accu
  else div_aux (n1 - n2) n2 (accu + 1)

let div n1 n2 = div_aux n1 n2 0

let divint n1 n2 =
  if n2 = 0 then failwith "divint" else
  if n1 >= 0 then (if n2 >= 0 then div n1 n2 else - (div n1 (- n2)))
  else (if n2 >= 0 then - (div (- n1) n2) else (div (- n1) (- n2)))

(*** modulo d'après la doc OCaml : `((mod) x y) < 0` si et seulement si `x < 0` ***)
(*** (mod) 11 3        ~>  2 *)
(*** (mod) 11 (-3)     ~>  2 *)
(*** (mod) (-11) 3     ~> -2 *)
(*** (mod) (-11) (-3)  ~> -2 *)

let rec modulo n1 n2 =
  if n1 < n2 then n1
  else modulo (n1 - n2) n2

let rec modint n1 n2 = (* dans un premier temps, on suppose que n2 >= 0 ***)
  if n2 = 0 then failwith "modint" else
  if n1 < 0 then - (modulo (- n1) (abs n2)) else (modulo n1 (abs n2))


(*** opérations logiques ***)

let andint n1 n2 = 
  if n1 <> 0 && n2 <> 0 then 1 else 0

let orint n1 n2 = 
  if n1 <> 0 || n2 <> 0 then 1 else 0

let xorint n1 n2 = 
  if (n1 <> 0 && n2 = 0) || (n1 <> 0 && n2 = 0) then 1 else 0

let bnot n = 
  if n = 0 then 1 else 0

(*** opérations de décalage ***)
(*** dans un premier temps, on suppose que le déplacement est toujours >= 0 ***)
(*** dans un premier temps, on ne fait pas de distinction entre lsr et asr  ***)
let rec lslint n dep =
  if dep = 0 then n
  else lslint (n + n) (dep - 1)

let rec lsrint n dep =
  if dep = 0 then n
  else lsrint (n / 2) (dep - 1)

let asrint n1 n2 = lsrint n1 n2 

(*** opérations de comparaison ***)

(*** égalité physique ***)
let eq n1 n2 = 
  if n1 = n2 then 1 else 0

(*** différence physique ***)
let neq n1 n2 = 
  if n1 <> n2 then 1 else 0

let ltint n1 n2 = 
  if n1 < n2 then 1 else 0

let leint n1 n2 = 
  if n1 <= n2 then 1 else 0

let gtint n1 n2 = 
  if n1 > n2 then 1 else 0

let geint n1 n2 = 
  if n1 >= n2 then 1 else 0

let compare_imm n1 n2 =
  if n1 < n2 then -1 else if n1 > n2 then 1 else 0

(*** comparaison (<) non signée               ***)
(*** n1 < 0 && n2 >= 0 => (ultint n1 n2) ~> 0 ***)
let ultint n1 n2 =
  if n1 < 0 then (if n2 < 0 then gtint n1 n2 else 0)
  else if n2 < 0 then 0 else ltint n1 n2

(*** comparaison (>=) non signée              ***)
(*** n1 < 0 && n2 >= 0 => (ugeint n1 n2) ~> 1 ***)
let ugeint n1 n2 =
  if n1 < 0 then (if n2 < 0 then leint n1 n2 else 1)  
  else if n2 < 0 then 1 else geint n1 n2



let make_block tag sz =
  let sz = if sz = 0 then 1 else sz in
  let a = alloc (sz + 1) in
  (!from_space).(a-heap_start) <- make_header tag sz;
  val_ptr a

let make_closure pc size =
  let res = make_block closure_tag size in
  set_field res 0 (val_long pc);
  res


let debug = false
let debug_opcode = false
let debug_pc = false
let debug_data = false

let pc = ref 0
let extra_args = ref 0 
let trap_sp = ref 0

let pop_stack () =
  assert (!sp > 0);
  let v = stack.(!sp - 1) in 
  decr sp;
  v

let pop_stack_ignore n =
  assert (!sp >= n);
  sp := !sp - n

let stack_overflow () = 
  failwith "stack overflow vm "

let push_stack v =
  if !sp >= (stack_size - 1) then stack_overflow (); 
  stack.(!sp) <- v; incr sp

let take_argument code =
  incr pc;
  code.(!pc)

let rec debug_print_block block =
  begin
    print_string "(block[";
    print_int (ptr_val block);
    print_string "], size : ";
    print_int (size (ptr_val block));
    print_string ", tag : ";
    print_int (tag (ptr_val block));
    print_string ") ";
    print_string "{";
    (* attention, cela peut boucler sur des valeurs cycliques : *)
    (*
       for i = 0 to size (ptr_val block) - 1 do 
        print_string "<";
        if is_ptr (get_field block i) then
          debug_print_block (get_field block i)
        else
          print_int (long_val (get_field block i));
        print_string ">";
        print_string " | "
      done;
     *)
    print_string "}"; 
    print_newline ()
  end

let debug_print_arr arr arr_end name =
  begin
    print_newline ();
    print_string name;
    print_string " :";
    print_newline ();
    for i = 0 to arr_end do  
      if is_ptr arr.(i) then 
        debug_print_block (arr.(i))
      else begin
        print_int (long_val arr.(i)) 
      end;
      print_string " | " 
    done;
    print_newline ()
  end

let debug_print_state () = 
  (if debug_pc then
     begin
       print_newline ();
       print_string "pc: "; 
       print_int (!pc) ; 
       print_newline ()
     end);
  (if debug then
     begin
       print_newline ();
       print_string "pc: "; 
       print_int (!pc);
       print_string ", acc: "; 
       if is_ptr !acc then 
         debug_print_block !acc
       else 
         print_int (long_val !acc);
       print_string ", env: ";
       if is_ptr (!env) then
         debug_print_block (!env)
       else 
         print_int (long_val !env);
       print_string ", sp: "; 
       print_int !sp;
       print_string ", extra args: ";
       print_int !extra_args;
       print_newline ();
       debug_print_arr stack (!sp-1) "stack";
       debug_print_arr !from_space
         (!heap_top - 1 - heap_start) "from_space"
     end);
  if debug_data
  then begin debug_print_arr global (!global_top - 1) "global";
    debug_print_arr data (!data_top - 1) "data"
  end
  
(* print_string " global: ";
 if is_ptr (!global) then
 debug_print_block (!global);
 print_newline (); *)

let acc_n n = 
  acc := stack.(!sp - n-1)

let push () = 
  push_stack !acc

let push_acc_n n = 
  push_stack !acc; 
  acc := stack.(!sp - n-1)

let pop_n n =
  assert (!sp >= n);
  sp := !sp - n

let assign n =
  stack.(!sp-1-n) <- !acc; 
  acc := val_long 0

let env_acc_n n = 
  acc := get_field !env n

let push_env_acc_n n =
  push_stack !acc; 
  acc := get_field !env n

let offsetclosure_n n =
  acc := val_ptr (ptr_val !env + n)

let pushoffsetclosure_n n =
  push_stack !acc;
  acc := val_ptr (ptr_val !env + n)

let get_field_n n =
  assert (is_ptr !acc);
  acc := get_field !acc n

let set_field_n n =
  assert (is_ptr !acc);
  set_field !acc n (pop_stack ()); acc := unit 

let const_n n =
  acc := val_long n

let pushconst_n n =
  push_stack !acc;
  acc := val_long n

let appterm nargs n =
  for i = 0 to nargs - 1 do
    stack.(!sp - n + i) <- stack.(!sp - nargs + i) 
  done;
  pop_stack_ignore (n-nargs);
  pc := long_val (get_field !acc 0) - 1;
  env := !acc;
  extra_args := !extra_args + nargs - 1




let interp code =
  sp := 0;
  pc := 0;
  while !pc < Array.length code do
    if debug_opcode then (
      print_newline () ;
      print_string "opcode : " ; print_int code.(!pc)
    );
    debug_print_state ();
    begin
      match code.(!pc) with
      | 0 (* ACC0 *) -> acc_n 0
      | 1 (* ACC1 *) -> acc_n 1
      | 2 (* ACC2 *) -> acc_n 2
      | 3 (* ACC3 *) -> acc_n 3
      | 4 (* ACC4 *) -> acc_n 4
      | 5 (* ACC5 *) -> acc_n 5
      | 6 (* ACC6 *) -> acc_n 6
      | 7 (* ACC7 *) -> acc_n 7
      | 8 (* ACC *) -> acc_n @@ take_argument code
      | 9 (* PUSH *) -> push ()
      | 10 (* PUSHACC0 *) -> push ()
      | 11 (* PUSHACC1 *) -> push_acc_n 1
      | 12 (* PUSHACC2 *) -> push_acc_n 2
      | 13 (* PUSHACC3 *) -> push_acc_n 3
      | 14 (* PUSHACC4 *) -> push_acc_n 4
      | 15 (* PUSHACC5 *) -> push_acc_n 5
      | 16 (* PUSHACC6 *) -> push_acc_n 6
      | 17 (* PUSHACC7 *) -> push_acc_n 7
      | 18 (* PUSHACC *) -> push_acc_n @@ take_argument code
      | 19 (* POP *) -> pop_n @@ take_argument code
      | 20 (* ASSIGN *) -> assign @@ take_argument code
      | 21 (* ENVACC1 *) -> env_acc_n 1
      | 22 (* ENVACC2 *) -> env_acc_n 2
      | 23 (* ENVACC3 *) -> env_acc_n 3
      | 24 (* ENVACC4 *) -> env_acc_n 4
      | 25 (* ENVACC *) -> env_acc_n @@ take_argument code
      | 26 (* PUSHENVACC1 *) -> push_env_acc_n 1
      | 27 (* PUSHENVACC2 *) -> push_env_acc_n 2
      | 28 (* PUSHENVACC3 *) -> push_env_acc_n 3
      | 29 (* PUSHENVACC4 *) -> push_env_acc_n 4
      | 30 (* PUSHENVACC *) -> push_env_acc_n (take_argument code)
      | 31 (* PUSH-RETADDR *) -> let ofs = take_argument code in
                                 push_stack @@ val_long !extra_args;
                                 push_stack !env;
                                 push_stack @@ val_long ofs
      | 32 (* APPLY *) -> let args = take_argument code in
                          extra_args := args - 1;
                          pc := long_val (get_field !acc 0) - 1;
                          (* -1 annule l'incrémentation du pc en fin de boucle *)
                          env := !acc
      | 33 (* APPLY1 *) -> assert (is_ptr !acc);
                           assert(let tag = tag_val !acc in 
                                  tag = closure_tag || 
                                    tag = infix_tag
                             );
                           let arg = pop_stack () in
                           push_stack @@ val_long !extra_args;
                           push_stack !env;
                           push_stack @@ val_long !pc;
                           push_stack arg;
                           pc := long_val (get_field !acc 0) - 1;
                           env := !acc;
                           extra_args := 0
      | 34 (* APPLY2 *) -> let arg1 = pop_stack () in
                           let arg2 = pop_stack () in
                           push_stack @@ val_long !extra_args;
                           push_stack @@ !env;
                           push_stack @@ val_long !pc;
                           push_stack arg2;
                           push_stack arg1;
                           pc := long_val (get_field !acc 0) - 1;
                           env := !acc;
                           extra_args := 1
      | 35 (* APPLY3 *) -> let arg1 = pop_stack () in
                           let arg2 = pop_stack () in
                           let arg3 = pop_stack () in
                           push_stack @@ val_long !extra_args;
                           push_stack !env;
                           push_stack @@ val_long !pc;
                           push_stack arg3;
                           push_stack arg2;
                           push_stack arg1;
                           pc := long_val (get_field !acc 0) - 1;
                           env := !acc;
                           extra_args := 2
      | 36 (* APPTERM *) -> let nbargs = take_argument code in 
                            let n = take_argument code in 
                            appterm nbargs n
      | 37 (* APPTERM1 *) -> appterm 1 (take_argument code) 
      | 38 (* APPTERM2 *) -> appterm 2 (take_argument code)
      | 39 (* APPTERM3 *) -> appterm 3 (take_argument code)
      | 40 (* RETURN *) -> let n = take_argument code in
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
      | 41 (* RESTART *) ->
         let size = size (ptr_val !env) - 2 in
         for i = 0 to size - 1 do 
           push_stack @@ get_field !env (i+2)
         done;
         env := get_field !env 1;
         extra_args := !extra_args + size
      | 42 (* GRAB *) -> let n = take_argument code in
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
                             pc := long_val (pop_stack ());
                             env := pop_stack ();
                             extra_args := long_val @@ pop_stack ()
                           end
      | 43 (* CLOSURE *) -> let n = take_argument code in
         let addr = take_argument code in
         if n > 0 then push_stack !acc;
         acc := make_closure (!pc + addr) (n+1);
         for i = 1 to n do
           set_field !acc i (pop_stack ())
         done
      | 44 (* CLOSUREREC *) -> 
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
      | 45 (* OFFSETCLOSUREM2 *) -> offsetclosure_n (-2)
      | 46 (* OFFSETCLOSURE0 *) -> offsetclosure_n 0
      | 47 (* OFFSETCLOSURE2 *) -> offsetclosure_n 2
      | 48 (* OFFSETCLOSURE *) -> offsetclosure_n @@ take_argument code
      | 49 (* PUSHOFFSETCLOSUREM2 *) -> pushoffsetclosure_n (-2)
      | 50 (* PUSHOFFSETCLOSURE0 *) -> pushoffsetclosure_n 0
      | 51 (* PUSHOFFSETCLOSURE2 *) -> pushoffsetclosure_n 2
      | 52 (* PUSHOFFSETCLOSURE *) -> pushoffsetclosure_n @@ take_argument code
      | 53 (* GETGLOBAL *) -> let n = take_argument code in
                              acc := get_global n
      | 54 (* PUSHGETGLOBAL *) -> push_stack !acc;
                                  let n = take_argument code in
                                  acc := get_global n
      | 55 (* GETGLOBALFIELD *) -> let n = take_argument code in
                                   let p = take_argument code in
                                   acc := get_field (val_long n) p
      | 56 (* PUSHGETGLOBALFIELD *) -> push_stack !acc;
                                       let n = take_argument code in
                                       let p = take_argument code in
                                       acc := get_field (val_long n) p
      | 57 (* SETGLOBAL *) -> let n = take_argument code in
                              set_global n !acc;
                              acc := unit
      | 58 (* ATOM0 *) -> acc := make_block 0 0
      | 59 (* ATOM *) -> let tag = take_argument code in
                         acc := make_block tag 0
      | 60 (* PUSHATOM0 *) -> push_stack !acc;
                              acc := make_block 0 0
      | 61 (* PUSHATOM *) -> push_stack !acc;
                             let tag = take_argument code in
                             acc := make_block tag 0
      | 62 (* MAKEBLOCK *) -> let sz = take_argument code in
                              let tag = take_argument code in
                              let blk = make_block tag sz in
                              set_field blk 0 !acc;
                              for i = 1 to sz - 1 do 
                                set_field blk i (pop_stack ())
                              done;
                              acc := blk
      | 63 (* MAKEBLOCK1 *) -> let tag = take_argument code in
                               let blk = make_block tag 1 in
                               set_field blk 0 !acc;
                               acc := blk
      | 64 (* MAKEBLOCK2 *) -> let tag = take_argument code in
                               let blk = make_block tag 2 in
                               set_field blk 0 !acc;
                               set_field blk 1 (pop_stack ());
                               acc := blk
      | 65 (* MAKEBLOCK3 *) -> let tag = take_argument code in
                               let blk = make_block tag 3 in
                               set_field blk 0 !acc;
                               set_field blk 1 (pop_stack ());
                               set_field blk 2 (pop_stack ());
                               acc := blk

      (* 66 MAKEFLOATBLOCK *)

      | 67 (* GETFIELD0 *) -> get_field_n 0
      | 68 (* GETFIELD1 *) -> get_field_n 1
      | 69 (* GETFIELD2 *) -> get_field_n 2
      | 70 (* GETFIELD3 *) -> get_field_n 3
      | 71 (* GETFIELD *) -> get_field_n @@ take_argument code

      (* GETFLOATFIELD (opInput.code: 72) *)

      | 73 (* SETFIELD0 *) -> set_field_n 0
      | 74 (* SETFIELD1 *) -> set_field_n 1
      | 75 (* SETFIELD2 *) -> set_field_n 2
      | 76 (* SETFIELD3 *) -> set_field_n 3
      | 77 (* SETFIELD *) -> set_field_n @@ take_argument code

      (* 78 SETFLOATFIELD *)

      | 79 (* VECTLENGTH *) -> acc := val_long @@
                                               size (ptr_val !acc)
      | 80 (* GETVECTITEM *) -> let n = long_val @@ pop_stack () in
                                acc := get_field !acc n
      | 81 (* SETVECTITEM *) -> let n = pop_stack () in
                                let v = pop_stack () in
                                set_bytes !acc (long_val n) v;
                                acc := unit
      | 82 (* GETSTRINGCHAR *) -> let n = pop_stack () in
                                  acc := get_bytes
                                                  !acc
                                                  (long_val n)
      | 83 (* SETBYTESCHAR *) -> let n = pop_stack () in
                                 let v = pop_stack () in
                                 set_bytes !acc (long_val n) (
                                     pop_stack ()
                                   );
                                 acc := unit
      | 84 (* BRANCH *) -> let n = take_argument code in 
                           pc := n + !pc
      | 85 (* BRANCHIF *) -> let n = take_argument code in 
                             if not (is_ptr !acc) &&
                                  long_val !acc <> 0 
                             then pc := n + !pc (* attention à l'adresse zéro *)
      | 86 (* BRANCHIFNOT *) -> let n = take_argument code in 
                                if not (is_ptr !acc)
                                   && long_val !acc = 0 
                                then pc := n + !pc  (* attention à l'adresse zéro *)
      | 87 (* SWITCH *) ->   
         let n = take_argument code in 
         if is_ptr !acc 
         then pc := let idx = tag (ptr_val !acc) in
                    let ofs = 2 * (n + idx) + 1 in
                    ofs - 1
         else pc := long_val !acc
      | 88 (* BOOLNOT *) ->
         acc := val_long @@ bnot (long_val !acc)
      | 89 (* PUSHTRAP *) ->
         let ofs = take_argument code in
         push_stack @@ val_long !extra_args;
         push_stack !env;
         push_stack @@ val_long !trap_sp;
         push_stack @@ val_long (!pc - 1 + ofs);
         trap_sp := !sp
      | 90 (* POPTRAP *) -> 
         pop_stack_ignore 1;
         trap_sp := long_val @@ pop_stack ();
         pop_stack_ignore 2
      | 91 (* RAISE *) -> 
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
        
      | 92 (* CHECK-SIGNALS *) -> ()

      (*| 93 (* C-CALL1 *) ->
         (*let p = take_argument code in
         push_stack !env; 
         acc := (match p with
                        | 0 -> n2t_print_int_code     !acc
                        | 1 -> n2t_print_newline_code !acc
                        | 2 -> n2t_print_char_code    !acc
                        | 3 -> n2t_print_string_code  !acc        
                        | 4 -> n2t_array_length_code  !acc
                        | 5 -> caml_fresh_oo_id_code  !acc
                        | 6 -> caml_array_concat_code !acc  
                        | _ -> not_available ());
         pop_stack_ignore 1*)
      | 94 (* C-CALL2 *) -> 
         (*let p = take_argument code in
         let v = pop_stack () in
         push_stack !env; 
         acc := (match p with
                        | 0 -> caml_make_vect_code !acc v
                        | 1 -> caml_array_get_addr_code !acc v
                        | 2 -> caml_greaterequal_code !acc v
                        | 3 -> caml_lessequal_code !acc v
                        | 4 -> caml_lessthan_code !acc v
                        | 5 -> caml_int_compare_code !acc v
                        | 6 -> caml_array_append_code !acc v                     
                        | _ -> not_available ());
         pop_stack_ignore 1 *)
      | 95 (* C-CALL3 *) ->
         (*let p = take_argument code in
         let v1 = pop_stack () in
         let v2 = pop_stack () in
         push_stack !env; 
         acc := (match p with
                        | 0 -> caml_array_set_addr_code !acc v1 v2
                        | 1 -> caml_array_sub_code !acc v1 v2
                        | _ -> not_available ());
         env := pop_stack () *)
      | 96 (* C-CALL4 *) -> 
         (* let p = take_argument code in
         let v1 = pop_stack () in
         let v2 = pop_stack () in
         let v3 = pop_stack () in
         push_stack !env; 
         acc := (match p with
                        | _ -> not_available ());
         env := pop_stack () *)
      | 97 (* C-CALL5 *) -> 
         (*let p = take_argument code in
         let v1 = pop_stack () in
         let v2 = pop_stack () in
         let v3 = pop_stack () in
         let v4 = pop_stack () in
         push_stack !env; 
         acc := (match p with
                        | 0 -> caml_array_blit_code !acc v1 v2 v3 v4
                        | _ -> not_available ());
         env := pop_stack () *)
      (* 98 C-CALLN *) *)
      | 99  (* CONST0 *) -> const_n 0
      | 100 (* CONST1 *) -> const_n 1
      | 101 (* CONST2 *) -> const_n 2
      | 102 (* CONST3 *) -> const_n 3
      | 103 (* CONSTINT *) -> const_n @@ take_argument code
      | 104 (* PUSHCONST0 *) -> pushconst_n 0
      | 105 (* PUSHCONST1 *) -> pushconst_n 1
      | 106 (* PUSHCONST2 *) -> pushconst_n 2
      | 107 (* PUSHCONST3 *) -> pushconst_n 3
      | 108 (* PUSHCONSTINT *) -> pushconst_n @@ take_argument code
      | 109 (* NEGINT *) ->
         acc := val_long @@
                         negint (long_val !acc)
      | 110 (* ADDINT *) ->
         acc := val_long @@
                         addint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 111 (* SUBINT *) ->
         acc := val_long @@
                         subint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 112 (* MULINT *) ->
         acc := val_long @@
                         mulint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 113 (* DIVINT *) ->
         acc := val_long @@
                         divint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 114 (* MODINT *) ->
         acc := val_long @@
                         modint
                           (long_val !acc)
                           (long_val (pop_stack ()))  
      | 115 (* ANDINT *) ->
         acc := val_long @@
                         andint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 116 (* ORINT  *) ->
         acc := val_long @@
                         orint
                           (long_val !acc)
                           (long_val (pop_stack ()))  
      | 117 (* XORINT *) ->
         acc := val_long @@
                         xorint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 118 (* LSLINT *) ->
         acc := val_long @@
                         lslint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 119 (* LSRINT *) ->
         acc := val_long @@
                         lsrint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 120 (* ASRINT *) ->
         acc := val_long @@
                         asrint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 121 (* EQ *) ->
         acc := val_long @@
                         eq
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 122 (* NEQ *) ->
         acc := val_long @@
                         neq
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 123 (* LTINT *) ->
         acc := val_long @@
                         ltint
                           (long_val !acc)
                           (long_val (pop_stack ()))  
      | 124 (* LEINT *) ->
         acc := val_long @@
                         leint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 125 (* GTINT *) ->
         acc := val_long @@
                         gtint
                           (long_val !acc)
                           (long_val (pop_stack ())) 
      | 126 (* GEINT *) ->
         acc := val_long @@
                         geint
                           (long_val !acc)
                           (long_val (pop_stack ()))
      | 127 (* OFFSETINT *) -> let ofs = take_argument code in 
                               acc := val_long @@
                                               addint
                                                 (long_val !acc)
                                                 ofs
      | 128 (* OFFSETREF *) -> let ofs = take_argument code in
                               let old = get_field !acc 0 in
                               set_field !acc 0
                                 (val_long @@
                                    addint (long_val old) ofs);
                               acc := unit
      | 129 (* ISINT *) -> acc := val_long @@
                                           isint !acc
      | 130 (* GETMETHOD *) -> (* todo *)
         let x = pop_stack () in 
         let y = get_field x 0 in
         acc := get_field y
                         (long_val @@ !acc)
      | 131 (* BEQ *) -> 
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) = 0
         then pc := (!pc + ofs - 1)
      | 132 (* BNEQ *) -> 
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) <> 0
         then pc := (!pc + ofs - 1)
      | 133 (* BLTINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) < 0
         then pc := (!pc + ofs - 1)
      | 134 (* BLEINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) <= 0
         then pc := (!pc + ofs - 1)
      | 135 (* BGTINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) > 0
         then pc := (!pc + ofs - 1)
      | 136 (* BGEINT *) ->
         let v = take_argument code in
         let ofs = take_argument code in
         if compare_imm v (long_val !acc) >= 0
         then pc := (!pc + ofs - 1)
      | 137 (* ULTINT *) -> acc := val_long @@
                                            ultint
                                              (long_val !acc)
                                              (long_val (pop_stack ()))
      | 138 (* UGEINT *) -> acc := val_long @@
                                            ugeint
                                              (long_val !acc)
                                              (long_val (pop_stack ()))
      | 139 (* BULTINT *) -> let v = take_argument code in 
                             let ofs = take_argument code in
                             if ultint v (long_val !acc) = 1
                             then pc := (!pc + ofs - 1)

      | 140 (* BUGEINT *) -> let v = take_argument code in 
                             let ofs = take_argument code in
                             if ugeint v (long_val !acc) = 1
                             then pc := (!pc + ofs - 1)
      (* GETPUBMET *)
      (* GETDYNMET *)

      | 143 (* STOP *) -> pc := Array.length code

      (* EVENT *)
      (* BREAK *)

      | _ -> print_string "unknown opcode : ";
             print_int code.(!pc);
             print_newline ();
             exit 1
    end;
    incr pc;

    let print_array (x  : value array )=
      let print_value (x : value) = 
        print_int (long_val x) ;
        print_string ";"
      in
    Array.map print_value x 
    in
  
    print_string "\n stack : ";
    print_array stack;
    print_string "\n from_space : ";
    print_array !from_space;
    print_string "\n env : ";
    print_int (long_val !env);
    print_string " pc : ";print_int (!pc);
    print_string " acc : ";print_int (long_val !acc);
    print_string " extra_arg : "; print_int (!extra_args);
    print_string " sp : " ; print_int (!sp);
  

  done

  
(** la fonction get_op_code renvoie la chaine de carractère correspondant a l'instruction instr
Ex: get_op_code "ACC2" -> "2" *) 

let get_op_code (instr : string) : string = 
  match instr with  
  | "ACC0"                      -> "0"
  | "ACC1"                      -> "1"
  | "ACC2"                      -> "2"
  | "ACC3"                      -> "3"
  | "ACC4"                      -> "4"
  | "ACC5"                      -> "5"
  | "ACC6"                      -> "6"
  | "ACC7"                      -> "7"
  | "ACC"                    -> "8"
  | "PUSH"                      -> "9" 
  | "PUSHACC0"                  -> "10"
  | "PUSHACC1"                  -> "11"
  | "PUSHACC2"                  -> "12"
  | "PUSHACC3"                  -> "13"
  | "PUSHACC4"                  ->  "14"
  | "PUSHACC5"                  ->  "15"
  | "PUSHACC6"                  ->  "16"
  | "PUSHACC7"                  ->  "17"
  | "PUSHACC"                 ->  "18"
  | "POP"                     ->  "19"
  | "ASSIGN"                  ->  "20"
  | "ENVACC1"                   ->  "21"
  | "ENVACC2"                   ->  "22"
  | "ENVACC3"                   ->  "23"
  | "ENVACC4"                   -> "24"
  | "ENVACC"                ->  "25"
  | "PUSHENVACC1"               ->  "26"
  | "PUSHENVACC2"               ->  "27"
  | "PUSHENVACC3"               ->  "28"
  | "PUSHENVACC4"               ->  "29"
  | "PUSHENVACC"              ->  "30"
  | "PUSH_RETADDR"          ->  "31"
  | "APPLY"                   ->  "32"
  | "APPLY1"                    ->  "33"
  | "APPLY2"                    ->  "34"
  | "APPLY3"                    ->  "35"
  | "APPTERM"             ->  "36"
  | "APPTERM1"                 ->  "37"
  | "APPTERM2"                 ->  "38"
  | "APPTERM3"                 ->  "39"
  | "RETURN"                   ->  "40"
  | "RESTART"                   ->  "41"
  | "GRAB"                    ->  "42"
  | "CLOSURE"           ->  "43"
  | "CLOSUREREC"    ->  "44"
  | "OFFSETCLOSUREM2"           ->  "45"
  | "OFFSETCLOSURE0"            ->  "46"
  | "OFFSETCLOSURE2"            ->  "47"
  | "OFFSETCLOSURE"            ->  "48"
  | "PUSHOFFSETCLOSUREM2"       ->  "49"
  | "PUSHOFFSETCLOSURE0"        ->  "50"
  | "PUSHOFFSETCLOSURE2"        ->  "51"
  | "PUSHOFFSETCLOSURE"        ->  "52"
  | "GETGLOBAL"                ->  "53"
  | "PUSHGETGLOBAL"            ->  "54"
  | "GETGLOBALFIELD"      ->  "55"
  | "PUSHGETGLOBALFIELD"  ->  "56"
  | "SETGLOBAL"                ->  "57"
  | "ATOM0"                     ->  "58"
  | "ATOM"                   ->  "59"
  | "PUSHATOM0"                 ->  "60"
  | "PUSHATOM"               ->  "61"
  | "MAKEBLOCK"        ->  "62"
  | "MAKEBLOCK1"            ->  "63"
  | "MAKEBLOCK2"             ->  "64"
  | "MAKEBLOCK3"             ->  "65"
  | "MAKEFLOATBLOCK"          ->  "66"
  | "GETFIELD0"                 ->  "67"
  | "GETFIELD1"                 ->  "68"
  | "GETFIELD2"                 ->  "69"
  | "GETFIELD3"                 ->  "70"
  | "GETFIELD"                 ->  "71"
  | "GETFLOATFIELD"            ->  "72"
  | "SETFIELD0"                 ->  "73"
  | "SETFIELD1"                 ->  "74"
  | "SETFIELD2"                 ->  "75"
  | "SETFIELD3"                 ->  "76"
  | "SETFIELD"                ->  "77"
  | "SETFLOATFIELD"            ->  "78"
  | "VECTLENGTH"                ->  "79"
  | "GETVECTITEM"               ->  "80"
  | "SETVECTITEM"               ->  "81"
  | "GETBYTESCHAR"              ->  "82"
  | "SETBYTESCHAR"              ->  "83"
  | "BRANCH"                ->  "84"
  | "BRANCHIF"               ->  "85"
  | "BRANCHIFNOT"           ->  "86"
  | "SWITCH"           ->  "87"
  | "BOOLNOT"                   ->  "88"
  | "PUSHTRAP"              ->  "89"
  | "POPTRAP"                   ->  "90"
  | "RAISE"                     ->  "91"
  | "CHECK_SIGNALS"             ->  "92"
  | "C_CALL1"                ->  "93"
  | "C_CALL2"                ->  "94"
  | "C_CALL3"               ->  "95"
  | "C_CALL4"               ->  "96"
  | "C_CALL5"                ->  "97"
  | "C_CALLN"        ->  "98"
  | "CONST0"                    ->  "99"
  | "CONST1"                    ->  "100"
  | "CONST2"                    ->  "101"
  | "CONST3"                    ->  "102"
  | "CONSTINT"                 -> "103"
  | "PUSHCONST0"                ->  "104"
  | "PUSHCONST1"                ->  "105"
  | "PUSHCONST2"                ->  "106"
  | "PUSHCONST3"                ->  "107"
  | "PUSHCONSTINT"            ->  "108"
  | "NEGINT"                    ->  "109"
  | "ADDINT"                    ->  "110"
  | "SUBINT"                    ->  "111"
  | "MULINT"                    ->  "112"
  | "DIVINT"                    ->  "113"
  | "MODINT"                    ->  "114"
  | "ANDINT"                    ->  "115"
  | "ORINT"                     ->  "116"
  | "XORINT"                    ->  "117"
  | "LSLINT"                    ->  "118"
  | "LSRINT"                    ->  "119"
  | "ASRINT"                    ->  "120"
  | "EQ"                        ->  "121"
  | "NEQ"                       ->  "122"
  | "LTINT"                     ->  "123"
  | "LEINT"                     ->  "124"
  | "GTINT"                     ->  "125"
  | "GEINT"                     ->  "126"
  | "OFFSETINT"                ->  "127"
  | "OFFSETREF"                ->  "128"
  | "ISINT"                     -> "129"
  | "GETMETHOD"                 ->  "130"
  | "BEQ"               ->  "131"
  | "BNEQ"              ->  "132"
  | "BLTINT"            ->  "133"
  | "BLEINT"            ->  "134"
  | "BGTINT"            ->  "135"
  | "BGEINT"            ->  "136"
  | "ULTINT"                    ->  "137"
  | "UGEINT"                    ->  "138"
  | "BULTINT"           ->  "139"
  | "BUGEINT"           ->  "140"
  | "GETPUBMET"     ->  "141"
  | "GETDYNMET"                 ->  "142"
  | "STOP"                      ->  "143"
  | "EVENT"                     ->  "144"
  | "BREAK"                     ->  "145"
  | "RERAISE"                   ->  "146"
  | "RAISE_NOTRACE"             ->  "147"
  | "GETSTRINGCHAR"             ->  "148"
  | _ -> failwith "mauvaise instr"

(** opcode_from_string renvoie l'entier associer a l'instruction instr
Ex : ACC2 -> 2 *)
let opcode_from_string instr = 
  int_of_string (get_op_code instr)
          
(** retourne un tableau tableau d'entier a partir d'une liste d'entier *)
let array_from_list (l1 : int list ) = 
  let taille = (List.length l1) in
  let arrayInst = (Array.make taille 0)in
  let cmp = ref 0 in
  let put_int (arr : int array) (value : int) : unit = 
    arr.(!cmp)<-value ;
    cmp := (!cmp+1) ;
  in
  List.map (put_int arrayInst) l1 ;
  arrayInst

(** retourne l'entier correspondant a l'etiquette de la chaine s *)
let rec tag_of_string (s : string) (tag : string)= 
    let x = s.[0] in 
    match x with 
      ':' | ' '  ->  tag 
    | '1'| '2'| '3'| '4'| '5'| '6'| '7'| '8'| '9'| '0' -> tag_of_string (String.sub s 1 ((String.length s)-1) )  (tag ^ (String.make 1 x) )
    |_ -> "erreur tag"
  
(** retire les virgules de la chaine s *)
let remove_virg (s :string) :string =
    if  String.contains s ',' then
      if s.[(String.length s)-1]= ','  then
        String.sub s 0 ((String.length s)-1)
      else String.sub s 1 (String.length s)
    else s


(** retourne le tableau d'entier correspondant a la suite d'instruction generé par -dinstr du compilateur
ocamlc *)
let dinstr_trad (dinstr :string) : int array =
  let lisnt = (List.map (String.trim) (String.split_on_char '\n' dinstr)) in
  let l_notag = ref [] in
  let pc = ref 0 in
  let arr = ref (Array.make 10 0) in
  
  let incr_pc (inst : string) : unit =
    l_notag := !l_notag @ [inst];
    let linst = String.split_on_char ' ' (String.trim inst) in
    pc := !pc + List.length linst;
  in
  
  
  
  let rec notebranche (linst : string list) : unit = 
    match linst with 
      []-> ()
    |instr::l' -> 
        if (instr.[0] = 'L') then (
          let listr = String.split_on_char '\t' instr in
          let stag = List.hd listr in
          let tag = tag_of_string (String.sub stag 1 ((String.length stag)-1)) "" in
          let itag = int_of_string tag in
          if (Array.length !arr) < itag then begin 
            arr := Array.append !arr (Array.make (Array.length !arr) 0);
          end;
          (Array.set !arr (itag-1) (!pc )) ;
          incr_pc (List.nth listr 1);)
        else
          incr_pc instr;
        (notebranche l');
  in

  let rec assoc (larg : string list) ?(inv = false) (acc :int list): int list =
    match larg with 
      []-> acc
    |arg::larg -> incr pc;
        let arg = remove_virg arg in
          
        if arg.[0] = 'L' then 
          let stag = String.sub arg 1 ((String.length arg)-1) in
          let itag = int_of_string stag in
          if inv then (assoc larg  ~inv:true ([(!arr.(itag-1)-(!pc))] @ acc))
          else (assoc larg (acc @ [(!arr.(itag-1)-(!pc))]))
        else if inv then (assoc larg ~inv:true ([(int_of_string arg)] @ acc ) )
        else assoc larg (acc@[(int_of_string arg)])
  in

  

  let rebranche (lisinst : string list)=
    pc :=0 ;
    let rec loop (linst : string list) (nlist : int list) =
      incr pc;
      match linst with 
        []-> nlist
      |ins_arg::l' -> 
          let l_inst_arg = (String.split_on_char ' ' ins_arg)in
          match l_inst_arg with
          |instr::[]-> loop l'  (nlist @ [opcode_from_string instr])
          |instr::larg -> (
              match instr with 
                "CLOSURE"|"closure" -> loop l' (nlist @ ((opcode_from_string instr)::(assoc larg ~inv:true [] )))
              |_->  loop l'  (nlist@((opcode_from_string instr)::(assoc larg [])))

            )
          |_->failwith "ya err1"
    in
    loop lisinst []
  in
  notebranche lisnt;
  array_from_list(rebranche !l_notag) 
;;
(** concatene interp et dinstr_trad *)
let interp_dinstr (code : string) : unit = 
  interp(dinstr_trad code)
;;
  (** retourne la liste d'entier des arguments d'un switch *)
let rec switch (param : string list)(inst : int list)=
  match param with 
    []-> inst 
  |x::lpar'-> let ninst = inst@[(int_of_string x)] in  (switch lpar' ninst)


  (** retourn la liste d'entier associer la chaine  *)
let list_from_string (code : string) : int list =
  let listInst = (List.map (String.trim) (String.split_on_char '\n' code)) in
  let lii : int list ref = ref [] in 
  let rec makeListInt (listInst : string list) = 
    match (listInst) with 
      [] -> () 
    |s::l' ->( 
        let instrlist = (String.split_on_char ' ' s) in 
        match instrlist with 
        
          inst::[]->  (let instInt = ref [0] in
                       if inst = "" then instInt := []
                       else instInt := [opcode_from_string inst] ;
                       lii := (!lii)@(!instInt) ; makeListInt l')
    
        |inst::param1::[]->( let instInt = opcode_from_string inst in
                             lii := (!lii)@(instInt::(int_of_string param1)::[]) ;
                             makeListInt l'
                   
                           )

        |inst::param1::param2::[] ->(let instInt = opcode_from_string inst in
                                     lii := (!lii)@(instInt::(int_of_string param1)::(int_of_string param2)::[]);
                                     makeListInt l' 
                                    )
                                        
        |inst::param1::param2::param3::param4::[] ->( (lii := ((!lii)@(15::(int_of_string param1)::(int_of_string param2)::(int_of_string param3)::(int_of_string param4)::[]))); makeListInt l';)
        |inst::lparam -> lii := (!lii)@(switch lparam [36])                                                  
        |_-> (failwith "erreur format" )
                    
      )      
  in
  (makeListInt listInst);
  !lii 
  

(** retourne le tableau d'entier correspondant a la suite d'instruction decrit dans instr *)
let array_from_string (s:string) = 
  let listi = list_from_string s in 
  array_from_list listi 
;;

(** concatene interp et array_from_string *)
let interp_code (code : string)=
  interp (array_from_string code)

