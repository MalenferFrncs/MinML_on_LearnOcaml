
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