let opcode_from_string (s:string) : int= 
  match s with 
    "PUSH"->1
  |"APPLY1"->8
  |"RESTART"->12
  |"VECTLENGTH"->28
  |"GETVECTLENGTH"->29
  |"SETVECTITEM"->30
  |"GETSTRINGCHAR"->31
  |"SETSTRINGSHAR"-> 32
  |"BOOLNOT"->37
  |"POPTRAP"->39
  |"RAISE"->40
  |"CHECK-SIGNALS"->41
  |"NEGINT"->44
  |"ADDINT"->45
  |"SUBINT"->46
  |"MULINT"->47
  |"DINVINT"->48
  |"MODINT"->49
  |"ANDINT"->50
  |"ORINT"->51
  |"XORINT"->52
  |"LSLINT"->53
  |"LSRINT"->54
  |"ASRINT"->55
  |"EQ"->56
  |"NEQ"->57
  |"LINT"->58
  |"LEINT"->59
  |"GTINT"->60
  |"GEINT"->61
  |"ISINT"->64
  |"GETMETHOD"->65
  |"ULTINT"->72
  |"UGEINT"->73
  |"STOP"->76
  (*|""->*)
  | "ACC" -> 0 
  |"PUSHACC" -> 2
  |"POP" -> 3
  |"ASSIGN" -> 4
  |"ENVACC" -> 5
  |"PUSHENVACC" -> 6
  |"PUSH-RETADDR" -> 7
                       (* |"APPLY" -> 8*)
  |"APPLYN" -> 9
  |"RETURN" ->  11
  |"GRAB" -> 13
  |"OFFSETCLOSURE" -> 16
  |"PUSHOFFSETCLOSURE" -> 17
  |"GETGLOBAL"-> 18
  |"PUSHGETGLOBAL"-> 19
  |"SETGLOBAL"-> 22
  |"ATOM"->23
  |"PUSHATOM"->24
  |"GETFIELD"->26
  |"SETFIELD"->27
  |"BRANCH"->33
  |"BRANCHIF"->34
  |"BRANCHIFNOT"->35
  |"PUSHTRAP"->38
  |"CONSTINT" -> 42 
  |"PUSHCONSTINT"->43
  |"OFFSETINT"->62
  |"OFFSETREF"->63
  |"APPTERM" -> 10
  |"CLOSURE" -> 14
  |"GETGLOBALFIELD"-> 20
  |"PUSHGETGLOBALFIELD"-> 21
  |"MAKEBLOCK"->25
  |"BEQ"->66
  |"BNEQ"->67
  |"BLTINT"->68
  |"BLEINT"->69
  |"BGTINT"->70
  |"BGEINT"->71
  |"BULTINT"->74
  |"BUGEINT"->75
  |"SWITCH"-> 36
  |"CLOSUREREC" -> 15
  |_ -> failwith "l'instruction n'existe pas"

let rec switch (param : string list)(inst : int list)=
  match param with 
    []-> inst 
  |x::lpar'-> let ninst = inst@[(int_of_string x)] in  (switch lpar' ninst)

let rec remove (li : (int list)) (x:int) : int list =
  match li with 
    [] -> [] 
  |i::lis -> if x=i then  lis
      else (i::(remove lis x)) 
;; (* renvoit la liste privé de la 1er instance de x si x est dans la liste *)

let check_not_in (li : (int list)) (x:int) : unit =
  let equal x a = if x=a then true else false in
  if (List.exists (equal x) li) then failwith "instruction invalide dans cette exercice" else ()
;; (*renvoit une erreur si x est dans li, unit sinon*)

let check_instr (instr_banis : int list) (instr_oblig_ref : int list ref ) (instr :int) : unit = 
  let new_instr_oblig_ref = ref (remove !instr_oblig_ref instr) in
  if (!new_instr_oblig_ref = !instr_oblig_ref )  (*si on utilise pas d'instruction obligatoire *)
  then (check_not_in instr_banis instr)          (*on verifie qu'on utilise pas une instruction illegal *)
  else instr_oblig_ref := !new_instr_oblig_ref;  (*sinon on reasigne la liste privé de la 1er instance de instr *)
  ()                                             (*a instr_oblig_ref et on renvoit vrais *)  
;;

let list_from_string (code : string) (instr_banis : int list) (instr_oblig : int list): int list =
  let listInst = (List.map (String.trim) (String.split_on_char '\n' code)) in
  let lii = ref [] in
  let instr_oblig_ref = ref instr_oblig  in
  let check_instInt = check_instr instr_banis instr_oblig_ref in
  let rec makeListInt (listInst : string list) = 
    match (listInst) with 
      [] -> if !instr_oblig_ref = [] then () 
              else failwith "vous n'avez pas utiliser toutes les instructions indiqués" 
    |s::l' ->( 
        let instrlist = (String.split_on_char ' ' s) in 
        match instrlist with 
          inst::[]->( let instInt = opcode_from_string inst in
                      check_instInt instInt ;
                      lii := (!lii)@[instInt] ; makeListInt l'
                    )
        |inst::param1::[]->( let instInt = opcode_from_string inst in
                            check_instInt instInt ;
                             lii := (!lii)@(instInt::(int_of_string param1)::[]) ;
                             makeListInt l'
                   
                           )

        |inst::param1::param2::[] ->(let instInt = opcode_from_string inst in
                            check_instInt instInt ;
                             lii := (!lii)@(instInt::(int_of_string param1)::(int_of_string param2)::[]);
                             makeListInt l' 
                            )
                                        
        |inst::param1::param2::param3::param4::[] ->( 
                            check_instInt 15 ;
                            (lii := ((!lii)@(15::(int_of_string param1)::(int_of_string param2)::(int_of_string param3)::(int_of_string param4)::[]))); makeListInt l';)
        |inst::lparam -> 
                      check_instInt 36 ;
                      lii := (!lii)@(switch lparam [36])                                                  
        |_-> (failwith "erreur format" )
                    
)      
in
(makeListInt listInst);
!lii

(* construit la liste d'entier a partir de la chaine de caractère, produit une erreur si on 
 n'utilise pas toutes les instruction obligatoires *)


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

(* produit un tableau a partir d'une liste *)

let array_from_string (s:string) (instr_banis : int list) (instr_oblig : int list) = 
  let listi = list_from_string s instr_banis instr_oblig in 
  array_from_list listi 

(* concatene les deux fonctions precedentes *)

