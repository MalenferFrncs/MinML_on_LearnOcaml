
  

let q1 () =
  Assume.compatible "identity" [%ty : 'a -> 'a]; 
  Check.name1 "identity" [%ty : unit -> unit]  
     [();()]


let q2 () = 
   let module Code = struct 
        let ex1 = Get.value "ex1" [%ty: string]
      end in
    Check.expr1 [%code Interpreteur.interp (Parser.array_from_string ex1 [] []) ] 
    [%ty: unit->Interpreteur.rapport ]
    ~equal: Interpreteur.equal_rapport
    [()]
    

let () =
  Result.set (Result.questions [q1;q2])