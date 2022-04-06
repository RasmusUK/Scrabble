module internal Eval

    open StateMonad

    let add a b = a >>= fun x -> b >>= fun y -> ret (x+y)
    let sub a b = a >>= fun x -> b >>= fun y -> ret (x-y)
    let mul a b = a >>= fun x -> b >>= fun y -> ret (x*y)
    let div a b = a >>= fun x -> b >>= fun y ->
        if y <> 0 then ret (x/y) else fail DivisionByZero
    let mod1 a b = a >>= fun x -> b >>= fun y ->
        if y <> 0 then ret (x%y) else fail DivisionByZero      

    type aExp =
        | N of int
        | V of string
        | WL
        | PV of aExp
        | Add of aExp * aExp
        | Sub of aExp * aExp
        | Mul of aExp * aExp
        | Div of aExp * aExp
        | Mod of aExp * aExp
        | CharToInt of cExp

    and cExp =
       | C  of char  (* Character value *)
       | CV of aExp  (* Character lookup at word index *)
       | ToUpper of cExp
       | ToLower of cExp
       | IntToChar of aExp

    type bExp =             
       | TT                   (* true *)
       | FF                   (* false *)

       | AEq of aExp * aExp   (* numeric equality *)
       | ALt of aExp * aExp   (* numeric less than *)

       | Not of bExp          (* boolean not *)
       | Conj of bExp * bExp  (* boolean conjunction *)

       | IsVowel of cExp      (* check for vowel *)
       | IsLetter of cExp     (* check for letter *)
       | IsDigit of cExp      (* check for digit *)

    let (.+.) a b = Add (a, b)
    let (.-.) a b = Sub (a, b)
    let (.*.) a b = Mul (a, b)
    let (./.) a b = Div (a, b)
    let (.%.) a b = Mod (a, b)

    let (~~) b = Not b
    let (.&&.) b1 b2 = Conj (b1, b2)
    let (.||.) b1 b2 = ~~(~~b1 .&&. ~~b2)       (* boolean disjunction *)
    let (.->.) b1 b2 = (~~b1) .||. b2           (* boolean implication *) 
       
    let (.=.) a b = AEq (a, b)   
    let (.<.) a b = ALt (a, b)   
    let (.<>.) a b = ~~(a .=. b)
    let (.<=.) a b = a .<. b .||. ~~(a .<>. b)
    let (.>=.) a b = ~~(a .<. b)                (* numeric greater than or equal to *)
    let (.>.) a b = ~~(a .=. b) .&&. (a .>=. b) (* numeric greater than *)    

    let vowel c =
        let ch = System.Char.ToLower c
        match ch with
        | 'a' | 'e' | 'i' | 'o' | 'u' | 'y' -> true
        | _ -> false
    let rec arithEval a : SM<int> =
        match a with
        | N n -> ret n
        | V v -> lookup v
        | WL -> wordLength
        | PV a -> arithEval a >>= fun x -> pointValue x
        | Add (a,b) -> add (arithEval a) (arithEval b) 
        | Sub (a,b) -> sub (arithEval a) (arithEval b) 
        | Mul (a,b) -> mul (arithEval a) (arithEval b) 
        | Div (a,b) -> div (arithEval a) (arithEval b)
        | Mod (a,b) -> mod1 (arithEval a) (arithEval b)
        | CharToInt x -> charEval x >>= fun x -> ret (int x)
    and charEval c : SM<char> =
        match c with
        | C c -> ret c
        | CV a -> arithEval a >>= fun x -> characterValue x
        | ToUpper x -> charEval x >>= fun x -> ret (System.Char.ToUpper x)
        | ToLower x -> charEval x >>= fun x -> ret (System.Char.ToLower x)
        | IntToChar x -> arithEval x >>= fun x -> ret (char x)
    and boolEval b : SM<bool> =
        match b with
        | TT -> ret(true)                  
        | FF -> ret(false)                     
        | AEq (a,b) -> arithEval a >>= fun x -> arithEval b >>= fun y -> ret(x=y) 
        | ALt (a,b) -> arithEval a >>= fun x -> arithEval b >>= fun y -> ret(x<y) 
        | Not x -> boolEval x >>= fun x -> ret(not x)       
        | Conj (a,b) -> boolEval a >>= fun x -> boolEval b >>= fun y -> ret(x&&y) 
        | IsVowel x -> charEval x >>= fun x -> ret (vowel x)
        | IsLetter x -> charEval x >>= fun x -> ret (System.Char.IsLetter x)
        | IsDigit x -> charEval x >>= fun x -> ret (System.Char.IsDigit x)


    type stm =                (* statements *)
    | Declare of string       (* variable declaration *)
    | Ass of string * aExp    (* variable assignment *)
    | Skip                    (* nop *)
    | Seq of stm * stm        (* sequential composition *)
    | ITE of bExp * stm * stm (* if-then-else statement *)
    | While of bExp * stm     (* while statement *)

    let rec stmntEval stmnt : SM<unit> =
        match stmnt with
        | Declare x -> declare x
        | Ass (a,b) -> arithEval b >>= fun x -> update a x
        | Skip -> ret () 
        | Seq (a,b) -> stmntEval a >>>= stmntEval b >>= fun x -> ret x
        | ITE (a,b,c) -> boolEval a >>= fun x ->            
            if x
            then push >>>= stmntEval b >>>= pop
            else push >>>= stmntEval c >>>= pop                
        | While (a,b) -> boolEval a >>= fun x ->
            push >>>=
            if x
            then stmntEval b >>>= stmntEval (While(a,b)) >>>= pop
            else pop  

(* Part 3 (Optional) *)

    type StateBuilder() =

        member this.Bind(f, x)    = f >>= x
        member this.Return(x)     = ret x
        member this.ReturnFrom(x) = x
        member this.Delay(f)      = f ()
        member this.Combine(a, b) = a >>= (fun _ -> b)
        
    let prog = new StateBuilder()

    let rec arithEval2 a : SM<int> = prog{
        match a with
        | N n -> return n
        | V v -> return! lookup v
        | WL -> return! wordLength
        | PV a ->
            let! x = arithEval2 a
            return! pointValue x
        | Add (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            return x+y
        | Sub (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            return x-y
        | Mul (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            return x*y
        | Div (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            if y<> 0 then return (x/y)
            else return! fail DivisionByZero
        | Mod (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            if y<> 0 then return (x%y)
            else return! fail DivisionByZero
        | CharToInt a ->
            let! x = charEval2 a
            return int x}
    and charEval2 c : SM<char> = prog{
        match c with
        | C c -> return c
        | CV a ->
            let! x = arithEval2 a
            return! characterValue x
        | ToUpper x ->
            let! a = charEval2 x
            return System.Char.ToUpper a             
        | ToLower x ->
            let! a = charEval2 x
            return System.Char.ToLower a  
        | IntToChar x ->
            let! a = arithEval2 x
            return char a}
    and boolEval2 b : SM<bool> = prog{
        match b with
        | TT -> return true                  
        | FF -> return false                   
        | AEq (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            return x=y
        | ALt (a,b) ->
            let! x = arithEval2 a
            let! y = arithEval2 b
            return x<y
        | Not x ->
            let! a = boolEval2 x
            return not a    
        | Conj (a,b) ->
            let! x = boolEval2 a
            let! y = boolEval2 b
            return x&&y
        | IsVowel x ->
            let! a = charEval x
            return vowel a
        | IsLetter x ->
            let! a = charEval x
            return System.Char.IsLetter a
        | IsDigit x ->
            let! a = charEval x
            return System.Char.IsDigit a}

    let rec stmntEval2 stmnt : SM<unit> = prog{
        match stmnt with
        | Declare x -> do! declare x
        | Ass (a,b) ->
            let! x = arithEval2 b
            do! update a x
        | Skip -> do! stmntEval2 Skip
        | Seq (a,b) ->
            do! stmntEval2 a
            let! x = stmntEval2 b
            return x
        | ITE (a,b,c) ->
            let! x = boolEval2 a
            do! push
            if x then
                let! y = stmntEval2 b
                do! pop
                return y
            else
                let! y = stmntEval2 c
                do! pop
                return y          
        | While (a,b) ->
            let! x = boolEval2 a
            do! push
            if x then
                do! stmntEval2 b
                let! a = stmntEval2 (While(a,b))
                do! pop
                return a
            else do! pop
            }

(* Part 4 *) 

    type word = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>

    let stmntToSquareFun (stm:stm) : squareFun = fun w pos acc ->
        let s = mkState [("_pos_", pos); ("_acc_",acc); ("_result_",0)] w ["_pos_";"_acc_";"_result_"]
        stmntEval stm >>>= lookup "_result_" |> evalSM s

    type coord = int * int

    type boardFun = coord -> Result<squareFun option, Error> 
    let stmntToBoardFun (stm:stm) (m:Map<int, squareFun>) : boardFun = fun ((x,y):coord) ->
        let s = mkState [("_x_", x); ("_y_",y); ("_result_",0)] [] ["_x_";"_y_";"_result_"]
        let v = stmntEval stm >>>= lookup "_result_" >>= fun x ->
            match m.TryFind x with
            |Some x -> ret (Some x)
            |None -> ret None
        v |> evalSM s
        
    type square = Map<int, squareFun>

    let stmntToBoardFun2 (stm:stm) (m:Map<int, square>) = fun ((x,y):coord) ->
        let s = mkState [("_x_", x); ("_y_",y); ("_result_",0)] [] ["_x_";"_y_";"_result_"]
        let v = stmntEval stm >>>= lookup "_result_" >>= fun x ->
            match m.TryFind x with
            |Some x -> ret (Some x)
            |None -> ret None
        v |> evalSM s
        
    type board = {
        center        : coord
        defaultSquare : squareFun
        squares       : boardFun
    }

    let mkBoard (c:coord) (defaultSq:stm) (boardStmnt:stm) (ids:(int*stm) list) : board =
        let defaultSquareFun = stmntToSquareFun defaultSq
        let m = List.map (fun (x,y) ->  (x,(stmntToSquareFun y))) ids |> Map.ofList 
        let squaresBoardFun = stmntToBoardFun boardStmnt m
        {center = c; defaultSquare = defaultSquareFun; squares = squaresBoardFun }