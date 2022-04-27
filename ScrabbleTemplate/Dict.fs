module Dictionary

    type Dict =
        | Node of bool * Map<char,Dict> 
        | Leaf of bool
    let empty () = Node (false, Map.empty)
    let valueFromMap a (m:Map<char,Dict>) = Map.tryFind a m |> fun a -> match a with | Some(a) -> a | None -> Leaf false    
    let insert (s:string) (d:Dict) : Dict =
        let rec put (x:Dict) (s:string) (d:int) =
            match (x,d) with
            | Leaf _, d when d = s.Length -> Leaf true
            | Node (_, x), d when d = s.Length -> Node(true,x)
            | Leaf l, d -> Node(l, Map.empty.Add(s.[d],put (empty ()) s (d+1)))
            | Node (a, x), d -> Node(a, x.Add(s.[d], put (valueFromMap s.[d] x) s (d+1)))
        put d s 0
    
    let lookup (s:string) (d:Dict) : bool =
         let rec search (x:Dict) (s:string) (d:int) =
            match (x,d) with
            | Leaf x, d when d = s.Length -> x
            | Node (x, _), d when d = s.Length -> x
            | Leaf _, _ -> false
            | Node (_, x), d -> search (valueFromMap s.[d] x) s (d+1)
         search d s 0
    
    let rec step (c:char) (d:Dict) =
        match d with
        | Node (_,y) ->
            let d' = valueFromMap c y
            match d' with
                | Node (x,_) when x = true -> Some(true, d')
                | Node _ -> Some(false, d')
                | Leaf x when x = true -> Some(true, d')
                | _ -> None 
        | Leaf _ -> None
        
    
    let d = empty()
    let d' = insert "tulip" d
    
    let a = step 't' d'
    let a' = snd a.Value
    let b = step 'u' a'
    let b' = snd b.Value
    let c = step 'l' b'
    let c' = snd c.Value
    let e = step 'i' c'
    let e' = snd e.Value