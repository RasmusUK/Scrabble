module internal MultiSet

    open System

    type MultiSet<'a when 'a : comparison> = Ms of Map<'a, uint32>
    let empty = Ms Map.empty
    let isEmpty (Ms map) =  map.IsEmpty
    let size : MultiSet<'a> -> uint32 =
        function
        | Ms map when map.IsEmpty -> 0u
        | Ms map -> map |> Map.fold (fun acc _ value -> acc + value)  0u
    let contains a (Ms map)= 
        match map.TryFind(a) with
        | Some _ -> true
        | _ -> false
    let numItems a (Ms map) =
        if contains a (Ms(map))
        then map.Item(a)
        else 0u
    let add a n (Ms map) = Ms(map.Add(a, numItems a (Ms(map)) + n))
    let addSingle a multiset = add a 1u multiset
    let remove a (n : uint32) (Ms map) =
        if n < numItems a (Ms map)
        then Ms(map.Add(a,(uint32 ((int (numItems a (Ms map))) - (int n)))))
        else Ms(map.Remove(a))
    let removeSingle a map = remove a 1u map
    let rec fold f acc (Ms map)= Map.fold f acc map
    let rec foldBack f xs acc =
        match xs with
        | Ms map -> Map.foldBack f map acc
    let rec ofList =
        function
        | [] -> empty
        | x :: xs -> addSingle x (ofList xs)
    let rec listOfItems a =
        function
        | 0u -> []
        | n -> a :: listOfItems a (n-1u)
    let toList map = map |> fold (fun acc item value -> acc @ (listOfItems(item)value)) []
    let map f origin = origin |> toList |> List.map f |> ofList
    let union s1 s2 = fold (fun (acc : MultiSet<'a>) i v -> if numItems i acc < v then add i (v - numItems i acc) acc else acc) s1 s2 |> fold (fun (acc : MultiSet<'a>) i v -> if numItems i acc < v then add i (v - numItems i acc) acc else acc) s2
    let sum s1 s2 = ((s1 |> toList) @ (s2 |> toList)) |> ofList
    let subtract s1 s2 = fold (fun (acc : MultiSet<'a>) i v -> remove i v acc) s1 s2
    let smallest a b c d = add a (Math.Min(numItems a b,numItems a c)) d
    let intersection s1 s2 = fold (fun acc i v -> if contains i s1 && contains i s2 then smallest i s1 s2 acc else acc) empty (union s1 s2)