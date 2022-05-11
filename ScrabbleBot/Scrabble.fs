namespace YourClientName

open System
open Eval
open Microsoft.FSharp.Collections
open ScrabbleUtil
open ScrabbleUtil.Dictionary
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint
open StateMonad

// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?" 
        Regex.Matches(ts, pattern) |>
        Seq.cast<Match> |> 
        Seq.map 
            (fun t -> 
                match t.Value with
                | Regex pattern [x; y; id; c; p] ->
                    ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
                | _ -> failwith "Failed (should never happen)") |>
        Seq.toList

 module Print =

    let printHand pieces hand =
        hand |>
        MultiSet.fold (fun _ x i -> forcePrint $"%d{x} -> (%A{Map.find x pieces}, %d{i})\n") ()

module State = 
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.
    type move = (int*int)*(coord * char)list
    type state = {
        actualBoard   : Map<coord,char>
        tempBoard     : Map<coord,char>
        board         : Parser.board
        dict          : Dict
        playerNumber  : uint32
        numPlayers    : uint32
        playerTurn    : uint32
        hand          : MultiSet.MultiSet<uint32>
    }

    let mkState ab tb b d pn np pt h = {actualBoard = ab;tempBoard = tb; board = b; dict = d;  playerNumber = pn; numPlayers = np; playerTurn = pt; hand = h }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand

module Scrabble =
    let updateActualBoard (st:State.state) ms = List.fold (fun m x -> Map.add (fst x) (snd x |> snd |> fst) m) st.tempBoard ms    
    let updatePlayerTurn : State.state -> uint =
       function
       | s when (s.playerTurn + 1u) > s.numPlayers -> 1u
       | s -> s.playerTurn + 1u
    let findChar i = Convert.ToChar(i + 64u)
    let charToValue (c:char) = Convert.ToUInt32(c) - 64u
    let moveIsInsideBoard sizeOfBoard (partialWord:(coord * char) list ) =
        let minus = - ((sizeOfBoard - 1) / 2)
        let plus = ((sizeOfBoard - 1) / 2)
        let rec aux move =
            match move with
            | [] -> true
            | h :: t ->
                let x = fst (fst h)
                let y = snd (fst h)
                if x < minus || x > plus || y < minus || y > plus then false
                else aux t
        aux partialWord
    let legalMove (partialWord:(coord * char)list) anchor count sizeOfBoard =
        let hasPlacedTile =
            if count > 0 then
                let aux = List.map fst partialWord
                match List.tryFind (fun x -> x = anchor) aux with
                | Some _ -> true
                | _ -> false
            else false
        moveIsInsideBoard sizeOfBoard partialWord && hasPlacedTile
    let crossCheck square letter (state: State.state) i j =
        let actualBoard' = Map.add square letter state.tempBoard
        let rec findStart pos =
            let pos' = (fst pos - i, snd pos - j)
            match Map.tryFind pos' actualBoard' with
            | Some _ -> findStart pos' 
            | None -> pos
        let startPos = findStart square
        let rec isValid pos dict b count =
            match Map.tryFind pos actualBoard' with
            | Some c ->      
                match step c dict with
                | Some (b,d') -> isValid (fst pos + i, snd pos + j) d' b (count + 1)
                | None -> false
            | None when count = 1 -> true
            | _ -> b
        isValid startPos state.dict false 0           
    let allValidChars node =
        let letters = seq [1u..26u] |> Seq.map findChar |> Seq.toList
        let rec aux validLetters = function
            | [] -> validLetters
            | x :: xs ->
                match step x node with
                | Some _ -> aux (x :: validLetters) xs
                | None _ -> aux validLetters xs
        aux [] letters
    let mutable bestMove = ((0,0),[])
    let getBasePointsOfMove (move : (coord * char)list) (pieces: Map<uint32, tile>) =
        let rec aux move' acc =
            match move' with
            | [] -> acc
            | x :: xs ->
                let pid = snd x |> charToValue
                let pv = Map.find pid pieces |> Set.maxElement |> snd
                aux xs (acc + pv)
        aux move 0 
    let getNewCoordsFromMove (move: State.move) (state:State.state) = List.map (fun (pos,_) -> match Map.tryFind pos state.actualBoard with | Some _ | None -> pos) (snd move)
    let rec findStart anchor board i j =
        match Map.tryFind anchor board with
        | Some _ -> findStart (fst anchor - i, snd anchor - j) board i j
        | None -> anchor
    let rec readWord anchor board i j word =
        match Map.tryFind anchor board with
        | Some c -> readWord (fst anchor + 1, snd anchor + j) board i j (((fst anchor + 1, snd anchor + j),c) :: word)
        | None -> word
    let findLinkedWords board i j (coords: coord list) = List.fold (fun acc x -> (readWord (findStart x board i j) board i j []) :: acc) [] coords
    let evalSquare w pos acc (m : square) =
        let acc' = Map.find 0 m w pos acc |> fun (Success x) -> x
        m |>
        Map.tryFind 1 |>
        Option.map (fun f -> f w pos acc' |> fun (Success x) -> x) |>
        Option.defaultValue acc'
    let rec evalWord : ((int*int)*char) list -> (char*int) list-> int -> State.state -> int -> int =
        function
        | [] -> fun _ -> fun _ -> fun _ -> id
        | x :: xs -> fun word -> fun index -> fun st -> fun acc ->
            match Map.tryFind (fst x) st.actualBoard with
            | Some _ ->
                evalWord xs word (index + 1) st (evalSquare word index acc st.board.defaultSquare) 
            | None ->
                let v = st.board.squares (fst x) |> (fun (Success sq) -> sq |> Option.map (evalSquare word index acc))
                evalWord xs word (index + 1) st v.Value
    let rec evalWords acc (pieces: Map<uint32, tile>) state =
        function
        | [] -> acc 
        | x :: xs ->
            let word = List.map(fun x -> (snd x,pieces[charToValue(snd x)] |> Set.maxElement|>snd)) x
            evalWords (acc + evalWord x word 0 state acc) pieces state xs 
    let evalMove (move: State.move) (pieces: Map<uint32, tile>) (state:State.state) =
        let cross =
            getNewCoordsFromMove move state|>
            findLinkedWords state.tempBoard (fst (fst move)) (snd (fst move)) |>
            evalWords 0 pieces state
        let word = List.map(fun x -> (snd x,pieces[charToValue(snd x)] |> Set.maxElement |> snd)) (snd move)
        let p = evalWord (snd move) word 0 state cross
        if (getNewCoordsFromMove move state).Length = 7 then p + 50 else p 
        //getCrossCheckPointsForWord state pieces (getPointsForWord move pieces state true 0) move
    let updateBestMove move pieces state =
        let currentMovePoints = evalMove bestMove pieces state 
        let newMovePoints = evalMove move pieces state
        if newMovePoints > currentMovePoints then bestMove <- move     
    let rec extend (partialWord:(coord * char)list) (node : Dict) square (state : State.state) squareIsTerminal anchor i j count pieces sizeOfBoard =
        match Map.tryFind square state.tempBoard with
        | Some _ ->
            let l = state.tempBoard[square]
            match step l node with
            | Some (b,node') -> extend ((square, l) :: partialWord) node' (fst square + i, snd square + j) state b anchor i j count pieces sizeOfBoard
            | None _ -> ()
        | None ->
            if squareIsTerminal && legalMove partialWord anchor count sizeOfBoard then updateBestMove ((j,i),partialWord) pieces state
            let rec aux = function
                | [] -> ()
                | letter :: tail -> 
                    if MultiSet.contains (charToValue letter) state.hand && crossCheck square letter state i j && crossCheck square letter state j i then
                        match step letter node with
                        | Some (b, node') -> 
                            let partialWord' = (square, letter) :: partialWord
                            let square' = (fst square + i, snd square + j)
                            extend partialWord' node' square' {state with hand = MultiSet.removeSingle (charToValue letter) state.hand; tempBoard = Map.add square letter state.tempBoard } b anchor i j (count + 1) pieces sizeOfBoard
                        | None _ -> ()
                    aux tail
            aux (allValidChars node)
    let rec findAllWords (partialWord:(coord * char)list) dict square limit (state : State.state) isTerminal pieces sizeOfBoard =
        [0..limit] |> List.iter(fun i -> extend partialWord dict (fst square - i, snd square) state isTerminal square 1 0 0 pieces sizeOfBoard)
        [0..limit] |> List.iter(fun i -> extend partialWord dict (fst square, snd square - i) state isTerminal square 0 1 0 pieces sizeOfBoard)
    let search (st: State.state) pieces sizeOfBoard = st.tempBoard |> Map.toSeq |> List.ofSeq |> List.map fst |> List.iter (fun x -> findAllWords [] st.dict x (MultiSet.size st.hand |> int) st false pieces sizeOfBoard)
    let startSearch (st: State.state) pieces sizeOfBoard =
        bestMove <- (0,0),[]
        search st pieces sizeOfBoard
    let blankMove (st: State.state) pieces sizeOfBoard =
        let chars = seq [1u..26u] |> Seq.toList
        let rec aux hand' =
            match hand' with
            | [] -> ()
            | x :: xs ->
                let hand'' = MultiSet.addSingle x MultiSet.empty 
                let st' = {st with hand = hand''}
                search st' pieces sizeOfBoard
                aux xs
        aux chars 
    let firstMoveSearch (st: State.state) pieces sizeOfBoard =
        let hand = MultiSet.toList st.hand
        let rec aux hand' =
            match hand' with
            | [] -> ()
            | x :: xs ->
                let hand'' = List.fold (fun x y -> MultiSet.removeSingle y x) st.hand [x]
                let actualBoard = [((0,0), findChar x)] |> Map.ofList
                let st' = {st with hand = hand''; tempBoard = actualBoard}
                search st' pieces sizeOfBoard
                aux xs
        aux hand        
    let getPlay (st : State.state) pieces =
        evalMove bestMove pieces st |> printfn "%d"
        let rec aux move acc =
            match move with
            | [] -> acc
            | head :: tails ->
                match Map.tryFind (fst head) st.tempBoard with
                | Some _ -> aux tails acc
                | None ->
                    let pid = snd head |> charToValue
                    let char = snd head |> Char.ToString
                    let pv = Map.find pid pieces |> Set.maxElement |> snd
                    let x = fst (fst head)
                    let y = snd (fst head)
                    aux tails (acc + $"%i{x} %i{y} %i{pid}%s{char}%i{pv} ")
        (aux (snd bestMove) "").Trim()
    let getBlankPlay (st : State.state) =
        let rec aux move acc =
            match move with
            | [] -> acc
            | head :: tails ->
                match Map.tryFind (fst head) st.tempBoard with
                | Some _ -> aux tails acc
                | None ->
                    let pid = 0
                    let char = snd head |> Char.ToString
                    let pv = 0
                    let x = fst (fst head)
                    let y = snd (fst head)
                    aux tails (acc + $"%i{x} %i{y} %i{pid}%s{char}%i{pv} ")
        (aux (snd bestMove) "").Trim()      
    let getBoardSize boardP =
        match boardP.isInfinite with
        |true -> Int32.MaxValue
        |false -> 15
    let playGame cstream (pieces: Map<uint32, tile>) (st : State.state) (boardP:boardProg) =
        let rec aux (st : State.state) =
            
            let doMove = function
                | str when str = "" -> send cstream SMPass
                | str -> send cstream (SMPlay (RegEx.parseMove str))
                
            if st.playerTurn = st.playerNumber then
                if st.tempBoard.IsEmpty then
                    firstMoveSearch st pieces (getBoardSize boardP)                   
                elif MultiSet.size st.hand = 1u && MultiSet.contains 0u st.hand then
                    blankMove st pieces (getBoardSize boardP)
                else
                    startSearch st pieces (getBoardSize boardP)
                doMove (getPlay st pieces)
                    
            let msg = recv cstream
            
            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                let placedLetterIDs = List.fold (fun x y -> fst(snd(y)) :: x) [] ms
                let hand = List.fold (fun x y -> MultiSet.removeSingle y x) st.hand placedLetterIDs
                let hand' = List.fold (fun x y -> MultiSet.add(fst(y)) (snd(y)) x) hand newPieces                             
                let st' = {st with hand = hand'; tempBoard = updateActualBoard st ms; actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}  
                aux st'
            | RCM (CMPlayed (pid, ms, points)) ->
                let st' = {st with tempBoard = updateActualBoard st ms; actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}
                aux st'
            | RCM (CMPlayFailed (pid, ms)) ->
                let st' = {st with tempBoard = updateActualBoard st ms; actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}
                aux st'
            | RCM (CMPassed i) -> 
                let st' = {st with playerTurn = updatePlayerTurn st}
                aux st'
            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith $"not implmented: %A{a}"
            | RGPE err -> printfn $"Gameplay Error:\n%A{err}"; aux st
        aux st
    let startGame 
            (boardP : boardProg) 
            (dictf : bool -> Dict) 
            (numPlayers : uint32) 
            (playerNumber : uint32) 
            (playerTurn  : uint32) 
            (hand : (uint32 * uint32) list)
            (tiles : Map<uint32, tile>)
            (timeout : uint32 option) 
            (cstream : Stream) =
        debugPrint 
            $"Starting game!
                      number of players = %d{numPlayers}
                      player id = %d{playerNumber}
                      player turn = %d{playerTurn}
                      hand =  %A{hand}
                      timeout = %A{timeout}\n\n"

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        let dict = dictf false // Uncomment if using a trie for your dictionary
        let board = Parser.mkBoard boardP
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState Map.empty Map.empty board dict playerNumber numPlayers playerTurn handSet) boardP         