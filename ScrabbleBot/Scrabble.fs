namespace YourClientName

open System
open System.ComponentModel
open Microsoft.FSharp.Collections
open ScrabbleUtil
open ScrabbleUtil.Dictionary
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint

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

    type state = {
        actualBoard   : Map<coord,char>
        board         : Parser.board
        dict          : ScrabbleUtil.Dictionary.Dict
        playerNumber  : uint32
        numPlayers    : uint32
        playerTurn    : uint32
        hand          : MultiSet.MultiSet<uint32>
    }

    let mkState ab b d pn np pt h = {actualBoard = ab; board = b; dict = d;  playerNumber = pn; numPlayers = np; playerTurn = pt; hand = h }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand

module Scrabble =
    open System.Threading
    let updateActualBoard (st:State.state) ms = List.fold (fun m x -> Map.add (fst x) (snd x |> snd |> fst) m) st.actualBoard ms
    
    let updatePlayerTurn (st:State.state) =
                let newId = st.playerTurn + 1u
                if newId > st.numPlayers then 1u else newId 
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
        let actualBoard' = Map.add square letter state.actualBoard
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
            | None -> if count = 1 then true else b
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
          
    let mutable bestMove = List.empty
    
    let getBasePointsOfMove (move : (coord * char)list) (pieces: Map<uint32, tile>) =
        let rec aux move' acc =
            match move' with
            | [] -> acc
            | x :: xs ->
                let pid = snd x |> charToValue
                let pv = Map.find pid pieces |> Set.maxElement |> snd
                aux xs (acc + pv)
        aux move 0   
    let updateBestMove move pieces =
        let currentMovePoints = getBasePointsOfMove bestMove pieces
        let newMovePoints = getBasePointsOfMove move pieces
        if newMovePoints > currentMovePoints then bestMove <- move
               
    let rec extend (partialWord:(coord * char)list) (node : Dict) square (state : State.state) squareIsTerminal anchor i j count pieces sizeOfBoard =
        let isVacant =
            match Map.tryFind square state.actualBoard with
            | Some _ -> false
            | None -> true
        if isVacant then
            if squareIsTerminal && legalMove partialWord anchor count sizeOfBoard then updateBestMove partialWord pieces
            let validLetters = allValidChars node
            let rec aux = function
                | [] -> ()
                | letter :: tail -> 
                    if MultiSet.contains (charToValue letter) state.hand && crossCheck square letter state i j && crossCheck square letter state j i then
                        let hand' = MultiSet.removeSingle (charToValue letter) state.hand
                        let actualBoard' = Map.add square letter state.actualBoard
                        let state' = {state with hand = hand'; actualBoard = actualBoard' }
                        match step letter node with
                        | Some (b, node') -> 
                            let partialWord' = (square, letter) :: partialWord
                            let square' = (fst square + i, snd square + j)
                            extend partialWord' node' square' state' b anchor i j (count + 1) pieces sizeOfBoard
                        | None _ -> ()
                    aux tail
            aux validLetters                  
        else
            let l = state.actualBoard[square]
            match step l node with
            | Some (b,node') ->
                let partialWord' = (square, l) :: partialWord
                let square' = (fst square + i, snd square + j)
                extend partialWord' node' square' state b anchor i j count pieces sizeOfBoard
            | None _ -> ()
 
    let rec findAllWords (partialWord:(coord * char)list) dict square limit (state : State.state) isTerminal pieces sizeOfBoard =
        [0..limit] |> List.iter(fun i -> extend partialWord dict (fst square - i, snd square) state isTerminal square 1 0 0 pieces sizeOfBoard)
        [0..limit] |> List.iter(fun i -> extend partialWord dict (fst square, snd square - i) state isTerminal square 0 1 0 pieces sizeOfBoard)
    
    let search (st: State.state) pieces sizeOfBoard = st.actualBoard |> Map.toSeq |> List.ofSeq |> List.map fst |> List.iter (fun x -> findAllWords [] st.dict x (MultiSet.size st.hand |> int) st false pieces sizeOfBoard)
    let startSearch (st: State.state) pieces sizeOfBoard =
        bestMove <- []
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
                let st' = {st with hand = hand''; actualBoard = actualBoard}
                search st' pieces sizeOfBoard
                aux xs
        aux hand        
    
    let getPlay (st : State.state) pieces =
        let rec aux move acc =
            match move with
            | [] -> acc
            | head :: tails ->
                match Map.tryFind (fst head) st.actualBoard with
                | Some _ -> aux tails acc
                | None ->
                    let pid = snd head |> charToValue
                    let char = snd head |> Char.ToString
                    let pv = Map.find pid pieces |> Set.maxElement |> snd
                    let x = fst (fst head)
                    let y = snd (fst head)
                    aux tails (acc + $"%i{x} %i{y} %i{pid}%s{char}%i{pv} ")
        (aux bestMove "").Trim()
    
    let getBlankPlay (st : State.state) =
        let rec aux move acc =
            match move with
            | [] -> acc
            | head :: tails ->
                match Map.tryFind (fst head) st.actualBoard with
                | Some _ -> aux tails acc
                | None ->
                    let pid = 0
                    let char = snd head |> Char.ToString
                    let pv = 0
                    let x = fst (fst head)
                    let y = snd (fst head)
                    aux tails (acc + $"%i{x} %i{y} %i{pid}%s{char}%i{pv} ")
        (aux bestMove "").Trim()      
    
    let getBoardSize boardP =
        match boardP.isInfinite with
        |true -> Int32.MaxValue
        |false -> 15
        
    let playGame cstream (pieces: Map<uint32, tile>) (st : State.state) (boardP:boardProg) =
        let rec aux (st : State.state) =
            let doMove str =
                if str = "" then send cstream SMPass
                else send cstream (SMPlay (RegEx.parseMove str))
            
            if st.playerTurn = st.playerNumber then
                if st.actualBoard.IsEmpty then
                    firstMoveSearch st pieces (getBoardSize boardP)
                    doMove (getPlay st pieces)
                elif MultiSet.size st.hand = 1u && MultiSet.contains 0u st.hand then
                    blankMove st pieces (getBoardSize boardP)
                    doMove (getPlay st pieces)
                else
                    startSearch st pieces (getBoardSize boardP)
                    doMove (getPlay st pieces)
       
            let msg = recv cstream
                       
            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                let placedLetterIDs = List.fold (fun x y -> fst(snd(y)) :: x) [] ms
                let hand = List.fold (fun x y -> MultiSet.removeSingle y x) st.hand placedLetterIDs
                let hand' = List.fold (fun x y -> MultiSet.add(fst(y)) (snd(y)) x) hand newPieces                             
                let st' = {st with hand = hand'; actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}  
                aux st'
            | RCM (CMPlayed (pid, ms, points)) ->
                let st' = {st with actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}
                aux st'
            | RCM (CMPlayFailed (pid, ms)) ->
                let st' = {st with actualBoard = updateActualBoard st ms; playerTurn = updatePlayerTurn st}
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
            (dictf : bool -> Dictionary.Dict) 
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

        fun () -> playGame cstream tiles (State.mkState Map.empty board dict playerNumber numPlayers playerTurn handSet) boardP         