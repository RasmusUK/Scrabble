namespace YourClientName

open System
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
        MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

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
        hand          : MultiSet.MultiSet<uint32>
    }

    let mkState ab b d pn h = {actualBoard = ab; board = b; dict = d;  playerNumber = pn; hand = h }

    let board st         = st.board
    let dict st          = st.dict
    let playerNumber st  = st.playerNumber
    let hand st          = st.hand

module Scrabble =
    open System.Threading
    let updateActualBoard (st:State.state) ms = List.fold (fun m x -> Map.add (fst x) (snd x |> snd |> fst) m) st.actualBoard ms
    
    let findChar i = Convert.ToChar(i + 64u)
    
    let charToValue (c:char) = Convert.ToUInt32(c) - 64u
    
    let validateWord lst = true
    
    let legalMove (partialWord:(coord * char)list) anchor =
        let aux = List.map (fun (x,_) -> x) partialWord
        match List.tryFind (fun x -> x = anchor) aux with
        | Some _ -> true
        | _ -> false
    let crossCheck square letter state = true
    
    let allValidChars node =
        let letters = seq {for i in 1u..26u -> findChar i} |> Seq.toList
        let rec aux validLetters = function
            | [] -> validLetters
            | x :: xs ->
                match step x node with
                | Some _ -> aux (x :: validLetters) xs
                | None _ -> aux validLetters xs
        aux [] letters
        
    let mutable legalMoves = List.empty
    
    let rec ExtendRight (partialWord:(coord * char)list) (node : Dict) square (state : State.state) squareIsTerminal anchor i j =
        let aux =
            if squareIsTerminal && legalMove partialWord anchor then
                legalMoves <- partialWord :: legalMoves         
        let isVacant =
            match Map.tryFind square state.actualBoard with
            | Some _ -> false
            | None -> true
        if isVacant then
            aux |> ignore
            let validLetters = allValidChars node
            for letter in validLetters do
                if MultiSet.contains (charToValue letter) state.hand && crossCheck square letter state then
                    let hand' = MultiSet.removeSingle (charToValue letter) state.hand
                    let actualBoard' = Map.add square letter state.actualBoard
                    let state' = {state with hand = hand'; actualBoard = actualBoard' }
                    match step letter node with
                    | Some (b, node') -> 
                        let partialWord' = (square, letter) :: partialWord
                        let square' = (fst square + i, snd square + j)
                        ExtendRight partialWord' node' square' state' b anchor i j
                    | None _ -> ()                
        else
            let l = state.actualBoard[square]
            match step l node with
            | Some (b,node') ->
                let partialWord' = (square, l) :: partialWord
                let square' = (fst square + i, snd square + j)
                ExtendRight partialWord' node' square' state b anchor i j
            | None _ -> ()
 
    let rec LeftPart (partialWord:(coord * char)list) dict square limit (state : State.state) isTerminal =
        for i in 0..limit do
            ExtendRight partialWord dict (fst square - i, snd square) state isTerminal square 1 0
            ExtendRight partialWord dict (fst square, snd square - i) state isTerminal square 0 1
                          
    let playGame cstream pieces (st : State.state) =

        let rec aux (st : State.state) =
            Print.printHand pieces (State.hand st)
    
            // remove the force print when you move on from manual input (or when you have learnt the format)
            forcePrint "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"
            let input =  System.Console.ReadLine()
            let move = RegEx.parseMove input

            debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
            send cstream (SMPlay move)

            let msg = recv cstream
            debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            match msg with
            | RCM (CMPlaySuccess(ms, points, newPieces)) ->
                let placedLetterIDs = List.fold (fun x y -> fst(snd(y)) :: x) [] ms
                let hand = List.fold (fun x y -> MultiSet.removeSingle y x) st.hand placedLetterIDs
                let hand' = List.fold (fun x y -> MultiSet.add(fst(y)) (snd(y)) x) hand newPieces
                let st' = {st with hand = hand'; actualBoard = updateActualBoard st ms}
                for coord in st'.actualBoard do
                    LeftPart [] st'.dict coord.Key (MultiSet.size st'.hand |> int) st' false 
                legalMoves <- []   
                aux st'
            | RCM (CMPlayed (pid, ms, points)) ->
                let st' = {st with actualBoard = updateActualBoard st ms}
                for coord in st'.actualBoard do
                    LeftPart [] st'.dict coord.Key (MultiSet.size st'.hand |> int) st' false 
                legalMoves <- []  
                aux st'
            | RCM (CMPlayFailed (pid, ms)) ->
                (* Failed play. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
            | RCM (CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err -> printfn "Gameplay Error:\n%A" err; aux st


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
            (sprintf "Starting game!
                      number of players = %d
                      player id = %d
                      player turn = %d
                      hand =  %A
                      timeout = %A\n\n" numPlayers playerNumber playerTurn hand timeout)

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        let dict = dictf false // Uncomment if using a trie for your dictionary
        let board = Parser.mkBoard boardP
                  
        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState Map.empty board dict playerNumber handSet)
        