namespace YourClientName

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
    
    let findChar = function
        | 1u -> 'A'
        | 2u -> 'B'
        | 3u -> 'C'
        | 4u -> 'D'
        | 5u -> 'E'
        | 6u -> 'F'
        | 7u -> 'G'
        | 8u -> 'H'
        | 9u -> 'I'
        | 10u -> 'J'
        | 11u -> 'K'
        | 12u -> 'L'
        | 13u -> 'M'
        | 14u -> 'N'
        | 15u -> 'O'
        | 16u -> 'P'
        | 17u -> 'Q'
        | 18u -> 'R'
        | 19u -> 'S'
        | 20u -> 'T'
        | 21u -> 'U'
        | 22u -> 'V'
        | 23u -> 'W'
        | 24u -> 'X'
        | 25u -> 'Y'
        | 26u -> 'Z'
        | _ -> '_'
    
    let validateWord lst = true
    
    let rec findHWord (acc:(coord * char)list) board dict (hand:MultiSet.MultiSet<uint32>) =
        let currentCoord = fst(acc.Head)
        let nextCoord = (fst(currentCoord)+1,snd(currentCoord))
        match Map.tryFind nextCoord board with
        | Some c ->
            match step c dict with
            | Some (hasWord,dict') when hasWord = true ->
                if validateWord ((nextCoord,c)::acc)
                then Some ((nextCoord,c)::acc)
                else findHWord ((nextCoord,c)::acc) board dict' hand // Goes to next char and tries to see if can add more
            | Some (_,dict') -> findHWord ((nextCoord,c)::acc) board dict' hand
            | None -> None
        | None ->
            MultiSet.fold (fun x y z ->
                match step (findChar y) dict with
                | Some (hasWord,dict') when hasWord = true ->
                    if validateWord ((nextCoord,(findChar y))::acc)
                    then Some ((nextCoord,(findChar y))::acc)
                    else (findHWord ((nextCoord,(findChar y))::acc) board dict' (MultiSet.removeSingle y hand)) 
                | Some (_,dict') -> (findHWord ((nextCoord,(findChar y))::acc) board dict' (MultiSet.removeSingle y hand))
                | None -> None) (Some []) hand
                // (findHWord ((nextCoord,(findChar y))::acc) board dict (MultiSet.removeSingle y hand))::x)
               
        
    (*let findHorizontalWord (st:State.state) coord =
        
        let fstCharacter = st.actualBoard[coord]
        let word = []
        let rec aux character dict hand =
            match step character dict with
            | Some (hasWord,_) when hasWord = true -> Some word
            | Some (_,dict') ->
                match hand with
                | [] -> None
                | x::xs ->
                    word @ (findChar x)
                    aux (findChar x) dict' xs 
            | None _ -> None
        // aux (findChar (MultiSet.toList st.hand).Head) st.dict (MultiSet.toList st.hand).Tail
        aux fstCharacter st.dict (MultiSet.toList st.hand)*)
            
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
                aux st'
            | RCM (CMPlayed (pid, ms, points)) ->
                let st' = {st with actualBoard = updateActualBoard st ms}
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
        