// ScrabbleUtil contains the types coord, boardProg, and SquareProg. Remove these from your file before proceeding.
// Also note that the modulse Ass7 and ImpParser have been merged to one module called Parser.

// Insert your Parser.fs file here from Assignment 7. All modules must be internal.

module internal Parser

    open StateMonad
    open ScrabbleUtil // NEW. KEEP THIS LINE.
    open System
    open Eval
    open FParsecLight.TextParser     // Industrial parser-combinator library. Use for Scrabble Project.
    
    
    let pIntToChar  = pstring "intToChar"
    let pPointValue = pstring "pointValue"

    let pCharToInt  = pstring "charToInt"
    let pToUpper    = pstring "toUpper"
    let pToLower    = pstring "toLower"
    let pCharValue  = pstring "charValue"

    let pTrue       = pstring "true"
    let pFalse      = pstring "false"
    let pIsDigit    = pstring "isDigit"
    let pIsLetter   = pstring "isLetter"
    let pIsVowel   = pstring "isVowel"

    let pif       = pstring "if"
    let pthen     = pstring "then"
    let pelse     = pstring "else"
    let pwhile    = pstring "while"
    let pdo       = pstring "do"
    let pdeclare  = pstring "declare"

    
    let pletter        = satisfy Char.IsLetter <?> "letter"
    let palphanumeric  = satisfy Char.IsLetterOrDigit <?> "alphanumeric"
    let whitespaceChar = satisfy Char.IsWhiteSpace <?> "whitespace"
    let spaces         = many whitespaceChar <?> "space"
    let spaces1        = many1 whitespaceChar <?> "space1"

    let (.>*>.) p1 p2 = p1 .>> spaces .>>. p2 <?> "Unexpected ' ' at start"
    let (.>*>) p1 p2 = p1 .>> spaces .>> p2
    let (>*>.) p1 p2  = p1 .>> spaces >>. p2

    let parenthesise p = pchar '(' >*>. p .>*> pchar ')' <?> "Unexpected char"
    let parenthesise2 p = pchar '{' >*>. p .>*> pchar '}'
    
    let palphanumericsOrUnderscore = many (palphanumeric <|> pchar '_')
    
    let pid =  ((pletter <|> pchar '_' .>>. palphanumericsOrUnderscore) |>> (fun r -> fst(r) :: snd(r)) |>> fun l -> String(List.toArray l) |> string) <?> "identifier"
    let unop p1 p2 = p1 >*>. p2
    
    let binop op p1 p2 = p1 .>*> op .>*>. p2


    let TermParse, tref = createParserForwardedToRef<aExp>()
    let ProdParse, pref = createParserForwardedToRef<aExp>()
    let AtomParse, aref = createParserForwardedToRef<aExp>()
    
    let CParse, cref = createParserForwardedToRef<cExp>()
    
    let B1Parse, b1ref = createParserForwardedToRef<bExp>()
    let B2Parse, b2ref = createParserForwardedToRef<bExp>()
    let B3Parse, b3ref = createParserForwardedToRef<bExp>()
    
    let S1Parse, s1ref = createParserForwardedToRef<stm>()
    let S2Parse, s2ref = createParserForwardedToRef<stm>()



    let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
    let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"

    do tref := choice [AddParse; SubParse; ProdParse]    

    let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
    let DivParse = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
    
    let ModParse = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"


    do pref := choice [MulParse; DivParse; ModParse; AtomParse]
     
    let AexpParse = TermParse   

    let NParse   = pint32 |>> N <?> "Int"
    let VParse   = pid |>> V <?> "String"
    let ParParse = parenthesise TermParse
    let PVParse = pPointValue >*>. ParParse |>> PV <?> "PV"
    let NegationParse = pchar '-' >>. pint32 |>> (fun x -> Mul ((N -1),(N x))) <?> "Neg"
    let CharToIntParse = pCharToInt >*>. parenthesise CParse |>> CharToInt <?> "CharToInt"

    do aref := choice [NegationParse; PVParse; CharToIntParse; VParse; NParse; ParParse]   
    
    let CharParse = (pchar ''') >>. anyChar .>> (pchar ''') |>> C <?> "Char"
    let CharValueParse = pCharValue >*>. parenthesise TermParse |>> CV <?> "CV"
    let ToUpperParse = pToUpper >*>. parenthesise CParse |>> ToUpper <?> "ToUpper"
    let ToLowerParse = pToLower >*>. parenthesise CParse |>> ToLower <?> "ToLower"
    let IntToCharParse = pIntToChar >*>. parenthesise TermParse |>> IntToChar <?> "IntToChar"
   
    do cref := choice [CharParse; CharValueParse; ToUpperParse; ToLowerParse; IntToCharParse]

    let CexpParse = CParse
        
    let BexpParse = B1Parse
    
    let BConParse =  binop (pstring "/\\") B2Parse B1Parse |>> (fun x -> (.&&.) (fst x) (snd x))<?> "/\\"
    let BDisParse =  binop (pstring "\\/") B2Parse B1Parse |>> (fun x -> (.||.) (fst x) (snd x))<?> "\\/"
    
    do b1ref := choice [BConParse; BDisParse; B2Parse]
    
    let BEqParse =  binop (pstring "=") TermParse TermParse |>> (fun x -> (.=.) (fst x) (snd x))<?> "="
    let BNEqParse =  binop (pstring "<>") TermParse TermParse |>> (fun x -> (.<>.) (fst x) (snd x))<?> "<>"
    let BNleParse =  binop (pstring "<") TermParse TermParse |>> (fun x -> (.<.) (fst x) (snd x))<?> "<"
    let BNleEqParse =  binop (pstring "<=") TermParse TermParse |>> (fun x -> (.<=.) (fst x) (snd x))<?> "<="
    let BNgeParse =  binop (pstring ">") TermParse TermParse |>> (fun x -> (.>.) (fst x) (snd x))<?> ">"
    
    let BNgeEqParse =  binop (pstring ">=") TermParse TermParse |>> (fun x -> (.>=.) (fst x) (snd x))<?> ">="
    
    do b2ref := choice [BEqParse; BNEqParse; BNleParse; BNleEqParse; BNgeParse; BNgeEqParse; B3Parse]
    
    let BNotParse = pchar '~' >>. B1Parse |>> (~~) <?> "Not"
    let BIsLetterParse= pIsLetter >*>. CParse |>> IsLetter <?> "Letter"
    
    let BIsVowelParse= pIsVowel >*>. CParse |>> IsVowel <?> "Vowel"
    
    let BIsDigitParse= pIsDigit >*>. CParse |>> IsDigit <?> "Digit"

    let BIsTrueParse = pTrue |>> (fun _ -> TT) <?> "True"
    let BIsFalseParse = pFalse |>> (fun _ -> FF) <?> "False" 
    let BIsPare = parenthesise B1Parse

    do b3ref := choice [BNotParse; BIsLetterParse; BIsVowelParse; BIsDigitParse; BIsTrueParse; BIsFalseParse; BIsPare]


    let stmntParse = S1Parse
    
    let SDeclareParse = pdeclare .>> spaces1 >>. pid |>> Declare <?> "Declare"
    let SAssParse = binop (pstring ":=") pid TermParse |>> Ass <?> "Assign"
    let SSeq = binop (pchar ';') S2Parse S1Parse |>> Seq <?> "Seq"
    let SITE =
        let b = unop pif (parenthesise B1Parse)
        let x1 = binop pthen b (binop pelse (parenthesise2 S1Parse) (parenthesise2 S1Parse)) |>> (fun (x,(y,z)) -> ITE (x,y,z)) <?> "ITE"
        let x2 = binop pthen b (parenthesise2 S1Parse) |>> (fun (a,b) -> ITE (a,b,Skip)) <?> "ITE"
        x1 <|> x2
    let SWHILE =
        let b = unop pwhile (parenthesise B1Parse)
        binop pdo b (parenthesise2 S1Parse) |>> While <?> "While"
    let SPare = parenthesise2 S1Parse
    
    do s1ref := choice [SSeq;  S2Parse]
    do s2ref := choice [SITE; SWHILE; SDeclareParse; SAssParse]

    (* The rest of your parser goes here *)
    type word   = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>
    //The word; the position in the word; accumulator ; then result
    type square = Map<int, squareFun>
    //Priority ; squarefun
    let parseSquareProg (sqp:squareProg) : square = Map.map (fun _ v ->  stmntToSquareFun (getSuccess(run stmntParse v))) sqp
    type boardFun2 = coord -> Result<square option, Error>
        
    type board = {
        center        : coord
        defaultSquare : square
        squares       : boardFun2
    }
    let parseBoardProg (s:string) (sqs:Map<int,square>) : boardFun2 = stmntToBoardFun2 (getSuccess(run stmntParse s)) sqs
    let mkBoard (prog:boardProg) =
        let ds = parseSquareProg prog.squares[0]
        let sq = parseBoardProg prog.prog (Map.map (fun _ -> parseSquareProg) prog.squares)
        {
        center        = prog.center
        defaultSquare = ds
        squares       = sq
    }