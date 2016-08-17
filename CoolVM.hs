{-
    CoolVM.hs: A clean, lazily-evaluated, side-effect free virtual machine

    Copyright 2016 Mike Haskel (mike@haskels.org)

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

        http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
-}
module CoolVM where
import Data.Char
import System.IO

data Program =
    Context
    | WithContext Program Program

    | Eval Program Program

    | Sequence Program Program

    | Nil

    | Cons Program Program
    | Car Program
    | Cdr Program

    | Lambda Program
    | Apply Program Program

    | Symbol Symbol
    | CompareSymbol Program Program Program Program

    | Char Char
    | CompareChar Program Program
    | GeneralCategory Program
    
    | Read Program Program
    | Write Program Program
    | Halt

dataToProgram :: Data -> Program
dataToProgram ~(ConsData (SymbolData ((["CoolVM"], "Program"), command)) arguments) =
    case command of
        "context" -> Context
        "withContext" -> recurse2 WithContext
        "eval" -> recurse2 Eval
        "sequence" -> recurse2 Sequence
        "nil" -> Nil
        "cons" -> recurse2 Cons
        "car" -> recurse1 Car
        "cdr" -> recurse1 Cdr
        "lambda" -> recurse1 Lambda
        "apply" -> recurse2 Apply
        "symbol" -> let (ConsData (SymbolData sym) _) = arguments in Symbol sym
        "compareSymbol" -> recurse4 CompareSymbol
        "char" -> let (ConsData (CharData char) _) = arguments in Char char
        "compareChar" -> recurse2 CompareChar
        "generalCategory" -> recurse1 GeneralCategory
        "read" -> recurse2 Read
        "write" -> recurse2 Write
        "halt" -> Halt
    where recurse1 constructor =
            let (ConsData arg1 _) = arguments in constructor (dataToProgram arg1)
          recurse2 constructor =
            let (ConsData arg1 (ConsData arg2 _)) = arguments in constructor (dataToProgram arg1) (dataToProgram arg2)
          recurse4 constructor =
            let (ConsData arg1 (ConsData arg2 (ConsData arg3 (ConsData arg4 _)))) = arguments
            in constructor (dataToProgram arg1) (dataToProgram arg2) (dataToProgram arg3) (dataToProgram arg4)

-- ((namespace, type), constructor)
type Symbol = (([String], String), String)

data Data =
    NilData
    | ConsData Data Data
    | LambdaData (Data -> Data)
    | SymbolData Symbol
    | CharData Char
    | AgentData Agent

data Agent =
    ReadAgent Agent (Char -> Agent)
    | WriteAgent Char Agent
    | HaltAgent

eval :: Program -> Data -> Data
eval Context ctx = ctx
eval (WithContext prog eNewCtx) ctx =
    let newCtx = eval eNewCtx ctx
    in eval prog newCtx
eval (Eval eProg eNewCtx) ctx =
    let prog = eval eProg ctx
        newCtx = eval eNewCtx ctx
    in eval (dataToProgram prog) newCtx
eval (Sequence progA progB) ctx =
    seq (eval progA ctx) (eval progB ctx)
eval Nil ctx = NilData
eval (Cons eCar eCdr) ctx =
    let car = eval eCar ctx
        cdr = eval eCdr ctx
    in ConsData car cdr
eval (Car eCons) ctx =
    let (ConsData car cdr) = eval eCons ctx
    in car
eval (Cdr eCons) ctx =
    let (ConsData car cdr) = eval eCons ctx
    in cdr
eval (Lambda prog) ctx =
    LambdaData $ \input -> eval prog (ConsData input ctx)
eval (Apply eFun eArg) ctx =
    let (LambdaData fun) = eval eFun ctx
        arg = eval eArg ctx
    in fun arg
eval (Symbol sym) ctx = SymbolData sym
eval (CompareSymbol eSym1 eSym2 ifSame ifDifferent) ctx =
    let (SymbolData (t1, c1)) = eval eSym1 ctx
        (SymbolData (t2, c2)) = eval eSym2 ctx
    in if t1 == t2
       then if c1 == c2
            then eval ifSame ctx
            else eval ifDifferent ctx
       else undefined
eval (Char char) ctx = CharData char
eval (CompareChar eChar1 eChar2) ctx =
    let (CharData char1) = eval eChar1 ctx
        (CharData char2) = eval eChar2 ctx
    in if char1 == char2
       then SymbolData ((["CoolVM"], "Bool"), "true")
       else SymbolData ((["CoolVM"], "Bool"), "false")
eval (GeneralCategory eChar) ctx =
    let (CharData char) = eval eChar ctx
        gcString = case generalCategory char of
            UppercaseLetter -> "lu"
            LowercaseLetter -> "ll"
            TitlecaseLetter -> "lt"
            ModifierLetter -> "lm"
            OtherLetter -> "lo"
            NonSpacingMark -> "mn"
            SpacingCombiningMark -> "mc"
            EnclosingMark -> "me"
            DecimalNumber -> "nd"
            LetterNumber -> "nl"
            OtherNumber -> "no"
            ConnectorPunctuation -> "pc"
            DashPunctuation -> "pd"
            OpenPunctuation -> "ps"
            ClosePunctuation -> "pe"
            InitialQuote -> "pi"
            FinalQuote -> "pf"
            OtherPunctuation -> "po"
            MathSymbol -> "sm"
            CurrencySymbol -> "sc"
            ModifierSymbol -> "sk"
            OtherSymbol -> "so"
            Space -> "zs"
            LineSeparator -> "zl"
            ParagraphSeparator -> "zp"
            Control -> "cc"
            Format -> "cf"
            Surrogate -> "cs"
            PrivateUse -> "co"
            NotAssigned -> "cn"
    in SymbolData ((["CoolVM"], "GeneralCategory"), gcString)
eval (Read eOnEOF eOnChar) ctx =
    let (AgentData onEOF) = eval eOnEOF ctx
        (LambdaData onChar) = eval eOnChar ctx
    in AgentData $ ReadAgent onEOF (\char -> let (AgentData returnAgent) = onChar $ CharData char in returnAgent)
eval (Write eChar eContinue) ctx =
    let (CharData char) = eval eChar ctx
        (AgentData continue) = eval eContinue ctx
    in AgentData $ WriteAgent char continue
eval Halt ctx = AgentData HaltAgent


runAgent :: Agent -> IO ()
runAgent (ReadAgent onEOF onChar) =
    do isItEOF <- hIsEOF stdin
       (if isItEOF
        then runAgent onEOF
        else hGetChar stdin >>= runAgent . onChar)
runAgent (WriteAgent char continue) = hPutChar stdin char >> runAgent continue
runAgent HaltAgent = return ()
