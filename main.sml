(* ================================================================
   main.sml -- ML-Lex / ML-Yacc が生成した部品を繋いで REPL にする。
   ================================================================ *)

structure MinimlLrVals = MinimlLrValsFun (structure Token = LrParser.Token)
structure MinimlLex    = MinimlLexFun (structure Tokens = MinimlLrVals.Tokens)
structure MinimlParser =
    Join (structure ParserData = MinimlLrVals.ParserData
          structure Lex        = MinimlLex
          structure LrParser   = LrParser)

structure Main =
struct
  open Absyn

  exception Parse_error of string
  exception Done                (* 入力の終わり。EOF 検出専用。 *)

  (* フレーズは `;' で終わる。文法規則には `;' を入れず、%eop で
     受理を打ち切らせているので、余った `;' は次の周回で読み飛ばす。 *)
  fun repl (ins, prompt) =
      let
        val type_env = ref Prims.type_env_initial
        val val_env  = ref Prims.val_env_initial

        fun say s = (print s; TextIO.flushOut TextIO.stdOut)

        val fresh = ref true
        fun readLine _ =
            (if prompt then say (if !fresh then "## " else "   ") else ();
             fresh := false;
             case TextIO.inputLine ins of SOME s => s | NONE => "")

        val stream = ref (MinimlParser.makeLexer readLine)

        val eofTok  = MinimlLrVals.Tokens.EOF (0, 0)
        val semiTok = MinimlLrVals.Tokens.SEMI (0, 0)

        fun peekIs tok =
            let val (t, _) = MinimlParser.Stream.get (!stream)
            in MinimlParser.sameToken (t, tok) end
        fun drop () = stream := #2 (MinimlParser.Stream.get (!stream))

        (* 前のフレーズが残した `;' と、空フレーズを読み飛ばす *)
        fun skipSemis () = if peekIs semiTok then (drop (); skipSemis ()) else ()
        (* 誤りのあとは次の `;' まで捨てる *)
        fun resync () =
            if peekIs semiTok orelse peekIs eofTok then () else (drop (); resync ())

        (* mlyacc は誤りの修復案まで作るが、こちらは修復せず打ち切るので
           位置だけを報告する。 *)
        fun onError (_, l, _) =
            raise Parse_error ("syntax error at line " ^ Int.toString l)

        fun run phrase =
            case phrase of
                Expr e =>
                  let val ty = Types.type_exp (!type_env) e
                      val v  = Value.eval (!val_env) e
                  in say ("- : " ^ Show.showTypeTop ty
                          ^ " = " ^ Show.showValue v ^ "\n")
                  end
              | Def (r, n, e) =>
                  let val tenv = Types.type_def (!type_env) (r, n, e)
                      val venv = Value.value_definition (!val_env) (r, n, e)
                  in case (tenv, venv) of
                         ((_, sch) :: _, (_, v) :: _) =>
                           say (n ^ " : " ^ Show.showSchema sch
                                ^ " = " ^ Show.showValue v ^ "\n")
                       | _ => ();
                     type_env := tenv;
                     val_env := venv
                  end

        fun step () =
            (fresh := true;
             skipSemis ();
             if peekIs eofTok then raise Done else ();
             let val (phrase, rest) = MinimlParser.parse (0, !stream, onError, ())
             in stream := rest; run phrase end
             handle
                 Parse_error m => (say ("Parse error: " ^ m ^ ".\n"); resync ())
               | MinimlParser.ParseError => (say "Parse error.\n"; resync ())
               | MinimlLex.UserDeclarations.LexError m =>
                   (say ("Lexical error: " ^ m ^ ".\n"); resync ())
               | Types.Type_error m => (say ("Type error: " ^ m ^ ".\n"); resync ())
               | Value.Eval_error m => (say ("Runtime error: " ^ m ^ ".\n"); resync ())
               | Types.Conflict (a, b) =>
                   (say ("Type error: cannot match " ^ Show.showTypeTop a
                         ^ " with " ^ Show.showTypeTop b ^ ".\n"); resync ())
               | Types.Circulation (a, b) =>
                   (say ("Type error: cyclic type, " ^ Show.showTypeTop a
                         ^ " occurs in " ^ Show.showTypeTop b ^ ".\n"); resync ())
               | Value.Fail_filtrate =>
                   (say "Runtime error: pattern matching failed.\n"; resync ())
               | Done => raise Done
               | Util.End_of_system => raise Util.End_of_system
               | Overflow => (say "Runtime error: integer overflow.\n"; resync ())
               | Div      => (say "Runtime error: division by zero.\n"; resync ())
               | e => (say ("Runtime error: " ^ exnMessage e ^ ".\n"); resync ()))
      in
        (while true do step ())
        (* miniml2 と同じく、入力の終わりで改行を一つ出す *)
        handle Done => print "\n"
             | Util.End_of_system => print "End of MINIML3...\n"
      end

  fun run () = repl (TextIO.stdIn, true)

  fun runFile name =
      let val ins = TextIO.openIn name
      in repl (ins, false) handle e => (TextIO.closeIn ins; raise e);
         TextIO.closeIn ins
      end

  fun main () =
      case CommandLine.arguments () of
          [] => run ()
        | files => List.app runFile files
end

val () = Main.main ()
