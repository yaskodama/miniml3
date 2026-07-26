(* ================================================================
   miniml.lex -- ML-Lex の字句定義。
   miniml2 の手書き字句解析器と同じ記号を切り出す。
   入れ子のコメントと文字列は開始状態で扱う。
   ================================================================ *)

structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

exception LexError of string

val line   = ref 1
val depth  = ref 0
val strbuf = ref ([] : char list)

val eof = fn () => Tokens.EOF (!line, !line)

fun keyword (s, p) =
    case s of
        "let"      => Tokens.LET (p, p)
      | "rec"      => Tokens.REC (p, p)
      | "in"       => Tokens.IN (p, p)
      | "if"       => Tokens.IF (p, p)
      | "then"     => Tokens.THEN (p, p)
      | "else"     => Tokens.ELSE (p, p)
      | "fun"      => Tokens.FUN (p, p)
      | "function" => Tokens.FUNCTION (p, p)
      | "match"    => Tokens.MATCH (p, p)
      | "with"     => Tokens.WITH (p, p)
      | "true"     => Tokens.TRUE (p, p)
      | "false"    => Tokens.FALSE (p, p)
      | "mod"      => Tokens.MOD (p, p)
      | _          => Tokens.ID (s, p, p)

%%

%header (functor MinimlLexFun (structure Tokens : Miniml_TOKENS));
%s COMMENT STR;

digit  = [0-9];
idchar = [A-Za-z0-9_'];
idfst  = [A-Za-z_];
ws     = [\ \t\013];

%%

<INITIAL>{ws}+      => (continue ());
<INITIAL>\n         => (line := !line + 1; continue ());

<INITIAL>"(*"       => (YYBEGIN COMMENT; depth := 1; continue ());
<COMMENT>"(*"       => (depth := !depth + 1; continue ());
<COMMENT>"*)"       => (depth := !depth - 1;
                        if !depth = 0 then YYBEGIN INITIAL else ();
                        continue ());
<COMMENT>\n         => (line := !line + 1; continue ());
<COMMENT>.          => (continue ());

<INITIAL>"\""       => (YYBEGIN STR; strbuf := []; continue ());
<STR>"\""           => (YYBEGIN INITIAL;
                        Tokens.STRING (String.implode (List.rev (!strbuf)),
                                       !line, !line));
<STR>"\\n"          => (strbuf := #"\n" :: !strbuf; continue ());
<STR>"\\t"          => (strbuf := #"\t" :: !strbuf; continue ());
<STR>"\\\\"         => (strbuf := #"\\" :: !strbuf; continue ());
<STR>"\\\""         => (strbuf := #"\"" :: !strbuf; continue ());
<STR>"\\".          => (strbuf := String.sub (yytext, 1) :: !strbuf; continue ());
<STR>\n             => (line := !line + 1;
                        strbuf := #"\n" :: !strbuf; continue ());
<STR>.              => (strbuf := String.sub (yytext, 0) :: !strbuf; continue ());

<INITIAL>{digit}+   => (case IntInf.fromString yytext of
                            SOME n => Tokens.NUM (n, !line, !line)
                          | NONE => raise LexError ("bad integer " ^ yytext));

<INITIAL>{idfst}{idchar}* => (if yytext = "_" then Tokens.UNDERSCORE (!line, !line)
                              else keyword (yytext, !line));

<INITIAL>"->"       => (Tokens.ARROW (!line, !line));
<INITIAL>"::"       => (Tokens.CONS (!line, !line));
<INITIAL>"<="       => (Tokens.LE (!line, !line));
<INITIAL>">="       => (Tokens.GE (!line, !line));
<INITIAL>"<>"       => (Tokens.NE (!line, !line));
<INITIAL>"&&"       => (Tokens.ANDALSO (!line, !line));
<INITIAL>"||"       => (Tokens.ORELSE (!line, !line));
<INITIAL>"+"        => (Tokens.PLUS (!line, !line));
<INITIAL>"-"        => (Tokens.MINUS (!line, !line));
<INITIAL>"*"        => (Tokens.TIMES (!line, !line));
<INITIAL>"/"        => (Tokens.DIVIDE (!line, !line));
<INITIAL>"^"        => (Tokens.CARET (!line, !line));
<INITIAL>"="        => (Tokens.EQ (!line, !line));
<INITIAL>"<"        => (Tokens.LT (!line, !line));
<INITIAL>">"        => (Tokens.GT (!line, !line));
<INITIAL>","        => (Tokens.COMMA (!line, !line));
<INITIAL>"|"        => (Tokens.BAR (!line, !line));
<INITIAL>"("        => (Tokens.LPAREN (!line, !line));
<INITIAL>")"        => (Tokens.RPAREN (!line, !line));
<INITIAL>"["        => (Tokens.LBRACKET (!line, !line));
<INITIAL>"]"        => (Tokens.RBRACKET (!line, !line));
<INITIAL>";"        => (Tokens.SEMI (!line, !line));

<INITIAL>.          => (raise LexError ("unexpected character `" ^ yytext ^ "'"));
