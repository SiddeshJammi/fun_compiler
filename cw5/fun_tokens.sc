// Rexp
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 

// Values, you might have to extend them 
// according to which values you want to create
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

// Convenience for typing
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}

implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

extension (r: Rexp) {
  def ~ (s: Rexp) = SEQ(r, s)
  def % = STAR(r)
  def | (s: Rexp) = ALT(r, s)
}


extension (s: String) {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// nullable
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(cs) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(r1) => true
  case NTIMES(r1, n) => if (n == 0) true else nullable(r1)
  case RECD(_, r1) => nullable(r1)

}

// der
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case OPTIONAL(r1) => der(c,r1)
  case RANGE(cs) => if (cs.contains(c)) ONE else ZERO
  case NTIMES(r,n) => if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
  case PLUS(r1) =>  SEQ(der(c,r1),STAR(r1))
  case RECD(_, r1) => der(c, r1)
}

// Flatten
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// Env
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// Mkeps
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil) 
  case RECD(x, r) => Rec(x, mkeps(r))
  case OPTIONAL(r) => if (nullable(r)) mkeps(r) else Empty
  case PLUS(r1) => Stars(Nil)
  case NTIMES(r,n) => if (n == 0) Empty else Sequ(Empty,mkeps(NTIMES(r,n-1)))
}

// Inj
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c)
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case(RANGE(ds), Empty) => Chr(c)
  case(OPTIONAL(r), v) => inj(r,c,v)
  case (PLUS(r),Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (NTIMES(r,n),Sequ(v1,v2))=> Sequ(inj(r,c,v1),v2)
}

// Rectification functions
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// Simp
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// Lex
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}
 
def ders_simp(cs: List[Char], r: Rexp) : Rexp = cs match {
  case Nil => r
  case c::cs => ders_simp(cs, simp(der(c, r))._1)
} 

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList)) 

// Language specific code
val COLON : Rexp = ":"
val KEYWORD : Rexp =  "if" | "then" | "else" | "true" | "false" | "def" | "val"
val OP : Rexp = "=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "%" | "<=" | ">=" | "&&" | "||" | "/"
val LET: Rexp = RANGE(('A' to 'Z').toSet | ('a' to 'z').toSet)
val SEMI : Rexp = ";"
val COMMA : Rexp = ","
val SYM : Rexp =  LET | "." | "_" | ">" | "<" | "=" | "," | ":" | "\\"
val LPAREN : Rexp = "(" | "{"
val RPAREN : Rexp = ")" | "}"
val WHITESPACE : Rexp = PLUS(" "| "\n" | "\t" | "\r")
val DIGIT : Rexp = RANGE(('0' to '9').toSet)
val ID : Rexp = LET ~ STAR(LET| DIGIT | "_")
val DOUBLE : Rexp = OPTIONAL("-") ~ PLUS(DIGIT) ~ "." ~ PLUS(DIGIT)
val STRING : Rexp = "\"" ~ STAR(SYM | WHITESPACE | DIGIT | OP) ~ "\""
val CHARV : Rexp = "\'" ~ STAR(SYM | WHITESPACE | DIGIT | OP) ~ "\'"
val NUM : Rexp = OPTIONAL("-") ~ PLUS(DIGIT)
val EOL : Rexp = "\n" | "\t" | "\r"
val COMMENT : Rexp = "//" ~ STAR(SYM | " " | DIGIT | LPAREN | SEMI | RPAREN | OP | STRING) ~ EOL
val TYPE : Rexp = "Int" | "Double" | "Void"
                  

val FUN_REGS = (  ("t" $ TYPE) | 
                  ("k" $ KEYWORD) | 
                  ("o" $ OP) | 
                  ("str" $ STRING) |
                  ("ch" $ CHARV) |
                  ("lp" $ LPAREN) |
                  ("rp" $ RPAREN) |
                  ("s" $ SEMI) |
                  ("colon" $ COLON) |
                  ("com" $ COMMA) | 
                  ("w" $ WHITESPACE) | 
                  ("i" $ ID) | 
                  ("n" $ NUM) |
                  ("d" $ DOUBLE) |
		              ("c" $ COMMENT)).%

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

// Token
abstract class Token extends Serializable 
case class T_KWD(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STRING(s: String) extends Token
case object T_COMMA extends Token
case object T_COLON extends Token
case object T_SEMI extends Token
case class T_ID(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_DOUBLE(n: Double) extends Token
case class T_TYPE(s: String) extends Token
case class T_CHAR(s: Int) extends Token
case object T_RPAREN extends Token
case object T_LPAREN extends Token


val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KWD(s)
  case ("o", s) => T_OP(s)
  case ("str", s) => T_STRING(s.replaceAll("\"", ""))
  case ("lp", _) => T_LPAREN
  case ("rp", _) => T_RPAREN
  case ("s", _) => T_SEMI
  case ("colon",_) => T_COLON
  case ("com", _) => T_COMMA
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("d", s) => T_DOUBLE(s.toDouble)
  case ("t", s) => T_TYPE(s)
  case ("ch", s) => T_CHAR(s.replaceAll("\'", "").replace("\\n","\n").toCharArray.head.toInt)
}

// Tokenise
def tokenise(s: String) : List[Token] = 
  lexing_simp(FUN_REGS, s).collect(token)


// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._

//@doc("Tokenising a file.")


