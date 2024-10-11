// A parser for the Fun language
//================================
//
// call with 
//
//     amm fun_parser.sc fact.fun

//     amm fun_parser.sc defs.fun
//
// this will generate a parse-tree from a list
// of tokens

import scala.language.implicitConversions    
import scala.language.reflectiveCalls

import $file.fun_tokens, fun_tokens._ 


// Parser combinators
//    type parameter I needs to be of Seq-type
//
type IsSeq[I] = I => Seq[_]

/*
abstract class Parser[I, T](using is: I => Seq[_])  {
  def parse(in: I): Set[(T, I)]  

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if is(tl).isEmpty) yield hd
}
*/


abstract class Parser[I, T](using is: I => Seq[_]) {
  def parse(ts: I): Set[(T, I)]

  def parse_single(ts: I) : T = 
    parse(ts).partition(p => is(p._2).isEmpty) match {
      case (good, _) if !good.isEmpty => good.head._1
      case (_, err) => { println (s"Parse Error\n${err.minBy(p => is(p._2).length)}") ; sys.exit(-1) }
    }
}

// convenience for writing grammar rules
case class ~[+A, +B](_1: A, _2: B)

// parser combinators

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)   
}

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

case object StringParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]) = tokens match {
    case T_STRING(x) :: cs  => Set((x, cs)) 
    case _ => Set()
  }
}

// more convenient syntax for parser combinators
extension [I : IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

def ListParser[I, T, S](p: => Parser[I, T], q: => Parser[I, S])(using is: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)).map{ case (x:T) ~ (y:S) ~ (z:List[T]) => x :: z } ||
  (p.map[List[T]]{s => List(s)})
}

case class TokParser(tok: Token) extends Parser[List[Token], Token] {
  def parse(ts: List[Token]) = ts match {
    case t::ts if (t == tok) => Set((t, ts)) 
    case _ => Set ()
  }
}

implicit def token2tparser(t: Token) : Parser[List[Token], Token] = TokParser(t)


extension (t: Token) {
  def || (q : => Parser[List[Token], Token]) = new AltParser[List[Token], Token](t, q)
  def map[S] (f: => Token => S) = new MapParser[List[Token], Token, S](t, f)
  def ~[S](q : => Parser[List[Token], S]) = new SeqParser[List[Token], Token, S](t, q)
}

case object NumParser extends Parser[List[Token], Int] {
  def parse(ts: List[Token]) = ts match {
    case T_NUM(n)::ts => Set((n, ts)) 
    case _ => Set ()
  }
}

case object FloatParser extends Parser[List[Token], Double] {
  def parse(tokens: List[Token]): Set[(Double, List[Token])] = tokens match {
    case T_DOUBLE(s) :: cs => Set((s, cs))
    case _ => Set()
  }
}

case object IdParser extends Parser[List[Token], String] {
  def parse(ts: List[Token]) = ts match {
    case T_ID(s)::ts => Set((s, ts)) 
    case _ => Set ()
  }
}

case object ParamParser extends Parser[List[Token],(String,String)] {
  def parse(tokens: List[Token]) = tokens match {
    case T_ID(x)::T_COLON::T_TYPE(y):: cs  => Set(((x,y), cs)) 
    case _  => Set()
  }
}

case object TokenTypeParser extends Parser[List[Token], String] {
  def parse(tokens: List[Token]) = tokens match {
    case T_TYPE(x):: cs  => Set((x, cs)) 
    case _ => Set()
  }
}

case object CharParser extends Parser[List[Token], Int] {
  def parse(tokens: List[Token]) = tokens match {
    case T_CHAR(x):: cs  => Set((x, cs)) 
    case _ => Set()
  }
}

// Abstract syntax trees for the Fun language
abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String,String)], ty: String, body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String, v: Int) extends Decl
case class FConst(name: String, x: Double) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp  // integer numbers
case class FNum(i: Double) extends Exp  // float numbers
case class ChConst(c: Int) extends Exp  // character constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp  // expressions separated by semicolons
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp
case class StringConst(s: String) extends Exp //This is temp idk what to do with strigns lol


// Grammar Rules for the Fun language

// arithmetic expressions
lazy val Exp: Parser[List[Token], Exp] = 
  (T_KWD("if") ~ BExp ~ T_KWD("then") ~ Exp ~ T_KWD("else") ~ Exp).map{ case _ ~ x ~ _ ~ y ~ _ ~ z => If(x, y, z): Exp } ||
  (T_LPAREN ~ Exp ~ T_RPAREN).map{ case _ ~ y ~ _ => y: Exp } ||
  (L ~ T_SEMI ~ Exp).map{ case x ~ _ ~ y => Sequence(x, y): Exp } || L
lazy val L: Parser[List[Token], Exp] = 
  (T ~ T_OP("+") ~ Exp).map{ case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (T ~ T_OP("-") ~ Exp).map{ case x ~ _ ~ z => Aop("-", x, z): Exp } || T  
lazy val T: Parser[List[Token], Exp] =  
  (F ~ T_OP("*") ~ T).map{ case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (F ~ T_OP("/") ~ T).map{ case x ~ _ ~ z => Aop("/", x, z): Exp } || 
  (F ~ T_OP("%") ~ T).map{ case x ~ _ ~ z => Aop("%", x, z): Exp } || F
lazy val F: Parser[List[Token], Exp] = 
  (IdParser ~ T_LPAREN ~ ListParser(Exp, T_COMMA) ~ T_RPAREN).map
    { case x ~ _ ~ z ~ _ => Call(x, z): Exp } ||
  (IdParser ~ T_LPAREN ~ T_RPAREN).map
    { case x ~ _ ~ _ => Call(x, Nil): Exp } ||
  (T_ID("skip")).map{case x => Call("skip",Nil)} ||
  IdParser.map{ case x => Var(x): Exp } || 
  NumParser.map{ case x => Num(x): Exp } ||
  FloatParser.map{case x => FNum(x)} || 
  CharParser.map{case x => ChConst(x)} ||
  StringParser.map{case x => StringConst(x)}


// boolean expressions
lazy val BExp: Parser[List[Token], BExp] = 
  (Exp ~ T_OP("==") ~ Exp).map{ case x ~ _ ~ z => Bop("==", x, z): BExp } || 
  (Exp ~ T_OP("!=") ~ Exp).map{ case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
  (Exp ~ T_OP("<") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  x, z): BExp } || 
  (Exp ~ T_OP(">") ~ Exp) .map{ case x ~ _ ~ z => Bop("<",  z, x): BExp } || 
  (Exp ~ T_OP("<=") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", x, z): BExp } || 
  (Exp ~ T_OP("=>") ~ Exp).map{ case x ~ _ ~ z => Bop("<=", z, x): BExp }  

lazy val Defn: Parser[List[Token], Decl] =
   (T_KWD("def") ~ IdParser ~ T_LPAREN ~ ListParser(ParamParser, T_COMMA) ~ T_RPAREN ~ T_COLON ~ TokenTypeParser ~ T_OP("=") ~ Exp).map{ case _ ~ y ~ _ ~ w ~ _ ~ _ ~ x ~ _ ~ r => Def(y, w, x, r): Decl } ||
   (T_KWD("val") ~ IdParser ~ T_COLON ~ T_TYPE("Int") ~ T_OP("=") ~ NumParser).map{case _ ~ x ~ _ ~ _ ~ _ ~ y => Const(x, y): Decl} ||
   (T_KWD("val") ~ IdParser ~ T_COLON ~ T_TYPE("Double") ~ T_OP("=") ~ FloatParser).map{case _ ~ x ~ _ ~ _ ~ _ ~ y => FConst(x, y): Decl} || 
   (T_KWD("def") ~ IdParser ~ T_LPAREN ~ T_RPAREN ~ T_COLON ~ TokenTypeParser ~ T_OP("=") ~ Exp).map {case _ ~ x ~ _ ~ _ ~ _ ~ z ~ _ ~ e => Def(x, Nil, z, e): Decl}

lazy val Prog: Parser[List[Token], List[Decl]] =
  (Defn ~ T_SEMI ~ Prog).map{ case x ~ _ ~ z => x :: z : List[Decl] } ||
  (Exp.map((s) => List(Main(s)) : List[Decl]))



// Reading tokens and Writing parse trees

// pre-2.5.0 ammonite 
// import ammonite.ops._

// post 2.5.0 ammonite
// import os._

// def parse_tks(tks: List[Token]) : Decl = 
//   Defn.parse_single(tks)

// val fname = "fact.fun"
// val tks = tokenise(os.read(os.pwd / fname))
// println(Prog.parse_single(tks))



