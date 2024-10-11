// typing
type Ty = String
type TyEnv = Map[String, Ty]

// initial typing environment
val initialEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
                                "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void", "print_string" -> "Void")

val typeConversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")


def typ_val(v: KVal, ts: TyEnv) : KVal = v match {
  case KVar(s,ty) => { 
    val rty = ts.getOrElse(s,"UNDEF")
    KVar(s,rty)
  }
  case KNum(i) => KNum(i) 
  case KFNum(i) => KFNum(i) 
  case KCall(s,vrs,ty) => { 
    val rty = ts.getOrElse(s,"UNDEF")
    KCall(s,vrs,rty)
  }
  case Kop(o, v1 , v2 ) => { 
    val v1_typed = typ_val(v1,ts)
    val v2_typed = typ_val(v2,ts)
    Kop(o,v1_typed,v2_typed)
  }
  case KConst(s,ty) => {
    val rty = ts.getOrElse(s,"UNDEF")
    KConst(s,rty)
  }
  case KStringConst(n) => KStringConst(n) // this case shouldnt be activated 
}

def typ_exp(a: KExp, ts: TyEnv) : KExp = a match {
  case KLet(x, v, e) => {
    KLet(x,typ_val(v,ts),typ_exp(e,ts))
  }
  case KIf(x, e1, e2) => {
    KIf(x, typ_exp(e1,ts), typ_exp(e2,ts))
  }
  case KReturn(v,ty) => KReturn(typ_val(v,ts),ty)
}

import $file.fun_tokens, fun_tokens._
import $file.fun_parser, fun_parser._ 


// for generating new labels
var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String, ty: String = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class Kop(o: String, v1: KVal, v2: KVal) extends KVal
case class KCall(o: String, vrs: List[KVal],ty: String = "UNDEF") extends KVal
case class KFNum(i: Double) extends KVal
case class KStringConst(s: String) extends KVal
case class KConst(s: String,ty: String = "UNDEF") extends KVal

case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def pad(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${pad(e1)}\nELSE\n${pad(e2)}"
}
case class KReturn(v: KVal, rt: String = "UNDEF") extends KExp

// some functions for drawing KVal-trees 
// inspired by William Bradford Larcombe

def draw_vals(vs: List[KVal], prefix: String) : String = {
  val vsi = vs.iterator
  vsi.map(v => draw_val(v, prefix, vsi.hasNext)).mkString 
}

def draw_val(k: KVal, prefix: String, more: Boolean) : String = {
  val full_prefix = s"$prefix${if more then "├" else "└"}"
  val childPrefix = s"$prefix${if more then "│" else ""}  "
  s"\n${full_prefix}" ++ 
  (k match {
    case KVar(x,ty) => x
    case KNum(n) => n.toString
    case KFNum(n) => n.toString
    case KStringConst(n) => n
    case Kop(op, v1 , v2) => s"KOp($op) ${draw_vals(List(v1, v2), childPrefix)}" 
    case KCall(nme, as,ty) => s"KCall($nme) ${draw_vals(as, childPrefix)}" 
  })
}

def draw(k: KVal) = "│" ++ draw_val(k, "", false)

// val k1 = KVar("foo")
// val k2 = KNum(1)
// val k3 = Kop("-", Kop("+", k1, k2), KNum(2))
// println(draw(k3).mkString)
// println(draw(KCall("bar", List(k1,k2,k3,k2,k1))).mkString)


// CPS translation from Exps to KExps using a
// continuation k.
def CPS(e: Exp)(k: KVal => KExp) : KExp = e match {
  case Var(s) => {
    if (s.head.isUpper) {
      val z = Fresh("tmp")
      KLet(z, KConst(s), k(KVar(z)) )
    }
    else k(KVar(s)) 
  }
  case Num(i) => k(KNum(i))
  case FNum(i) => k(KFNum(i))
  case ChConst(i) => k(KNum(i))
  case StringConst(i) => k(KStringConst(i))
  case Aop(o, e1, e2) => {
    val z = Fresh("tmp")
    CPS(e1)(y1 => 
      CPS(e2)(y2 => KLet(z, Kop(o, y1, y2), k(KVar(z)))))
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val z = Fresh("tmp")
    CPS(b1)(y1 => 
      CPS(b2)(y2 => 
        KLet(z, Kop(o, y1, y2), KIf(z, CPS(e1)(k), CPS(e2)(k)))))
  }
  case Call(name, args) => {
    def aux(args: List[Exp], vs: List[KVal]) : KExp = args match {
      case Nil => {
          val z = Fresh("tmp")
          KLet(z, KCall(name, vs), k(KVar(z)))
      }
      case e::es => CPS(e)(y => aux(es, vs ::: List(y)))
    }
    aux(args, Nil)
  }
  case Sequence(e1, e2) => 
    CPS(e1)(_ => CPS(e2)(y2 => k(y2)))
}   

//initial continuation
def CPSi(e: Exp,ty: String) = CPS(e)(KReturn(_,ty))

def CPSi_no_ret(e: Exp,ty: String) = CPS(e)



// convenient string interpolations 
// for instructions, labels and methods
import scala.language.implicitConversions
import scala.language.reflectiveCalls

extension (sc: StringContext) {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
    def m(args: Any*): String = sc.s(args:_*) ++ "\n"
}

// mathematical and boolean operations
def compile_op(op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "/" => "sdiv i32 "
  case "%" => "srem i32 "
  case "==" => "icmp eq i32 "
  case "<=" => "icmp sle i32 "     // signed less or equal
  case "<"  => "icmp slt i32 " 
  case "!=" => "icmp ne i32 "    // signed less than
}

def compile_dop (op: String) = op match {
case "+" => "fadd double "
case "*" => "fmul double "
case "-" => "fsub double "
case "==" => "fcmp oeq double "
case "!=" => "fcmp one double "
case "<=" => "fcmp ole double "
case "<" => "fcmp olt double "
}


def get_type (v: KVal, ty: TyEnv) : String = v match {  // this function is mainly used for OP i think
  case KNum(i) => "Int"
  case KFNum(i) => "Double"
  case KVar(i,typ) => ty.getOrElse(i, "")
  case Kop(op,x1,x2) => get_type(x1,ty)
  case KCall(x1,args,typ) => ty.getOrElse(x1, "")
  case KConst(s,typ) => ty.getOrElse(s, "")
  case KStringConst(s) => "STRING"
}

// compile K values
def compile_val(v: KVal,ty: TyEnv) : String = typ_val(v,ty) match {
  case KNum(i) => s"$i"
  case KFNum(i) => s"$i"
  case KVar(s,typ) => s"%$s"
  case KConst(s,typ) => s"load ${typeConversion.getOrElse(typ, "UNDEF")},${typeConversion.getOrElse(typ,"UNDEF")}* @$s" 
  case Kop(op, x1, x2) => 
    { 
      val typs = get_type(x1,ty)
      if (typs == "Double") { 
        s"${compile_dop(op)} ${compile_val(x1,ty)}, ${compile_val(x2,ty)}"
      }
      else {
        s"${compile_op(op)} ${compile_val(x1,ty)}, ${compile_val(x2,ty)}"
      }
    }

  case KCall("print_string", args, typ)  => args.head match {
    case KStringConst(x) => {
      val list_chars = x.toList
      val print_to_chars = list_chars.map{x => s"call void @print_char(i32 ${x.toInt})"}.mkString("\n")
      s"$print_to_chars"
    }
    case _ =>  s""
  }
  case KCall(x1, Nil,typ) => s"call ${typeConversion.getOrElse(typ,"UNDEF")} @$x1()"
  case KCall(x1, args,typ) => 
  { 
    val args_vals = args.map{x => compile_val(x,ty)}
    val args_typ = args.map{x => typeConversion.getOrElse(get_type(x,ty),"UNDEF")}
    s"call ${typeConversion.getOrElse(typ,"UNDEF")} @$x1(${args_typ.zip(args_vals).map{case (x, y) => s"$x $y"}.mkString(", ")})"
  }
  
}

// compile K expressions
def compile_exp(a: KExp, ty : TyEnv) : String = typ_exp(a,ty) match {
  case KReturn(v,typ) => 
  {
    val val_typ  = typeConversion.getOrElse(typ, "UNDEF")
    if (val_typ == "void") { 
      i"ret void"
    }
    else {
      i"ret $val_typ ${compile_val(v,ty)}"
    }
  }
  case KLet(x: String, KCall(x1, args, "Void"), e: KExp) => 
  {
    i"${compile_val(KCall(x1, args, "Void"), ty)}" ++ compile_exp(e,ty + (x -> "Void"))
  }
  case KLet(x: String, v: KVal, e: KExp) => 
    i"%$x = ${compile_val(v,ty)}" ++ compile_exp(e,ty + (x -> get_type(v,ty)))
  case KIf(x, e1, e2) => {
    val if_br = Fresh("if_branch")
    val else_br = Fresh("else_branch")
    i"br i1 %$x, label %$if_br, label %$else_br" ++
    l"\n$if_br" ++
    compile_exp(e1,ty) ++
    l"\n$else_br" ++ 
    compile_exp(e2,ty)
  }
}

// val ets: TyEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
//                                 "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void","funct" -> "Int") 

// val v = compile_exp(KLet("test", KCall("funct", List(KNum(2),KFNum(6)), "UNDEF"), KReturn(KNum(3))),ets)

// println(v)

// compile function for declarations and main
def compile_decl(d: Decl,ty: TyEnv) : (String,TyEnv) = d match {
  case Def(name, args, rettype, body) => { 
    val name_env = ty + (name -> rettype)
    (m"define ${typeConversion(rettype)} @$name (${args.map{(x,y) => m"${typeConversion.getOrElse(y, "UNDEF")} %$x"}.mkString(",")}) {" ++
    compile_exp(CPSi(body,rettype),name_env ++ args.toMap) ++
    m"}\n", name_env)
  }

  case Const(name, value) => {
   ( m"@$name = global i32 $value", ty + (name -> "Int"))
  }
  case FConst(name, value) => {
    (m"@$name = global double $value", ty + (name -> "Double"))
  }
  case Main(body) => {
    (m"define i32 @main() {" ++
    compile_exp(CPS(body)(_ => KReturn(KNum(0),"Int")),ty) ++
    m"}\n", ty + ("main" -> "Int"))
  }
}

// val rs = Def("sqr",List(("x","Double")),"Double",Aop("*",Var("x"),Var("x")))

// println(compile_decl(rs,initialEnv))


// // main compiler functions
def compile(prog: List[Decl],ty : TyEnv) : String = prog match { 
  case Nil => ""
  case c :: cs => {
    val (llvmc, ty_new) = compile_decl(c,ty)
    llvmc ++ compile(cs, ty_new)
  }
}


// prelude
val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_int = private constant [3 x i8] c"%d\00"
@.str_c = private constant [3 x i8] c"%c\00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_int, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @print_char(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_c, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x)
  ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILT-IN FUNCTIONS (prelude)

"""


def fun_compile(prog: List[Decl]) : String = prelude ++ compile(prog,initialEnv) 

// val fname = "hanoi.fun"
// val tks = tokenise(os.read(os.pwd / fname))
// val ast = Prog.parse_single(tks)
// println(fun_compile(ast))



def write(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    val tks = tokenise(os.read(path))
    val ast = Prog.parse_single(tks)
    val code = fun_compile(ast)
    os.write.over(os.pwd / (file ++ ".ll"), code)
}



def run(fname: String) = {
    val path = os.pwd / fname
    val file = fname.stripSuffix("." ++ path.ext)
    write(fname)  
    os.proc("clang", file ++ ".ll").call()
    os.proc("./a.exe").call()
}

// s
// //some testcases:  
// // (1 + 2) * 3
// println(CPSi(Aop("*", Aop("+", Num(1), Num(2)), Num(3))).toString)

// // 3 * (1 + 2)
// println(CPSi(Aop("*", Num(3), Aop("+", Num(1), Num(2)))).toString)

// //some testcases:

// // numbers and vars   
// println(CPSi(Num(1)).toString)
// println(CPSi(Var("z")).toString)

// //  a * 3
// val e1 = Aop("*", Var("a"), Num(3))
// println(CPSi(e1).toString)

// // (a * 3) + 4
// val e2 = Aop("+", Aop("*", Var("a"), Num(3)), Num(4))
// println(CPSi(e2).toString)

// // 2 + (a * 3)
// val e3 = Aop("+", Num(2), Aop("*", Var("a"), Num(3)))
// println(CPSi(e3).toString)

// //(1 - 2) + (a * 3)
// val e4 = Aop("+", Aop("-", Num(1), Num(2)), Aop("*", Var("a"), Num(3)))
// println(CPSi(e4).toString)

// // 3 + 4 ; 1 * 7
// val es = Sequence(Aop("+", Num(3), Num(4)),
//                   Aop("*", Num(1), Num(7)))
// println(CPSi(es).toString)

// // if (1 == 1) then 3 else 4
// val e5 = If(Bop("==", Num(1), Num(1)), Num(3), Num(4))
// println(CPSi(e5).toString)

// // if (1 == 1) then 3 + 7 else 4 * 2
// val ei = If(Bop("==", Num(1), Num(1)), 
//                 Aop("+", Num(3), Num(7)),
//                 Aop("*", Num(4), Num(2)))
// println(CPSi(ei).toString)


// // if (10 != 10) then e5 else 40
// val e6 = If(Bop("!=", Num(10), Num(10)), e5, Num(40))
// println(CPSi(e6).toString)


// // foo(3)
// val e7 = Call("foo", List(Num(3)))
// println(CPSi(e7).toString)

// // foo(3 * 1, 4, 5 + 6)
// val e8 = Call("foo", List(Aop("*", Num(3), Num(1)), 
//                           Num(4), 
//                           Aop("+", Num(5), Num(6))))
// println(CPSi(e8).toString)

// // a * 3 ; b + 6
// val e9 = Sequence(Aop("*", Var("a"), Num(3)), 
//                   Aop("+", Var("b"), Num(6)))
// println(CPSi(e9).toString)


// val e10 = Aop("*", Aop("+", Num(1), Call("foo", List(Var("a"), Num(3)))), Num(4))
// println(CPSi(e10).toString)






// // main compilation function

// def fun_compile(prog: List[Decl]) : String = ???
