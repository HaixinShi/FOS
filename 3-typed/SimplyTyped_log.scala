package fos

import fos.SimplyTyped.{numericLit, typeof}

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.*

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Defintion of terms
   * /////////////////////////////////////////////////////////////////////////
   t ::=          "true"
   *               | "false"
   *               | number
   *               | "succ" t
   *               | "pred" t
   *               | "iszero" t
   *               | "if" t "then" t "else" t
   *               | ident
   *               | "\" ident ":" T "." t
   *               | t t
   *               | "(" t ")"
   *               | "let" ident ":" T "=" t "in" t
   *               | "{" t "," t "}"
   *               | "fst" t
   *               | "snd" t
   * /////////////////////////////////////////////////////////////////////////
   */
  def termPrime: Parser[Term] = (
    "true" ^^ {case "true" => True}
    | "false" ^^ {case "false" => False}
    | "succ" ~ term ^^ {case "succ" ~ t => Succ(t)}
    | "pred" ~ term ^^ {case "pred" ~ t => Pred(t)}
    | "iszero" ~ term ^^ {case "iszero" ~ t => IsZero(t)}
    | ("if" ~ term ~ "then" ~ term ~ "else" ~ term ^^
      {case "if" ~ cond ~ "then" ~ t1 ~ "else" ~ t2 => If(cond, t1, t2)})
    | ident ^^ {case str => Var(str)}
    | ("\\" ~ ident ~ ":" ~ typeTerm ~ "." ~ term ^^
      {case "\\" ~ v ~ ":" ~ tp ~ "." ~ t => Abs(v, tp, t)})
    | "(" ~ term ~ ")" ^^ {case "(" ~ t ~ ")" => t}
    | ("let" ~ ident ~ ":" ~ typeTerm ~ "=" ~ term ~ "in" ~ term ^^
      {case "let" ~ v ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(v, tp, t2), t1)})
    | ("{" ~ term ~ "," ~ term ~ "}" ^^
      {case "{" ~ t1 ~ "," ~ t2 ~ "}" => TermPair(t1, t2)})
    | "fst" ~ term ^^ {case "fst" ~ t => First(t)}
    | "snd" ~ term ^^ {case "snd" ~ t => Second(t)}
    | numericLit ^^ {case str => number2Str(str.toInt)}
    )

  def number2Str(i: Int):Term = {
    var tmp:Term = Zero;
    for(i <- 1 to i)
      tmp = Succ(tmp)
    return tmp
  }

  def term: Parser[Term] = (
    termPrime ~ rep(termPrime) ^^ reduceList
    )

  val reduceList: Term ~ List[Term] => Term = {
    case t ~ tList => tList.foldLeft(t)(App(_,_))
  }

  /*
  def singleTerm: Parser[Term] =(
    "true"^^^True
      | "false"^^^False
      | ("if"~term~"then"~term~"else"~term)^^{case _~cond~_~t1~_~t2 => If(cond, t1, t2)}
      | numericLit^^(x => parseNumericLiteral(x.toInt))
      | ("succ"~term)^^{case _~term => Succ(term)}
      | ("pred"~term)^^{case _~term => Pred(term)}
      | ("iszero"~term)^^{case _~term => IsZero(term)}
      | ident ^^{case x => Var(x)}
      | "\\" ~ ident ~ ":" ~ parser_type ~ "." ~ term ^^ {case _ ~ x ~ _~ tp ~ _~ term => Abs(x, tp, term)}
      | "(" ~ term ~ ")" ^^ {case _~t~_ => t}
      | "let" ~ ident ~ ":" ~ parser_type ~ "=" ~ term ~ "in" ~ term ^^ {case _ ~ x ~ _ ~ tp ~ _ ~ t1 ~ _ ~ t2 => App(Abs(x,tp,t2),t1)}
      | "{" ~ term ~ "," ~ term ~ "}" ^^ {case _ ~ t1 ~ _ ~ t2 ~ _ => TermPair(t1, t2)}
      | "fst" ~ term ^^ {case _ ~ t => First(t)}
      | "snd" ~ term ^^ {case _ ~ t => Second(t)}

    )


  def term: Parser[Term] = {
    singleTerm~rep(singleTerm)^^{case firstTerm~otherTerms =>
      otherTerms.foldLeft(firstTerm){(z,i)=> App(z,i)}
    }
  }
  def parseNumericLiteral(x: Int): Term = x match {
    case 0 => Zero
    case _ => Succ(parseNumericLiteral(x-1))
  }


  def parser_type:Parser[Type] =
    rep1sep(pair_parser_type, "->")^^{case functions =>
      functions.reduceRight((function1, function2) => TypeFun(function1, function2))
    }
  def single_parser_type: Parser[Type] = (
    "Bool" ^^^ TypeBool
      | "Nat" ^^^ TypeNat
      | "(" ~ parser_type ~ ")" ^^ {case _ ~ t1 ~ _  => t1}
    )
  def pair_parser_type: Parser[Type] = rep1sep(single_parser_type, "*") ^^ {case pairs =>
    pairs.reduceRight((type1,type2) => TypePair(type1,type2))
  }*/
  /** Definition of types
   * /////////////////////////////////////////////////////////////////////////
   T ::=        "Bool"                      boolean type
   *               | "Nat"                     numeric type
   *               | T "->" T                  function types  (right associative)
   *               | "(" T ")"
   *               | T "*" T                   pair types (right associative)
   */
  def typeTerm: Parser[Type] = (
    simpleTypeTerm ~ "->" ~ simpleTypeTerm ^^ {case t1 ~ "->" ~ t2 => TypeFun(t1, t2)}
    | simpleTypeTerm ~ "*" ~ simpleTypeTerm ^^ {case t1 ~ "*" ~ t2 => TypePair(t1, t2)}
    | simpleTypeTerm ^^ {case tp => tp}
    )

  def simpleTypeTerm: Parser[Type] = (
      "Bool" ^^ {case "Bool" => TypeBool}
      | "Nat" ^^ {case "Nat" => TypeNat}
      | ("(" ~ typeTerm ~ ")" ^^ {case "(" ~ tp ~ ")" => tp})
    )
  /////////////////////////////////////////////////////////////////////////////

  /**     Definition of values
  v ::= "true"
    | "false"
    | nv                          numeric value
    | "\" x ":" T "." t           abstraction value
    | "{" v "," v "}"             pair values
  */
  def values: Parser[Term] = (
    simpleVals ^^ {case v => v}
  )

  def simpleVals: Parser[Term] = (
    "true" ^^ {case "true" => True}
    | "false" ^^ {case "false" => False}
    | nv ^^ {case nv => nv}
    | ("\\" ~ ident ~ ":" ~ typeTerm ~ "." ~ term ^^
    {case "\\" ~ v ~ ":" ~ tp ~ "." ~ t => Abs(v, tp, t)})
    | ("{" ~ values ~ "," ~ values ~ "}" ^^
      {case "{" ~ v1 ~ "," ~ v2 ~ "}" => TermPair(v1, v2)})
  )

  /**     Define the numeric values
  nv ::= "0"
    | "succ" nv
  */
  def nvPrime: Parser[Term] = (
    numericLit ^^ {case "0" => Zero}
    | "succ" ~ nv ^^ {case "succ" ~ nv => Succ(nv)}
  )

  def nv: Parser[Term] = (
    nvPrime ~ rep(nvPrime) ^^ reduceNVList
    )

  val reduceNVList: Term ~ List[Term] => Term = {
    case t ~ tList => tList.foldLeft(t)(App(_,_))
  }
  /////////////////////////////////////////////////////////////////////////////

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /////////////////////////////////////////////////////////////////////////////
  /** Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Abs): Abs = t match{
    case Abs(str, tp, term) => Abs(str+'0', tp, alphahelper(term, tp, str))
  }

  def alphahelper(t: Term, tp: Type, str: String): Term = t match{
    case Var(s) => if s == str then Var(str+'0') else Var(s)
    case Abs(s, tp, t) => if s == str then Abs(str+'0', tp, alphahelper(t, tp, str)) else Abs(s, tp, alphahelper(t, tp, str))
    case App(t1, t2) => App(alphahelper(t1, tp, str), alphahelper(t2, tp, str))
  }

  def calculateFv(t: Term): Set[Var] = {
    println("calculateFv")
    println(t)
    t match{
    case Var(str) => Set(Var(str))
    case Abs(str, tp, term) => {println("Abs(str, tp, term)")
      calculateFv(term).-(Var(str))}
    case App(t1, t2) => {println("App(t1, t2)")
      calculateFv(t1).++(calculateFv(t2))
    }
    case IsZero(t) => calculateFv(t)
    case Zero => Set()
  }}

  /** Substitution method [x -> s]t
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = {//[x->s]t
    println("subt")
    println(t)//t = (\y:Nat.x y)
    println(x)//x = x
    println(s)//s = (\x:Nat.iszero x)
    t match {
      case Var(str) => if str == x then s else Var(str)
      case Abs(str, tp, term) =>  {//str = y, term = (\x:Nat.iszero x)
        println(str ==x)
        str ==x match {//y != x
        case true => Abs(str, tp, term)
        case false => calculateFv(s).contains(Var(str)) match {
          case true => alpha(Abs(str, tp, term)) match {
            case Abs(str, tp, term) => Abs(str, tp, subst(term, x, s))
          }
          case false => Abs(str, tp, subst(term, x, s))
        }
      }}
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))

      case Succ(t1) => Succ(subst(t1, x, s))
      case Pred(t1) => Pred(subst(t1, x, s))
      case IsZero(t1) => IsZero(subst(t1, x, s))
      case First(t1) => First(subst(t1, x, s))
      case Second(t1) => Second(subst(t1, x, s))
      case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
      case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
      case _ => t

    }
  }
  /////////////////////////////////////////////////////////////////////////////

  /** Call by value reducer. */
  def reduce(t: Term): Term = {
    println("reduce")
    println(t)
    t match {
    case If(True, t1: Term, t2: Term) => t1
    case If(False, t1: Term, t2: Term) => t2
    case If(cond: Term, t1: Term, t2: Term) => If(reduce(cond), t1, t2)
    case IsZero(Zero) => True
    /*
    case IsZero(Succ(t: Term)) => {
      var tmp: Term = t
      while(tmp.isInstanceOf[Succ]){
        tmp = tmp.asInstanceOf[Succ].t
      }
      if(tmp == Zero){
        False
      }else{
        IsZero(reduce(Succ(t)))
      }
    }*/
    /*
    case IsZero(t: Term) => {
      print(t)
      IsZero(reduce(t))}
    case Pred(Zero) => Zero
    case Pred(Succ(Zero)) => Zero
    case Pred(Succ(t: Term)) => {
      var tmp: Term = t
      while(tmp.isInstanceOf[Succ]){
        tmp = tmp.asInstanceOf[Succ].t
      }
      if(tmp == Zero){
        t
      }else{
        Pred(reduce(Succ(t)))
      }
    }*/
    case Pred(t: Term) => Pred(reduce(t))
    case Succ(t: Term) => Succ(reduce(t))
  /*
    case First(TermPair(tp1, tp2)) if isV(tp1) && isV(tp2) => tp1
    case Second(TermPair(tp1, tp2)) if isV(tp1) && isV(tp2) => tp2
    case First(t) => First(reduce(t))
    case Second(t) => Second(reduce(t))
    case TermPair(t1,t2) if !isV(t1) => TermPair(reduce(t1),t2)
    case TermPair(t1,t2) if !isV(t2) => TermPair(t1,reduce(t2))
    case _ => throw new NoRuleApplies(t)
    */


    case App(Abs(v1, tp1, t1), Abs(v2, tp2, t2)) => {
      println("1")
      subst(t1, v1, Abs(v2, tp2, t2))
    }
    case App(App(t1,t2),term) => {
      println("2")
      App(reduce(App(t1,t2)),term)}
    case App(Abs(v1, tp1, t1),App(t2,t3)) => {
      println("3")
      App(Abs(v1, tp1, t1),reduce(App(t2,t3)))}
    case App(Abs(v1, tp1, t1),term) =>{
      println("4")
      subst(t1, v1, term)
    }
    case App(App(Abs(x,type_,y),z), t2)=>{
      println("I am in")
      throw new NoRuleApplies(t)
    }
    case App(t1, t2)=>{
      println("I am in")
      println(t1)
      println(t1.getClass.getSimpleName)
      t1 match {
        case Abs(x_, t_, y_) => {
          println(x_)
          println(t_)
          println(y_)
        }
      }
      println(t2)
      println(t2.getClass.getSimpleName)
      throw new NoRuleApplies(t)
    }
    case default => {
      println("reduce default")
      throw new NoRuleApplies(t)
    }}
    /*
    case Var(s) => Var(s)
    case values => values         // already as a value; cannot reduce anymore
    case If(cond, t1, t2) => cond match {
      case True => reduce(t1)
      case False => reduce(t2)
//      case numericLit => throw new NoRuleApplies(t)
      case _ => reduce(If(reduce(cond),t1,t2))
    }
    case IsZero(expr) => expr match {
      case Zero => True
      case Succ (expr) => False
      case _ => reduce(IsZero(reduce(expr)))
    }
    case Pred(expr) => expr match {
      case Zero => Zero
      case Succ(expr) => reduce(expr)
      case _ => reduce(Pred(reduce(expr)))
    }
    case Succ(expr) => expr match {
//      case False=>throw TermIsStuck(t)        // should be checked by the typing rules now
//      case True=>throw TermIsStuck(t)
      case _ => Succ(reduce(expr))
    }
    case App(t1, t2) => t1 match {
      case Abs(v, tp, t) => t2 match {
        case values => reduce(subst(t, v, t2))
        case Var(s) => reduce(subst(t, v, t2))
        case _ => reduce(App(t1, reduce(t2)))
      }
      case values => t2 match{                  // should continue to reduce or is stuck?
        case values => App(t1, t2)
      }
      case _ => reduce(App(reduce(t1), t2))
    }
    case App(Abs(v, tp, t2), t1) => t1 match {
      case values => reduce(subst(t2, v, t1))
      case _ => reduce(App(Abs(v, tp, t2), reduce(t1)))
    }
    case _ => throw new NoRuleApplies(t)*/
  }


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True => TypeBool
    case False => TypeBool
    case Zero => TypeNat
    case Pred(t0) => typeof(ctx, t0) match {
      case TypeNat => TypeNat
      case _ => throw new TypeError(t, "Nat type expected but " + typeof(ctx, t0).toString() + " found")
    }
    case Succ(t0) => typeof(ctx, t0) match {
      case TypeNat => TypeNat
      case _ => throw new TypeError(t, "Nat type expected but " + typeof(ctx, t0).toString() + " found")
    }
    case IsZero(t0) => typeof(ctx, t0) match {
      case TypeNat => TypeBool
      case _ => throw new TypeError(t, "Nat type expected but " + typeof(ctx, t0).toString() + " found")
    }
    case If(cond, t1, t2) => typeof(ctx, cond) match {
      case TypeBool => typeof(ctx, t1) == typeof(ctx, t2) match {
        case true => typeof(ctx, t1)
        case false => throw new TypeError(t, "Type of t1 " + typeof(ctx, t1).toString() + " type of t2 " +
          typeof(ctx, t1).toString() + " are different, but should be the same")
      }
      case _ => throw new TypeError(t, "Bool type expected but " + typeof(ctx, t1).toString() + " found")
    }
    case Var(s) => (ctx.map(_._2).lift(ctx.indexWhere(_._1 == s))).getOrElse(TypeBool)
    case Abs(v, tp, t2) => TypeFun(tp, typeof(ctx :+ (v, tp), t2))
    case App(t1, t2) => typeof(ctx, t1) match {
      case TypeFun(tp1, tp2) => typeof(ctx, t2) == tp1 match {
        case true => tp2
        case false => throw new TypeError(t, "parameter type mismatch: expected " + tp1.toString() +
          " but found " +  typeof(ctx, t2).toString())
      }
    }
    case TermPair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
    case First(t0) => typeof(ctx, t0) match {
      case TypePair(tp1, tp2) => tp1
      case _ => throw new TypeError(t, "pair type expected but " + typeof(ctx, t0) + " found")
    }
    case Second(t0) => typeof(ctx, t0) match {
      case TypePair(tp1, tp2) => tp2
      case _ => throw new TypeError(t, "pair type expected but " + typeof(ctx, t0) + " found")
    }
    case _ => throw new TypeError(t, "Type of this term is wrong")
  }



  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): LazyList[Term] =
    try {
      println("path")
      var t1 = reduce(t)
      LazyList.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        LazyList.cons(t, LazyList.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        try {
          println(trees)
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println("for-------------------------")
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
