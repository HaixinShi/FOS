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
   * ////////////////////////////////////////////////////////////////////////
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
   * ////////////////////////////////////////////////////////////////////////
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
    t match{
    case Var(str) => Set(Var(str))
    case Abs(str, tp, term) => {
      calculateFv(term).-(Var(str))}
    case App(t1, t2) => {
      calculateFv(t1).++(calculateFv(t2))
    }
    case IsZero(t1) => calculateFv(t1)
    case Succ(t1) => calculateFv(t1)
    case Pred(t1) => calculateFv(t1)
    case IsZero(t1) => calculateFv(t1)
    case First(t1) => calculateFv(t1)
    case Second(t1) => calculateFv(t1)
    case TermPair(t1, t2) => calculateFv(t1).++(calculateFv(t2))
    case If(cond, t1, t2) =>{
      calculateFv(t1).++(calculateFv(t2))
      calculateFv(t1).++(calculateFv(cond))
    }
    case _ => Set()
  }}

  /** Substitution method [x -> s]t
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = {//[x->s]t
    t match {
      case Var(str) => if str == x then s else Var(str)
      case Abs(str, tp, term) =>  {//str = y, term = (\x:Nat.iszero x)
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
  def IsNumbers(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t0) => IsNumbers(t0)
    case _ => false
  }
  def IsValues(t: Term): Boolean = t match {
    case True => true
    case False => true
    case Abs(v, tp, t0) => true
    case TermPair(t1, t2) => (IsValues(t1) && IsValues(t2))
    case _ => IsNumbers(t)
  }
  def StepToSucc(t: Term) : Term ={
    t match{
      case Succ(t1) => t1
      case _ => t
    }
  }
  /** Call by value reducer. */
  def reduce(t: Term): Term = {
    t match {
    case If(True, t1: Term, t2: Term) => t1
    case If(False, t1: Term, t2: Term) => t2
    case If(cond: Term, t1: Term, t2: Term) => If(reduce(cond), t1, t2)
    case IsZero(Zero) => True
    case IsZero(Succ(t)) => {
      var tmp = t
      while(tmp.isInstanceOf[Succ]){
        tmp = StepToSucc(tmp.asInstanceOf[Succ])
      }
      if(tmp == Zero){
        False
      }else{
        IsZero(reduce(Succ(t)))
      }
    }
    case IsZero(t) => {
      IsZero(reduce(t))}
    case Pred(Zero) => Zero
    case Pred(Succ(Zero)) => Zero
    case Pred(Succ(t)) => {
      var tmp= t
      while(tmp.isInstanceOf[Succ]){
        tmp = StepToSucc(tmp.asInstanceOf[Succ])
      }
      if(tmp == Zero){
        t
      }else{
        Pred(reduce(Succ(t)))
      }
    }
    case Pred(t) => Pred(reduce(t))
    case Succ(t) => Succ(reduce(t))

    case First(TermPair(p1, p2)) => IsValues(p1) && IsValues(p2) match {
      case true => p1
    }
    case Second(TermPair(p1, p2)) => IsValues(p1) && IsValues(p2) match{
      case true => p2
    }
    case First(t) => First(reduce(t))
    case Second(t) => Second(reduce(t))
    case TermPair(p1,p2) => IsValues(p1) match {
      case false => TermPair(reduce(p1),p2)
    }
    case TermPair(p1,p2) => IsValues(p2) match{
      case false => TermPair(p1,reduce(p2))
    }

    case App(Abs(v1, tp1, t1), Abs(v2, tp2, t2)) => {
      subst(t1, v1, Abs(v2, tp2, t2))
    }
    case App(App(t1,t2),term) => {
      App(reduce(App(t1,t2)),term)
    }
    case App(Abs(v1, tp1, t1),t2) => IsValues(t2) match{
      case true => subst(t1, v1, t2)
      case false => App(Abs(v1, tp1, t1),reduce(t2))
    }
    case _ => {
      throw new NoRuleApplies(t)
    }}
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
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
