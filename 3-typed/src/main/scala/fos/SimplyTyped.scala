package fos

import fos.SimplyTyped.numericLit

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
//    | term ~ term ^^ {case t1 ~ t2 => App(t1, t2)}
    | "(" ~ term ~ ")" ^^ {case "(" ~ t ~ ")" => t}
    | ("let" ~ ident ~ ":" ~ typeTerm ~ "=" ~ term ~ "in" ~ term ^^
      {case "let" ~ v ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(v, tp, t2), t1)})
    | ("{" ~ term ~ "," ~ term ~ "}" ^^
      {case "{" ~ t1 ~ "," ~ t2 ~ "}" => TermPair(t1, t2)})
    | "fst" ~ term ^^ {case "fst" ~ t => First(t)}
    | "snd" ~ term ^^ {case "snd" ~ t => Second(t)}
    | numericLit ^^ {
      case "0"=>Zero
      case "1"=>Succ(Zero)
      case "2"=>Succ(Succ(Zero))
      case "3"=>Succ(Succ(Succ(Zero)))
      case "4"=>Succ(Succ(Succ(Succ(Zero))))
      case "5"=>Succ(Succ(Succ(Succ(Succ(Zero)))))
      case "6"=>Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))
      case "7"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))
      case "8"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))))
      case "9"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))))
    }
    )

  def term: Parser[Term] = (
    termPrime ~ rep(termPrime) ^^ reduceList
    )

  val reduceList: Term ~ List[Term] => Term = {
    case t ~ tList => tList.foldLeft(t)(App(_,_))
  }
  /////////////////////////////////////////////////////////////////////////////

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

  def calculateFv(t: Term): Set[Var] = t match{
    case Var(str) => Set(Var(str))
    case Abs(str, tp, term) => calculateFv(term).-(Var(str))
    case App(t1, t2) => calculateFv(t1).++(calculateFv(t2))
  }

  /** Substitution method [x -> s]t
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = t match{//[x -> t] s
    case Var(str) => if str == x then s else Var(str)
    case Abs(str, tp, term) => str == x match{
      case true => Abs(str, tp, term)
      case false => calculateFv(s).contains(Var(str)) match{
        case true => alpha(Abs(str, tp, term)) match{
          case Abs(str, tp, term) => Abs(str, tp, subst(term, x, s))
        }
        case false => Abs(str, tp, subst(term, x, s))
      }
    }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
  }
  /////////////////////////////////////////////////////////////////////////////

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
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
    case _ => throw new NoRuleApplies(t)
  }


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???


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
//          println("typed: " + typeof(Nil, trees))
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
