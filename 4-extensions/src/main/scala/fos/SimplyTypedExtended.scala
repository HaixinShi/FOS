package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


  /** t ::=          "true"
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
   *               | "inl" t "as" T
   *               | "inr" t "as" T
   *               | "case" t "of" "inl" ident "=>" t "|" "inr" ident "=>" t
   *               | "fix" t
   *               | "letrec" ident ":" T "=" t "in" t
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
    | ("\\" ~ ident ~ ":" ~ funcTypeTerm ~ "." ~ term ^^
      {case "\\" ~ v ~ ":" ~ tp ~ "." ~ t => Abs(v, tp, t)})
    | "(" ~ term ~ ")" ^^ {case "(" ~ t ~ ")" => t}
    | ("let" ~ ident ~ ":" ~ funcTypeTerm ~ "=" ~ term ~ "in" ~ term ^^
      {case "let" ~ v ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(v, tp, t2), t1)})
    | ("{" ~ term ~ "," ~ term ~ "}" ^^
      {case "{" ~ t1 ~ "," ~ t2 ~ "}" => TermPair(t1, t2)})
    | "fst" ~ term ^^ {case "fst" ~ t => First(t)}
    | "snd" ~ term ^^ {case "snd" ~ t => Second(t)}
    | numericLit ^^ {case str => number2Str(str.toInt)}
    | "inl" ~ term ~ "as" ~ funcTypeTerm ^^ {case _ ~ t ~ _ ~ tp => Inl(t,tp)}
    | "inr" ~ term ~ "as" ~ funcTypeTerm ^^ {case _ ~ t ~ _ ~ tp => Inr(t,tp)}
    | ("case" ~ term ~ "of" ~ "inl" ~ ident ~ "=>" ~ term ~ "|" ~ "inr" ~ ident ~ "=>" ~ term ^^ 
      {case _ ~ t ~ _ ~ _ ~ str1 ~ "=>" ~ t1 ~ _ ~ _ ~ str2 ~ _ ~ t2 => Case(t, str1, t1, str2, t2)})
    | "fix" ~ term ^^ {case _ ~ t => Fix(t)}
    | ("letrec" ~ ident ~ ":" ~ funcTypeTerm ~ "=" ~ term ~ "in" ~ term ^^ 
      {case _ ~ str ~ _ ~ tp ~ _ ~ t1 ~ _ ~ t2 => App(Abs(str, tp, t2), Fix(Abs(str, tp, t1)))})
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

  def pairTypeTerm: Parser[Type] = repsep(simpleTypeTerm, "*") ^^ {case tpList => tpList.reduceRight(TypePair(_,_))}

  def funcTypeTerm: Parser[Type] = repsep(pairTypeTerm, "->") ^^ {case tyList => tyList.reduceRight(TypeFun(_,_))}

  def simpleTypeTerm: Parser[Type] = (
  "Bool" ^^ {case "Bool" => TypeBool}
  | "Nat" ^^ {case "Nat" => TypeNat}
  | ("(" ~ funcTypeTerm ~ ")" ^^ {case "(" ~ tp ~ ")" => tp}))



  /** Call by value reducer. */
  def reduce(t: Term): Term =
    ???

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
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
          println("parsed: " + trees)
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
