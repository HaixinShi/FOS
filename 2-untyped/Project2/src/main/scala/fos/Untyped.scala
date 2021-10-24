package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */
  def termPrime: Parser[Term] = (
    ident ^^ {case str => Var(str)}
    | "\\" ~ ident ~ "." ~ term ^^ {case "\\" ~ ident ~ "." ~ term => Abs(ident, term)}
    | "(" ~ term ~ ")" ^^ {case "(" ~ term ~ ")" => term}
  )

  def term: Parser[Term] = (
    termPrime ~ rep(termPrime) ^^ reduceList
  )

  val reduceList: Term ~ List[Term] => Term = {
    case t ~ tList => tList.foldLeft(t)(App(_,_))
  }
    

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
  def alpha(t: Abs): Abs = t match{
    case Abs(str, term) => Abs(str+'0', alphahelper(term, str))
  }
    
  def alphahelper(t: Term, str: String): Term = t match{
    case Var(s) => if s == str then Var(str+'0') else Var(s)
    case Abs(s, t) => if s == str then Abs(str+'0', alphahelper(t,str)) else Abs(s, alphahelper(t,str))
    case App(t1, t2) => App(alphahelper(t1, str), alphahelper(t2, str))
  }

  def calculateFv(t: Term): Set[Var] = t match{
    case Var(str) => Set(Var(str))
    case Abs(str, term) => calculateFv(term).-(Var(str))
    case App(t1, t2) => calculateFv(t1).++(calculateFv(t2))
  }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */
  def subst(t: Term, x: String, s: Term): Term = t match{//[x -> t] s
    case Var(str) => if str == x then s else Var(str)
    case Abs(str, term) => str == x match{
      case true => Abs(str, term)
      case false => calculateFv(s).contains(Var(str)) match{
        case true => alpha(Abs(str, term)) match{
          case Abs(str, term) => Abs(str, subst(term, x, s))
        }
        case false => Abs(str, subst(term, x, s))
      }
    }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))
  }
    

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match{
    case Abs(str, t) => Abs(str, reduceNormalOrder(t))
    //case App(Abs(str, t), t1) => subst(t, str, t1)// case 1:[str -> t] t1
    case App(t1,t2) => t1 match{//left most
      //case Abs(str, t) => App(reduceNormalOrder(t1),t2)//case 2 = case 1, so it is not necessary
      case Abs(str, t) => subst(t, str, t2)
      case App(t3, t4) =>
        try{App(reduceNormalOrder(t1),t2)}
        catch {
          case NoReductionPossible(_) =>
            App(t1, reduceNormalOrder(t2))
        }
      case Var(str) => App(t1, reduceNormalOrder(t2))// App(v1, v2)
    }
    case _ => throw new NoReductionPossible(t)
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = t match{
    case App(Abs(str1, t1), Abs(str2,t2)) => subst(t1, str1, Abs(str2,t2))
    case App(App(t1,t2),term) => App(reduceCallByValue(App(t1,t2)),term)
    case App(Abs(str,term),App(t1,t2)) => App(Abs(str,term),reduceCallByValue(App(t1,t2)))
    case _ => throw new NoReductionPossible(t)
  }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): LazyList[Term] =
    try {
      var t1 = reduce(t)
      LazyList.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        LazyList.cons(t, LazyList.empty)
    }
  //test cases:
  //(\x.x)((\x.x)(\z.(\x.x)z))
  //(\x.(\y.x))y
  //\y. ((\x. x) y)
  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
         println("normal order: ")
         for (t <- path(trees, reduceNormalOrder))
           println(t)
         println("call-by-value: ")
         for (t <- path(trees, reduceCallByValue))
           println(t)

      case e =>
        println(e)
    }
  }
}
