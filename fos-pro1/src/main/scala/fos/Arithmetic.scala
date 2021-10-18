package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  def number2Str(i: Int):Term = {
      var tmp:Term = Zero;
      for(i <- 1 to i)
        tmp = Succ(tmp)
      return tmp
  }

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | numericLit
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] = (
        "true" ^^^ True
      | "false" ^^^ False
      | "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^ {case "if" ~t1 ~ "then" ~ t2 ~ "else" ~ t3 => If(t1,t2,t3)}
      | numericLit ^^ { case str => number2Str(str.toInt) }
      | "succ" ~ term ^^ {case "succ" ~ t => Succ(t)}
      | "pred" ~ term ^^ {case "pred" ~ t => Pred(t)}
      | "iszero" ~ term ^^ {case "iszero" ~ t => IsZero(t)} 
      )
     // note: you should use `numericLit` to parse numeric literals
      

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  def isANumber(t:Term):Boolean = t match{
      case Zero => true
      case Succ(t) => isANumber(t)
      case Pred(t) => isANumber(t)
      case _ => false
  }

  def isNANTerminal(t:Term):Boolean = t match{
    case False => true
    case True => true
    case _ => false
  }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match{
      case If(True,t1,t2) => t1
      case If(False,t1,t2) => t2
      case IsZero(Zero) => True
      case Pred(Zero) => Zero
      case If(t,t1,t2) => If(reduce(t),t1,t2)
      case Pred(Succ(t)) => reduce(t)
      case IsZero(Succ(t)) => False
      case IsZero(t) => IsZero(reduce(t))
      case Pred(t) => Pred(reduce(t))
      case Succ(t) => if isNANTerminal(t) then throw new NoReductionPossible(t) else Succ(reduce(t))
      case Zero => Zero
      case _ => throw new NoReductionPossible(t)
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = t match{
      case If(t1, t2, t3) => if eval(t1) eq True then eval(t2) else eval(t3)
      case True => True
      case False => False
      case Zero => Zero
      case Succ(t) => if isANumber(eval(t)) then Succ(eval(t)) else throw new TermIsStuck(t)
      case Pred(t) => if isANumber(eval(t))&& (eval(t) ne Zero) then eval(t) else  throw new TermIsStuck(t)
      case Pred(t) => if eval(t) eq Zero then Zero else  throw new TermIsStuck(t)
      case IsZero(t) => if eval(t) eq Zero then True else throw new TermIsStuck(t)
      case IsZero(t) => if isANumber(eval(t))&& (eval(t) ne Zero) then False else throw new TermIsStuck(t)
      case _ => throw new TermIsStuck(t)
  }
    

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
